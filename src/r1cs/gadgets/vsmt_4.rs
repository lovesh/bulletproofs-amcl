use crate::errors::R1CSError;
use crate::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier,
};
use std::time::{Duration, Instant};
use crate::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;
use super::helper_constraints::constrain_lc_with_scalar;
use amcl_wrapper::field_elem::FieldElement;
use amcl_wrapper::group_elem::{GroupElement, GroupElementVector};
use amcl_wrapper::group_elem_g1::{G1, G1Vector};
use amcl_wrapper::constants::{MODBYTES, NLEN};

use rand::{RngCore, CryptoRng};

use super::helper_constraints::poseidon::{
    PoseidonParams, SboxType, PADDING_CONST, Poseidon_hash_4, Poseidon_hash_4_constraints
};
use std::collections::HashMap;

type DBVal = [FieldElement; 4];
type ProofNode = [FieldElement; 3];

/// Depth of the tree.
/// Has to be a multiple of 4.
// TODO: Remove above restriction.
pub const TreeDepth: usize = 8;

/// Number of bytes to represent leaf index
pub const LeafIndexBytes: usize = TreeDepth / 4;

/// Get a base 4 representation of the given `scalar`. Only process `limit_bytes` of the scalar
pub fn get_base_4_repr(scalar: &FieldElement, limit_bytes: usize) -> Vec<u8> {
    if limit_bytes > MODBYTES {
        panic!("limit_bytes cannot be more than {} but found {}", MODBYTES, limit_bytes)
    }
    let d = limit_bytes * 4;    // number of base 4 digits
    let n = limit_bytes * 8;    // number of bits to process
    let mut s = scalar.to_bignum();
    s.norm();
    let mut k = NLEN - 1;

    let mut base_4 = vec![];
    while base_4.len() != d {
        for i in 0..k + 1 {
            let mut c = s.w[i];
            while (c != 0) && (base_4.len() != d) {
                base_4.push((c % 4) as u8);
                c /= 4;
            }
        }
    }
    base_4.reverse();
    base_4
}

// TODO: ABSTRACT HASH FUNCTION BETTER
/// Sparse merkle tree with width 4, .i.e each node has 4 children.
pub struct VanillaSparseMerkleTree_4<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<FieldElement>,
    db: HashMap<Vec<u8>, DBVal>,
    hash_params: &'a PoseidonParams,
    pub root: FieldElement
}

impl<'a> VanillaSparseMerkleTree_4<'a> {
    pub fn new(hash_params: &'a PoseidonParams) -> VanillaSparseMerkleTree_4<'a> {
        if (TreeDepth % 4) != 0 {
            panic!("Tree depth should be a multiple of 4");
        }
        let depth = TreeDepth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<FieldElement> = vec![];
        empty_tree_hashes.push(FieldElement::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i-1];
            let input: [FieldElement; 4] = [prev.clone(); 4];
            // Hash all 4 children at once
            let new = Poseidon_hash_4(input.clone(), hash_params, &SboxType::Quint);
            let key = new.to_bytes();

            db.insert(key, input);
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree_4 {
            depth,
            empty_tree_hashes,
            db,
            hash_params,
            root
        }
    }

    pub fn update(&mut self, idx: FieldElement, val: FieldElement) -> FieldElement {

        // Find path to insert the new key
        let mut sidenodes_wrap = Some(Vec::<ProofNode>::new());
        self.get(idx, &mut sidenodes_wrap);
        let mut sidenodes = sidenodes_wrap.unwrap();

        // Convert leaf index to base 4
        let mut cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        cur_idx.reverse();
        let mut cur_val = val.clone();

        // Iterate over the base 4 digits
        for d in cur_idx {
            let mut side_elem = sidenodes.pop().unwrap().to_vec();
            // Insert the value at the position determined by the base 4 digit
            side_elem.insert(d as usize, cur_val);

            let mut input: DBVal = [FieldElement::zero(); 4];
            input.copy_from_slice(side_elem.as_slice());
            let h = Poseidon_hash_4(input.clone(), self.hash_params, &SboxType::Quint);
            self.update_db_with_key_val(h, input);
            cur_val = h;
        }

        self.root = cur_val;

        cur_val
    }

    /// Get a value from tree, if `proof` is not None, populate `proof` with the merkle proof
    pub fn get(&self, idx: FieldElement, proof: &mut Option<Vec<ProofNode>>) -> FieldElement {
        let cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<ProofNode>::new();

        for d in cur_idx {
            let k = cur_node.to_bytes();
            let children = self.db.get(&k).unwrap();
            cur_node = children[d as usize];
            if need_proof {
                let mut proof_node: ProofNode = [FieldElement::zero(); 3];
                let mut j = 0;
                for (i, c) in children.to_vec().iter().enumerate() {
                    if i != (d as usize) {
                        proof_node[j] = c.clone();
                        j += 1;
                    }
                }
                proof_vec.push(proof_node);
            }
        }

        match proof {
            Some(v) => {
                v.extend_from_slice(&proof_vec);
            }
            None => ()
        }

        cur_node
    }

    /// Verify a merkle proof, if `root` is None, use the current root else use given root
    pub fn verify_proof(&self, idx: FieldElement, val: FieldElement, proof: &[ProofNode], root: Option<&FieldElement>) -> bool {
        let mut cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        cur_idx.reverse();
        let mut cur_val = val.clone();

        for (i, d) in cur_idx.iter().enumerate() {
            let mut p = proof[self.depth-1-i].clone().to_vec();
            p.insert(*d as usize, cur_val);
            let mut input: DBVal = [FieldElement::zero(); 4];
            input.copy_from_slice(p.as_slice());
            let h = Poseidon_hash_4(input.clone(), self.hash_params, &SboxType::Quint);
            cur_val = h;
        }

        // Check if root is equal to cur_val
        match root {
            Some(r) => {
                cur_val == *r
            }
            None => {
                cur_val == self.root
            }
        }
    }

    fn update_db_with_key_val(&mut self, key: FieldElement, val: DBVal) {
        self.db.insert(key.to_bytes(), val);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::get_generators;

    #[test]
    fn test_vanilla_sparse_merkle_tree_4() {
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 6;
        let hash_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);

        let mut tree = VanillaSparseMerkleTree_4::new(&hash_params);

        for i in 1..6 {
            let s = FieldElement::from(i as u64);
            tree.update(s, s);
        }

        for i in 1..6 {
            let s = FieldElement::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<ProofNode>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(s, s, &proof_vec, None));
            assert!(tree.verify_proof(s, s, &proof_vec, Some(&tree.root)));
        }

        let kvs: Vec<(FieldElement, FieldElement)> = (0..10).map(|_| (FieldElement::random(), FieldElement::random())).collect();
        for i in 0..kvs.len() {
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }

    #[test]
    fn test_b4() {
        println!("{:?}", get_base_4_repr(&FieldElement::from(18u64), 32));
    }
}