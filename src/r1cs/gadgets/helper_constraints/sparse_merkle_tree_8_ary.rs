use std::collections::HashMap;

use amcl_wrapper::constants::{MODBYTES, NLEN};

use crate::errors::R1CSError;
use crate::r1cs::linear_combination::AllocatedQuantity;
use crate::r1cs::{ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier};
use amcl_wrapper::field_elem::FieldElement;
use amcl_wrapper::group_elem::GroupElement;
use amcl_wrapper::group_elem_g1::G1;

use super::constrain_lc_with_scalar;
use super::poseidon::{
    PoseidonParams, Poseidon_hash_8, Poseidon_hash_8_constraints, SboxType, PADDING_CONST,
};
use crate::r1cs::gadgets::helper_constraints::poseidon::ZERO_CONST;

const ARITY: usize = 8;

pub type DBVal = [FieldElement; ARITY];
pub type ProofNode = [FieldElement; ARITY-1];

/// Get a base 8 representation of the given `scalar`. Only process `limit_bytes` of the scalar
pub fn get_base_8_repr(scalar: &FieldElement, limit_bytes: usize) -> Vec<u8> {
    if limit_bytes > MODBYTES {
        panic!(
            "limit_bytes cannot be more than {} but found {}",
            MODBYTES, limit_bytes
        )
    }
    let d = limit_bytes * 3; // number of base 8 digits
    let mut s = scalar.to_bignum();
    s.norm();

    let mut base_8 = vec![];
    while (base_8.len() != d) && (!s.iszilch()) {
        base_8.push(s.lastbits(3) as u8);
        s.fshr(3);
    }
    while base_8.len() != d {
        base_8.push(0);
    }

    base_8.reverse();
    base_8
}

// TODO: ABSTRACT HASH FUNCTION BETTER
/// Sparse merkle tree with arity 8, .i.e each node has 4 children.
#[derive(Clone, Debug)]
pub struct VanillaSparseMerkleTree_8<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<FieldElement>,
    pub db: HashMap<Vec<u8>, DBVal>,
    hash_params: &'a PoseidonParams,
    pub root: FieldElement,
}

impl<'a> VanillaSparseMerkleTree_8<'a> {
    pub fn new(hash_params: &'a PoseidonParams, depth: usize) -> VanillaSparseMerkleTree_8<'a> {
        if (depth % ARITY) != 0 {
            panic!("Tree depth should be a multiple of {}", ARITY);
        }
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<FieldElement> = vec![];
        empty_tree_hashes.push(FieldElement::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i - 1];
            let input: [FieldElement; ARITY] = [prev.clone(); ARITY];
            // Hash all 8 children at once
            let new = Poseidon_hash_8(input.clone(), hash_params, &SboxType::Quint);
            let key = new.to_bytes();

            db.insert(key, input);
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree_8 {
            depth,
            empty_tree_hashes,
            db,
            hash_params,
            root,
        }
    }

    pub fn update(&mut self, idx: FieldElement, val: FieldElement) -> FieldElement {
        // Find path to insert the new key
        let mut sidenodes_wrap = Some(Vec::<ProofNode>::new());
        self.get(idx, &mut sidenodes_wrap);
        let mut sidenodes = sidenodes_wrap.unwrap();

        let mut path = Self::leaf_index_to_path(&idx, self.depth);
        path.reverse();
        let mut cur_val = val.clone();

        // Iterate over the base 8 digits
        for d in path {
            let mut side_elem = sidenodes.pop().unwrap().to_vec();
            // Insert the value at the position determined by the base 4 digit
            side_elem.insert(d as usize, cur_val);

            let mut input: DBVal = [FieldElement::zero(); ARITY];
            input.copy_from_slice(side_elem.as_slice());
            let h = Poseidon_hash_8(input.clone(), self.hash_params, &SboxType::Quint);
            self.update_db_with_key_val(&h, input);
            cur_val = h;
        }

        self.root = cur_val;

        cur_val
    }

    /// Get a value from tree, if `proof` is not None, populate `proof` with the merkle proof
    pub fn get(&self, idx: FieldElement, proof: &mut Option<Vec<ProofNode>>) -> FieldElement {
        let path = Self::leaf_index_to_path(&idx, self.depth);
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<ProofNode>::new();

        for d in path {
            let k = cur_node.to_bytes();
            let children = self.db.get(&k).unwrap();
            cur_node = children[d as usize];
            if need_proof {
                let mut proof_node: ProofNode = [FieldElement::zero(); ARITY-1];
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
            None => (),
        }

        cur_node
    }

    /// Verify a merkle proof, if `root` is None, use the current root else use given root
    pub fn verify_proof(
        &self,
        idx: FieldElement,
        val: FieldElement,
        proof: &[ProofNode],
        root: Option<&FieldElement>,
    ) -> bool {
        let mut path = Self::leaf_index_to_path(&idx, self.depth);
        path.reverse();
        let mut cur_val = val.clone();

        for (i, d) in path.iter().enumerate() {
            let mut p = proof[self.depth - 1 - i].clone().to_vec();
            p.insert(*d as usize, cur_val);
            let mut input: DBVal = [FieldElement::zero(); ARITY];
            input.copy_from_slice(p.as_slice());
            cur_val = Poseidon_hash_8(input.clone(), self.hash_params, &SboxType::Quint);
        }

        // Check if root is equal to cur_val
        match root {
            Some(r) => cur_val == *r,
            None => cur_val == self.root,
        }
    }

    /// Convert leaf index to base 8
    pub fn leaf_index_to_path(idx: &FieldElement, depth: usize) -> Vec<u8> {
        let leaf_index_byte_size = depth / ARITY;
        get_base_8_repr(idx, leaf_index_byte_size).to_vec()
    }

    fn update_db_with_key_val(&mut self, key: &FieldElement, val: DBVal) {
        self.db.insert(key.to_bytes(), val);
    }
}

pub fn vanilla_merkle_merkle_tree_8_verif_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    expected_root: &FieldElement,
    leaf_val: AllocatedQuantity,
    leaf_index: AllocatedQuantity,
    mut proof_nodes: Vec<AllocatedQuantity>,
    zero: AllocatedQuantity,
    poseidon_params: &PoseidonParams,
    sbox_type: &SboxType,
) -> Result<(), R1CSError> {
    let mut prev_hash = LinearCombination::from(leaf_val.variable);

    let zero: LinearCombination = zero.variable.into();

    unimplemented!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::get_generators;

    const TreeDepth: usize = 16;

    #[test]
    fn test_vanilla_sparse_merkle_tree_8() {
        let width = 9;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 57;
        let hash_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);

        let mut tree = VanillaSparseMerkleTree_8::new(&hash_params, TreeDepth);

        for i in 1..20 {
            let s = FieldElement::from(i as u64);
            tree.update(s, s);
        }

        for i in 1..20 {
            let s = FieldElement::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<ProofNode>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(s, s, &proof_vec, None));
            assert!(tree.verify_proof(s, s, &proof_vec, Some(&tree.root)));
        }

        let kvs: Vec<(FieldElement, FieldElement)> = (0..20)
            .map(|_| (FieldElement::random(), FieldElement::random()))
            .collect();
        for i in 0..kvs.len() {
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }
}