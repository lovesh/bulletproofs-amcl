/// Gadget to prove that 2 merkle trees have only few leaves different.
/// The leaves that are chosen different is based on value of the nonce
/// It is known to verifier which leaves are distorted.
/// The circuit should take the original data root, distorted data and the original pixels which were distorted.
/// The idea is that the circuit will take call update as many times as the number of distorted leaves and eventually the root should match

use std::collections::{HashSet, HashMap};
use rand::{CryptoRng, RngCore};
use std::time::{Duration, Instant};

use amcl_wrapper::field_elem::{FieldElementVector, FieldElement};
use amcl_wrapper::constants::MODBYTES;
use amcl_wrapper::amcl::sha3::{SHA3, SHAKE256};
use amcl_wrapper::group_elem::GroupElement;
use amcl_wrapper::group_elem_g1::{G1, G1Vector};
use merlin::Transcript;

use super::helper_constraints::poseidon::{
    PoseidonParams, Poseidon_hash_4, Poseidon_hash_4_constraints, SboxType, PADDING_CONST,
};
use super::helper_constraints::sparse_merkle_tree_4_ary::{
    DBVal, ProofNode, VanillaSparseMerkleTree_4, vanilla_merkle_merkle_tree_4_verif_gadget
};

use crate::errors::R1CSError;
use crate::r1cs::linear_combination::AllocatedQuantity;
use crate::r1cs::{ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier};
use crate::r1cs::gadgets::poseidon_hash::{allocate_statics_for_prover, allocate_statics_for_verifier};

/// Hash to get a new number. For other variations a keyed permutation should be used.
fn randomize(x: &FieldElement) -> FieldElement {
    FieldElement::from_msg_hash(&x.to_bytes())
}

/// Generate `count_modified` numbers in range [0, data_size) using `nonce`. Uses SHAKE.
fn get_indices_to_modify(nonce: &FieldElement, data_size: usize, count_modified: usize) -> HashSet<FieldElement> {
    let mut hasher = SHA3::new(SHAKE256);
    for b in nonce.to_bytes() {
        hasher.process(b);
    }
    let target_byte_size = count_modified * MODBYTES;
    let mut target = vec![0u8; target_byte_size];
    hasher.shake(&mut target.as_mut_slice(), target_byte_size);
    let data_size_as_big = FieldElement::from(data_size as u64).to_bignum();
    let mut indices = HashSet::<FieldElement>::new();
    for _ in 0..count_modified {
        let b: Vec<_> = target.drain(0..MODBYTES).collect();
        let mut n = FieldElement::from_bytes(&b).unwrap().to_bignum();
        // TODO: Somewhat probable that modulo data_size leads to repetition.
        // If that is the case, generate use a bigger target_size with shake.
        n.rmod(&data_size_as_big);
        indices.insert(n.into());
    }
    indices
}

fn get_randomized_data(original_data: &FieldElementVector, indices: &HashSet<FieldElement>) -> (HashMap<FieldElement, FieldElement>, FieldElementVector) {
    // Keeps original values of the modified indices.
    let mut modified_indices = HashMap::<FieldElement, FieldElement>::new();
    let mut new_data = original_data.clone();
    for _i in indices {
        // Next line is a temporary workaround
        let i = _i.to_bignum().w[0] as usize;
        let randomized = randomize(&new_data[i]);
        modified_indices.insert(_i.clone(), new_data[i]);
        new_data[i] = randomized;
    }

    (modified_indices, new_data)
}

/// XXX PASSING TREES AS ARGUMENT IS A BAD IDEA.

/// Proves the presence of `orig_vals` in the tree with root `orig_root`.
/// Also proves that if `new_tree` is updated with `orig_vals`, its root becomes same `orig_root`
pub fn randomizer_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    orig_root: AllocatedQuantity,   // original root is hidden since its correlating across several proofs
    new_tree: &mut VanillaSparseMerkleTree_4,
    indices: Vec<FieldElement>,     // TODO: `indices` can be made hidden too
    orig_vals: Vec<AllocatedQuantity>,  // values of the original tree
    mut orig_vals_proofs: Vec<Vec<AllocatedQuantity>>,   // merkle proofs for values of the original tree
    statics: Vec<AllocatedQuantity>,
    poseidon_params: &PoseidonParams,
    sbox_type: &SboxType,
) -> Result<(), R1CSError> {
    assert_eq!(new_tree.depth, depth);
    assert_eq!(indices.len(), orig_vals.len());

    let statics: Vec<LinearCombination> = statics.iter().map(|s| s.variable.into()).collect();

    // Keep a map of (depth, position) -> LinearCombination for the new_tree for all nodes in paths of modified indices
    let mut new_tree_modified_nodes = HashMap::<(usize, u8), LinearCombination>::new();
    let root_key = (0usize, 0u8);

    for i in 0..indices.len() {
        let idx = indices[i];
        let orig_val = orig_vals[i];
        let mut orig_vals_proof = &mut orig_vals_proofs[i];

        // Prove index `idx` has value `orig_val` in tree with root `orig_root`.
        let mut path_for_update = VanillaSparseMerkleTree_4::leaf_index_to_path(&idx, depth);
        let mut path_for_get = path_for_update.clone();
        path_for_update.reverse();

        println!("path_for_update={:?}", &path_for_update);
        println!("path_for_get={:?}", &path_for_get);

        let mut cur_hash_in_orig_tree = orig_vals[i].variable.into();

        for pos in &path_for_update {
            let mut proof: Vec<LinearCombination> = vec![];
            proof.push(orig_vals_proof.pop().unwrap().variable.into());
            proof.push(orig_vals_proof.pop().unwrap().variable.into());
            proof.push(orig_vals_proof.pop().unwrap().variable.into());
            proof.reverse();
            proof.insert(*pos as usize, cur_hash_in_orig_tree);
            let input = [proof[0].clone(), proof[1].clone(), proof[2].clone(), proof[3].clone()];
            cur_hash_in_orig_tree = Poseidon_hash_4_constraints::<CS>(
                cs,
                input,
                statics.clone(),
                poseidon_params,
                sbox_type,
            )?;
        }

        cs.constrain(cur_hash_in_orig_tree - orig_root.variable);

        // Update new_tree with orig_val
        let mut proof_vec = Vec::<[LinearCombination; 3]>::new();
        let mut cur_node = new_tree.root.clone();

        let mut d = 1usize;
        for pos in path_for_get {
            //let proof_node = if new_tree_modified_nodes.contains_key(&(d, pos)) {
            let proof_node = if i != 0 {
                println!("Looking in new_tree_modified_nodes, i={}, d={}", i, d);
                let mut proof_node: [LinearCombination; 3] = [LinearCombination::default(), LinearCombination::default(), LinearCombination::default()];
                let mut c = 0;
                for k in 0..4 {
                    if k != pos {
                        println!("get new_tree_modified_nodes d={}, k={}", d, k);
                        proof_node[c] = new_tree_modified_nodes[&(d, k)].clone();
                        c += 1;
                    }
                }
                proof_node
            } else {
                println!("Looking in tree db, i={}, d={}", i, d);
                let mut children = new_tree.db.get(&cur_node.to_bytes()).unwrap().to_vec();
                cur_node = children.remove(pos as usize);
                let proof_node: [LinearCombination; 3] = [children[0].into(), children[1].into(), children[2].into()];
                proof_node
            };
            proof_vec.push(proof_node);
            d += 1;
        }

        println!("get d={}", d);

        let mut orig_val_lc = LinearCombination::from(orig_val.variable);
        let mut d = depth as usize;
        for pos in path_for_update {
            let mut proof = proof_vec.pop().unwrap().to_vec();
            proof.insert(pos as usize, orig_val_lc);
            let input = [proof[0].clone(), proof[1].clone(), proof[2].clone(), proof[3].clone()];
            for k in 0..4 {;
                println!("update new_tree_modified_nodes d={}, k={}", d, k);
                new_tree_modified_nodes.insert((d, k), input[k as usize].clone());
            }
            orig_val_lc = Poseidon_hash_4_constraints::<CS>(
                cs,
                input,
                statics.clone(),
                poseidon_params,
                sbox_type,
            )?;
            d -= 1;
        }
        println!("update d={}", d);
        new_tree_modified_nodes.insert(root_key.clone(), orig_val_lc);
    }

    cs.constrain(new_tree_modified_nodes[&root_key].clone() - orig_root.variable);

    Ok(())
}

pub fn gen_proof_for_randomizer(
    orig_tree: &VanillaSparseMerkleTree_4,
    new_tree: &mut VanillaSparseMerkleTree_4,
    modified_indices: &[FieldElement],
    orig_vals: &[FieldElement],
    tree_depth: usize,
    hash_params: &PoseidonParams,
    sbox_type: &SboxType,
    transcript_label: &'static [u8],
    g: &G1,
    h: &G1,
    G: &G1Vector,
    H: &G1Vector,
) -> Result<(R1CSProof, Vec<G1>), R1CSError> {
    let orig_root = orig_tree.root;

    let mut prover_transcript = Transcript::new(transcript_label);
    let mut prover = Prover::new(&g, &h, &mut prover_transcript);

    let mut comms = vec![];

    let (com_orig_root, var_orig_root) = prover.commit(orig_root.clone(), FieldElement::random());
    let orig_root_alloc_scalar = AllocatedQuantity {
        variable: var_orig_root,
        assignment: Some(orig_root),
    };
    comms.push(com_orig_root);

    let mut orig_val_alloc_scalars = vec![];
    let mut proof_alloc_scalars = vec![];

    //for (i, v) in modified_indices {
    for i in 0..modified_indices.len() {
        let mut merkle_proof_vec = Vec::<ProofNode>::new();
        let mut merkle_proof = Some(merkle_proof_vec);
        let _v = orig_tree.get(modified_indices[i], &mut merkle_proof);
        assert_eq!(_v, orig_vals[i]);
        let (com_orig_val, var_orig_val) = prover.commit(_v, FieldElement::random());
        comms.push(com_orig_val);
        orig_val_alloc_scalars.push(AllocatedQuantity {
            variable: var_orig_val,
            assignment: Some(_v),
        });
        merkle_proof_vec = merkle_proof.unwrap();
        //println!("merkle_proof_vec len {}", &merkle_proof_vec.len());
        let mut ps = vec![];
        for p in merkle_proof_vec.iter() {
            for j in p {
                let (c, v) = prover.commit(*j, FieldElement::random());
                comms.push(c);
                ps.push(AllocatedQuantity {
                    variable: v,
                    assignment: Some(*j),
                });
            }
        }
        proof_alloc_scalars.push(ps);
    }

    let num_statics = 2;
    let statics = allocate_statics_for_prover(&mut prover, num_statics);

    /*for j in 0..modified_indices.len() {
        new_tree.update(modified_indices[j].clone(), orig_vals[j].clone());
    }
    assert_eq!(new_tree.root, orig_root);*/

    let start = Instant::now();
    randomizer_gadget(
        &mut prover,
        tree_depth,
        orig_root_alloc_scalar,
        new_tree,
        modified_indices.to_vec(),
        orig_val_alloc_scalars,
        proof_alloc_scalars,
        statics,
        &hash_params,
        sbox_type,
    )?;

    let total_rounds = hash_params.full_rounds_beginning
        + hash_params.partial_rounds
        + hash_params.full_rounds_end;
    println!("For 4-ary tree of height {} (has 2^{} leaves) and Poseidon rounds {}, no of multipliers is {} and constraints is {}", tree_depth, tree_depth*2, total_rounds, &prover.num_multipliers(), &prover.num_constraints());

    let proof = prover.prove(G, H).unwrap();
    let end = start.elapsed();

    println!("Proving time is {:?}", end);

    Ok((proof, comms))
}

pub fn verify_proof_for_randomizer(
    new_tree: &mut VanillaSparseMerkleTree_4,
    modified_indices: &[FieldElement],     // TODO: `modified_indices` can be made hidden too
    tree_depth: usize,
    hash_params: &PoseidonParams,
    sbox_type: &SboxType,
    proof: R1CSProof,
    commitments: Vec<G1>,
    transcript_label: &'static [u8],
    g: &G1,
    h: &G1,
    G: &G1Vector,
    H: &G1Vector,
) -> Result<(), R1CSError> {
    let mut verifier_transcript = Transcript::new(transcript_label);
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let var_orig_root = verifier.commit(commitments[0]);
    let orig_root_alloc_scalar = AllocatedQuantity {
        variable: var_orig_root,
        assignment: None,
    };

    let mut orig_val_alloc_scalars = vec![];
    let mut proof_alloc_scalars = vec![];

    let mut ctr = 1;
    for _ in 0..modified_indices.len() {
        let var_orig_val = verifier.commit(commitments[ctr]);
        let orig_val_alloc_scalar = AllocatedQuantity {
            variable: var_orig_val,
            assignment: None,
        };
        orig_val_alloc_scalars.push(orig_val_alloc_scalar);
        ctr += 1;

        let mut ps = vec![];
        for _ in 0..tree_depth*3 {    // Proof length = tree depth * 3
            let var = verifier.commit(commitments[ctr]);
            let alloc_scalar = AllocatedQuantity {
                variable: var,
                assignment: None,
            };
            ps.push(alloc_scalar);
            ctr += 1;
        }
        proof_alloc_scalars.push(ps);
    }

    let num_statics = 2;
    let statics = allocate_statics_for_verifier(&mut verifier, num_statics, g, h);

    let start = Instant::now();
    randomizer_gadget(
        &mut verifier,
        tree_depth,
        orig_root_alloc_scalar,
        new_tree,
        modified_indices.to_vec(),
        orig_val_alloc_scalars,
        proof_alloc_scalars,
        statics,
        hash_params,
        sbox_type,
    )?;

    println!("Verification");
    verifier.verify(&proof, &g, &h, &G, &H)?;
    let end = start.elapsed();

    println!("Verification time is {:?}", end);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::get_generators;

    #[test]
    fn test_randomizer() {
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 1;
        let hash_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);

        let tree_depth = 4;
        let data_size = 100;
        let count_modified = 2;
        let original_data = FieldElementVector::random(data_size);
        let nonce = FieldElement::random();
        let indices = get_indices_to_modify(&nonce, data_size, count_modified);

        println!("Trying to modify {} entries. Will modify {} entries", count_modified, indices.len());
        /*let mut indices: HashSet<FieldElement> = HashSet::new();
        indices.insert(FieldElement::from(1u32));
        indices.insert(FieldElement::from(4u32));*/

        let mut orig_tree = VanillaSparseMerkleTree_4::new(&hash_params, tree_depth);
        for i in 0..data_size {
            // Next line is a temporary workaround
            let idx = FieldElement::from(i as u64);
            orig_tree.update(idx, original_data[i]);
        }
        let orig_root = orig_tree.root;

        let (modified_indices, new_data) = get_randomized_data(&original_data, &indices);
        // `new_data` is different from `original_data` only in `count_modified` values.
        // Check by creating sets over `new_data` and `original_data` and then intersecting them.
        // The intersection should have `data_size - count_modified` values.
        let mut orig_data_set: HashSet<&FieldElement> = original_data.iter().collect();
        let mut new_data_set: HashSet<&FieldElement> = new_data.iter().collect();
        let intersection: HashSet<_> = orig_data_set.intersection(&new_data_set).collect();
        assert_eq!(intersection.len(), data_size - count_modified);

        // Create new tree different from original tree
        let mut new_tree = orig_tree.clone();
        for (i, v) in &modified_indices {
            new_tree.update(i.clone(), randomize(v));
        }
        let new_root = new_tree.root;
        assert_ne!(orig_root, new_root);

        // Update new_tree back to old tree
        for (i, v) in &modified_indices {
            new_tree.update(*i, *v);
        }
        assert_eq!(orig_root, new_tree.root);

        // Create new tree different from original tree
        let mut new_tree_again = orig_tree.clone();
        for (i, v) in &modified_indices {
            new_tree_again.update(i.clone(), randomize(v));
        }
        let new_root_again = new_tree_again.root;
        assert_ne!(orig_root, new_root_again);

        let sbox_type = &SboxType::Quint;

        // TODO: Use iterators. Generating so many generators at once is very slow. In practice, generators will be persisted.
        let G: G1Vector = get_generators("G", 8192).into();
        let H: G1Vector = get_generators("H", 8192).into();

        let g = G1::from_msg_hash("g".as_bytes());
        let h = G1::from_msg_hash("h".as_bytes());

        let label = b"Randomizer";

        let mut idxs = vec![];
        let mut orig_vals = vec![];
        for (i, v) in modified_indices {
            idxs.push(i);
            orig_vals.push(v);
        }

        let (proof, commitments) = {
            let mut new_tree_clone = new_tree_again.clone();
            gen_proof_for_randomizer(
                &orig_tree,
                &mut new_tree_clone,
                &idxs,
                &orig_vals,
                tree_depth,
                &hash_params,
                sbox_type,
                label,
                &g,
                &h,
                &G,
                &H,
            )
                .unwrap()
        };

        {
            let mut new_tree_clone = new_tree_again.clone();
            verify_proof_for_randomizer(
                &mut new_tree_clone,
                &idxs,
                tree_depth,
                &hash_params,
                sbox_type,
                proof,
                commitments,
                label,
                &g,
                &h,
                &G,
                &H,
            )
                .unwrap();
        }
    }
}