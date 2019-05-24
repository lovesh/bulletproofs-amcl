extern crate merlin;
extern crate rand;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;

mod utils;
use utils::poseidon::{PoseidonParams, Poseidon_permutation, Poseidon_permutation_gadget, Poseidon_hash_2, Poseidon_hash_2_gadget, SboxType, PADDING_CONST};


#[cfg(test)]
mod tests {
    use super::*;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::group_elem::{GroupElement, GroupElementVector};
    use bulletproofs::utils::field_elem::FieldElement;
    
    // For benchmarking
    use std::time::{Duration, Instant};
    use bulletproofs_amcl::utils::commitment::commit_to_field_element;

    fn poseidon_perm(sbox_type: &SboxType, transcript_label: &'static [u8]) {
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 140;
        let s_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let total_rounds = full_b + full_e + partial_rounds;

        let input = (0..width).map(|_| FieldElement::random(None)).collect::<Vec<_>>();
        let expected_output = Poseidon_permutation(&input, &s_params, sbox_type);

        println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);

        let G: GroupElementVector = get_generators("G", 2048).into();
        let H: GroupElementVector = get_generators("H", 2048).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(transcript_label);
            let mut prover = Prover::new(&g, &h, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for i in 0..width {
                let (com, var) = prover.commit(input[i].clone(), FieldElement::random(None));
                comms.push(com);
                allocs.push(AllocatedQuantity {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(Poseidon_permutation_gadget(&mut prover,
                                                     allocs,
                                                     &s_params,
                                                sbox_type,
                                                     &expected_output).is_ok());

            let proof = prover.prove(&G, &H).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(transcript_label);
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for i in 0..width {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedQuantity {
                variable: v,
                assignment: None,
            });
        }
        assert!(Poseidon_permutation_gadget(&mut verifier,
                                                 allocs,
                                                 &s_params,
                                            sbox_type,
                                                 &expected_output).is_ok());

        assert!(verifier.verify(&proof, &g, &h, &G, &H).is_ok());
    }
    
    fn poseidon_hash(sbox_type: &SboxType, transcript_label: &'static [u8]) {
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 144;
        let s_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let total_rounds = full_b + full_e + partial_rounds;

        let xl = FieldElement::random(None);
        let xr = FieldElement::random(None);
        let expected_output = Poseidon_hash_2(xl, xr, &s_params, sbox_type);

        let G: GroupElementVector = get_generators("G", 2048).into();
        let H: GroupElementVector = get_generators("H", 2048).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(transcript_label);
            let mut prover = Prover::new(&g, &h, &mut prover_transcript);

            let mut comms = vec![];
            let mut statics = vec![];

            let (com_l, var_l) = prover.commit(xl.clone(), FieldElement::random(None));
            comms.push(com_l);
            let l_alloc = AllocatedQuantity {
                variable: var_l,
                assignment: Some(xl),
            };

            let (com_r, var_r) = prover.commit(xr.clone(), FieldElement::random(None));
            comms.push(com_r);
            let r_alloc = AllocatedQuantity {
                variable: var_r,
                assignment: Some(xr),
            };

            // Commitment to PADDING_CONST with blinding as 0
            let (_, var) = prover.commit(FieldElement::from(PADDING_CONST), FieldElement::zero());
            statics.push(AllocatedQuantity {
                variable: var,
                assignment: Some(FieldElement::from(PADDING_CONST)),
            });

            // Commit to 0 with randomness 0 for the rest of the elements of width
            for _ in 3..width {
                let (_, var) = prover.commit(FieldElement::zero(), FieldElement::zero());
                statics.push(AllocatedQuantity {
                    variable: var,
                    assignment: Some(FieldElement::zero()),
                });
            }

            let start = Instant::now();
            assert!(Poseidon_hash_2_gadget(&mut prover,
                                           l_alloc,
                                           r_alloc,
                                           statics,
                                           &s_params,
                                           sbox_type,
                                           &expected_output).is_ok());

            println!("For Poseidon hash rounds {}, no of constraints is {}", total_rounds, &prover.num_constraints());
            println!("Proving time is: {:?}", start.elapsed());

            let proof =  prover.prove(&G, &H).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(transcript_label);
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut statics = vec![];
        let lv = verifier.commit(commitments[0]);
        let rv = verifier.commit(commitments[1]);
        let l_alloc = AllocatedQuantity {
            variable: lv,
            assignment: None,
        };
        let r_alloc = AllocatedQuantity {
            variable: rv,
            assignment: None,
        };

        // Commitment to PADDING_CONST with blinding as 0
        let pad_comm = commit_to_field_element(&g, &h, &FieldElement::from(PADDING_CONST), &FieldElement::zero());
        let v = verifier.commit(pad_comm);
        statics.push(AllocatedQuantity {
            variable: v,
            assignment: None,
        });

        // Commitment to 0 with blinding as 0
        let zero_comm = commit_to_field_element(&g, &h, &FieldElement::zero(), &FieldElement::zero());

        for i in 3..width {
            let v = verifier.commit(zero_comm.clone());
            statics.push(AllocatedQuantity {
                variable: v,
                assignment: None,
            });
        }

        let start = Instant::now();
        assert!(Poseidon_hash_2_gadget(&mut verifier,
                                       l_alloc,
                                       r_alloc,
                                       statics,
                                       &s_params,
                                       sbox_type,
                                       &expected_output).is_ok());

        assert!(verifier.verify(&proof, &g, &h, &G, &H).is_ok());
        println!("Verification time is: {:?}", start.elapsed());
    }

    #[test]
    fn test_poseidon_perm_cube_sbox() {
        poseidon_perm(&SboxType::Cube, b"Poseidon_perm_cube");
    }

    #[test]
    fn test_poseidon_perm_inverse_sbox() {
        poseidon_perm(&SboxType::Inverse, b"Poseidon_perm_inverse");
    }

    #[test]
    fn test_poseidon_hash_cube_sbox() {
        poseidon_hash(&SboxType::Cube, b"Poseidon_hash_cube");
    }

    #[test]
    fn test_poseidon_hash_inverse_sbox() {
        poseidon_hash(&SboxType::Inverse, b"Poseidon_hash_inverse");
    }
}