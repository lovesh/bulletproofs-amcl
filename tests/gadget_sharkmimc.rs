extern crate merlin;
extern crate rand;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;

mod utils;
use utils::sharkmimc::{SharkMiMCParams, SharkMiMC, sharkmimc_gadget, apply_inverse_sbox, apply_cube_sbox, SboxType};


#[cfg(test)]
mod tests {
    use super::*;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::group_elem::{GroupElement, GroupElementVector};
    use bulletproofs::utils::field_elem::FieldElement;
    
    // For benchmarking
    use std::time::{Duration, Instant};
    
    #[test]
    fn test_sharkmimc_cube_sbox() {
        let num_branches = 4;
        let middle_rounds = 6;
        let s_params = SharkMiMCParams::new(num_branches, middle_rounds);
        let total_rounds = s_params.total_rounds;

        let G: GroupElementVector = get_generators("G", 2048).into();
        let H: GroupElementVector = get_generators("H", 2048).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        let input = vec![FieldElement::from(1u32), FieldElement::from(2u32), FieldElement::from(3u32), FieldElement::from(4u32)];
        let expected_output = SharkMiMC(&input, &s_params, &apply_cube_sbox);

        println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"SharkMiMC");
            let mut prover = Prover::new(&g, &h, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for i in 0..num_branches {
                let (com, var) = prover.commit(input[i].clone(), FieldElement::random(None));
                comms.push(com);
                allocs.push(AllocatedQuantity {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(sharkmimc_gadget(&mut prover,
                                     allocs,
                                     &s_params,
                                     &SboxType::Cube,
                                     &expected_output).is_ok());

            let proof = prover.prove(&G, &H).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(b"SharkMiMC");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for i in 0..num_branches {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedQuantity {
                variable: v,
                assignment: None,
            });
        }
        assert!(sharkmimc_gadget(&mut verifier,
                                 allocs,
                                 &s_params,
                                 &SboxType::Cube,
                                 &expected_output).is_ok());

        assert!(verifier.verify(&proof, &g, &h, &G, &H).is_ok());
    }

    #[test]
    fn test_sharkmimc_inverse_sbox() {
        let num_branches = 4;
        let middle_rounds = 6;
        let s_params = SharkMiMCParams::new(num_branches, middle_rounds);
        let total_rounds = s_params.total_rounds;

        let G: GroupElementVector = get_generators("G", 2048).into();
        let H: GroupElementVector = get_generators("H", 2048).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        let input = vec![FieldElement::from(1u32), FieldElement::from(2u32), FieldElement::from(3u32), FieldElement::from(4u32)];
        let expected_output = SharkMiMC(&input, &s_params, &apply_inverse_sbox);

        println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"SharkMiMC");
            let mut prover = Prover::new(&g, &h, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for i in 0..num_branches {
                let (com, var) = prover.commit(input[i].clone(), FieldElement::random(None));
                comms.push(com);
                allocs.push(AllocatedQuantity {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(sharkmimc_gadget(&mut prover,
                                     allocs,
                                     &s_params,
                                     &SboxType::Inverse,
                                     &expected_output).is_ok());

            let proof = prover.prove(&G, &H).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(b"SharkMiMC");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for i in 0..num_branches {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedQuantity {
                variable: v,
                assignment: None,
            });
        }
        assert!(sharkmimc_gadget(&mut verifier,
                                 allocs,
                                 &s_params,
                                 &SboxType::Inverse,
                                 &expected_output).is_ok());

        assert!(verifier.verify(&proof, &g, &h, &G, &H).is_ok());
    }
}