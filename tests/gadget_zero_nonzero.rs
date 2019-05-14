extern crate merlin;
extern crate rand;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;
mod utils;
use utils::constrain_lc_with_scalar;
use utils::zero_non_zero::{is_zero_gadget, is_nonzero_gadget};

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::group_elem::{GroupElement, GroupElementVector};
    use bulletproofs::utils::field_elem::FieldElement;

    #[test]
    fn test_is_zero_non_zero() {
        let G: GroupElementVector = get_generators("G", 128).into();
        let H: GroupElementVector = get_generators("H", 128).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        // To prove/verify value == 0, set y = 0 and inv = 0
        // To prove/verify value != 0, set y = 1 and inv = value^-1

        let mut rng = rand::thread_rng();

        {
            let inv = 0;
            let y = 0;

            let (proof, commitment) = {
                let value = FieldElement::zero();
                let mut prover_transcript = Transcript::new(b"ZeroTest");
                let mut prover = Prover::new(&g, &h, &mut prover_transcript);

                let (com_val, var_val) = prover.commit(value.clone(), FieldElement::random(None));
                let alloc_scal = AllocatedQuantity {
                    variable: var_val,
                    assignment: Some(value),
                };
                assert!(is_zero_gadget(&mut prover, alloc_scal).is_ok());

                let proof = prover.prove(&G, &H).unwrap();

                (proof, com_val)
            };

            let mut verifier_transcript = Transcript::new(b"ZeroTest");
            let mut verifier = Verifier::new(&mut verifier_transcript);
            let var_val = verifier.commit(commitment);
            let alloc_scal = AllocatedQuantity {
                variable: var_val,
                assignment: None,
            };

            assert!(is_zero_gadget(&mut verifier, alloc_scal).is_ok());

            verifier.verify(&proof, &g, &h, &G, &H).unwrap();
        }

        {
            let (proof, commitments) = {

                let value = FieldElement::random(None);
                let inv = value.inverse();
                let mut prover_transcript = Transcript::new(b"NonZeroTest");
                let mut prover = Prover::new(&g, &h, &mut prover_transcript);

                let (com_val, var_val) = prover.commit(value.clone(), FieldElement::random(None));
                let alloc_scal = AllocatedQuantity {
                    variable: var_val,
                    assignment: Some(value),
                };

                let (com_val_inv, var_val_inv) = prover.commit(inv.clone(), FieldElement::random(None));
                let alloc_scal_inv = AllocatedQuantity {
                    variable: var_val_inv,
                    assignment: Some(inv),
                };
                assert!(is_nonzero_gadget(&mut prover, alloc_scal, alloc_scal_inv).is_ok());

                let proof = prover.prove(&G, &H).unwrap();

                (proof, (com_val, com_val_inv))
            };

            let mut verifier_transcript = Transcript::new(b"NonZeroTest");
            let mut verifier = Verifier::new(&mut verifier_transcript);
            let var_val = verifier.commit(commitments.0);
            let alloc_scal = AllocatedQuantity {
                variable: var_val,
                assignment: None,
            };

            let var_val_inv = verifier.commit(commitments.1);
            let alloc_scal_inv = AllocatedQuantity {
                variable: var_val_inv,
                assignment: None,
            };

            assert!(is_nonzero_gadget(&mut verifier, alloc_scal, alloc_scal_inv).is_ok());

            verifier.verify(&proof, &g, &h, &G, &H).unwrap();
        }
    }
}