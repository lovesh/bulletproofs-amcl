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
use utils::zero_non_zero::is_nonzero_gadget;


pub fn set_non_membership_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    diff_vars: Vec<AllocatedQuantity>,
    diff_inv_vars: Vec<AllocatedQuantity>,
    set: &[u64]
) -> Result<(), R1CSError> {
    let set_length = set.len();

    for i in 0..set_length {
        // Since `diff_vars[i]` is `set[i] - v`, `diff_vars[i]` + `v` should be `set[i]`
        constrain_lc_with_scalar::<CS>(cs, diff_vars[i].variable + v.variable, &FieldElement::from(set[i]));

        // Ensure `set[i] - v` is non-zero
        is_nonzero_gadget(cs, diff_vars[i], diff_inv_vars[i])?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::group_elem::{GroupElement, GroupElementVector};
    use bulletproofs::utils::field_elem::FieldElement;

    #[test]
    fn set_non_membership_check_gadget() {
        let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
        let value = 10u64;

        assert!(set_non_membership_check_helper(value, set).is_ok());
    }

    // Prove that difference between each set element and value is non-zero, hence value does not equal any set element.
    fn set_non_membership_check_helper(value: u64, set: Vec<u64>) -> Result<(), R1CSError> {
        let G: GroupElementVector = get_generators("G", 128).into();
        let H: GroupElementVector = get_generators("H", 128).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        let set_length = set.len();

        let (proof, commitments) = {
            let mut comms = vec![];
            let mut diff_vars: Vec<AllocatedQuantity> = vec![];
            let mut diff_inv_vars: Vec<AllocatedQuantity> = vec![];

            let mut prover_transcript = Transcript::new(b"SetNonMemebershipTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&g, &h, &mut prover_transcript);
            let value= FieldElement::from(value);
            let (com_value, var_value) = prover.commit(value.clone(), FieldElement::random(None));
            let alloc_scal = AllocatedQuantity {
                variable: var_value,
                assignment: Some(value),
            };
            comms.push(com_value);

            for i in 0..set_length {
                let elem = FieldElement::from(set[i]);
                let diff = elem - value;
                let diff_inv = diff.inverse();

                // Take difference of set element and value, `set[i] - value`
                let (com_diff, var_diff) = prover.commit(diff.clone(), FieldElement::random(None));
                let alloc_scal_diff = AllocatedQuantity {
                    variable: var_diff,
                    assignment: Some(diff),
                };
                diff_vars.push(alloc_scal_diff);
                comms.push(com_diff);

                // Inverse needed to prove that difference `set[i] - value` is non-zero
                let (com_diff_inv, var_diff_inv) = prover.commit(diff_inv.clone(), FieldElement::random(None));
                let alloc_scal_diff_inv = AllocatedQuantity {
                    variable: var_diff_inv,
                    assignment: Some(diff_inv),
                };
                diff_inv_vars.push(alloc_scal_diff_inv);
                comms.push(com_diff_inv);
            }

            assert!(set_non_membership_gadget(&mut prover, alloc_scal, diff_vars, diff_inv_vars, &set).is_ok());

//            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());

            let proof = prover.prove(&G, &H)?;

            (proof, comms)
        };

        let mut verifier_transcript = Transcript::new(b"SetNonMemebershipTest");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut diff_vars: Vec<AllocatedQuantity> = vec![];
        let mut diff_inv_vars: Vec<AllocatedQuantity> = vec![];

        let var_val = verifier.commit(commitments[0]);
        let alloc_scal = AllocatedQuantity {
            variable: var_val,
            assignment: None,
        };

        for i in 1..set_length+1 {
            let var_diff = verifier.commit(commitments[2*i-1]);
            let alloc_scal_diff = AllocatedQuantity {
                variable: var_diff,
                assignment: None,
            };
            diff_vars.push(alloc_scal_diff);

            let var_diff_inv = verifier.commit(commitments[2*i]);
            let alloc_scal_diff_inv = AllocatedQuantity {
                variable: var_diff_inv,
                assignment: None,
            };
            diff_inv_vars.push(alloc_scal_diff_inv);
        }

        assert!(set_non_membership_gadget(&mut verifier, alloc_scal, diff_vars, diff_inv_vars, &set).is_ok());

        Ok(verifier.verify(&proof, &g, &h, &G, &H)?)
    }
}
