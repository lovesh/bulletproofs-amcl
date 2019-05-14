extern crate merlin;
extern crate rand;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;
/*mod util;
use util::{constrain_lc_with_scalar};*/
mod utils;
use utils::constrain_lc_with_scalar;


// Ensure `v` is a bit, hence 0 or 1
pub fn bit_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity
) -> Result<(), R1CSError> {
    // TODO: Possible to save reallocation of `v` in `bit`?
    let (a, b, o) = cs.allocate_multiplier(v.assignment.map(|bit| {
        ((FieldElement::one() - bit), bit)
    }))?;

    // Might not be necessary if above TODO is addressed
    // Variable b is same as v so b + (-v) = 0
    let neg_v: LinearCombination = vec![(v.variable, FieldElement::minus_one())].iter().collect();
    cs.constrain(b + neg_v);

    // Enforce a * b = 0, so one of (a,b) is zero
    cs.constrain(o.into());

    // Might not be necessary if above TODO is addressed
    // Enforce that a = 1 - b, so they both are 1 or 0.
    cs.constrain(a + (b - FieldElement::one()));

    Ok(())
}

// Ensure sum of items of `vector` is `sum`
pub fn vector_sum_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vector: &[AllocatedQuantity],
    sum: u64
) -> Result<(), R1CSError> {
    let mut constraints = vec![(Variable::One(), FieldElement::from(sum).negation())];
    for i in vector {
        constraints.push((i.variable, FieldElement::one()));
    }

    cs.constrain(constraints.iter().collect());

    Ok(())
}

// TODO: Find better name
// Ensure items[i] * vector[i] = vector[i] * value
pub fn vector_product_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    items: &[u64],
    vector: &[AllocatedQuantity],
    value: &AllocatedQuantity
) -> Result<(), R1CSError> {
    let mut constraints = vec![(value.variable, FieldElement::minus_one())];

    for i in 0..items.len() {

        // TODO: Possible to save reallocation of elements of `vector` in `bit`? If circuit variables for vector are passed, then yes.
        let (bit_var, item_var, o1) = cs.allocate_multiplier(vector[i].assignment.map( |bit| {
            (bit, items[i].into())
        }))?;
        constrain_lc_with_scalar::<CS>(cs, item_var.into(), &items[i].into());

        let (_, _, o2) = cs.multiply(bit_var.into(), value.variable.into());

        cs.constrain(o1 - o2);

        constraints.push((o1, FieldElement::one()));

    }

    // Constrain the sum of output variables to be equal to the value of committed variable
    cs.constrain(constraints.iter().collect());

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
    fn set_membership_check_gadget() {
        let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
        let value = 3u64;

        assert!(set_membership_check_helper(value, set).is_ok());
    }

    // Allocate a bitmap for the `set` with 1 as the index of `value`, 0 otherwise. Then commit to values of bitmap
    // and prove that each element is either 0 or 1, sum of elements of this bitmap is 1 (as there is only 1 element)
    // and the relation set[i] * bitmap[i] = bitmap[i] * value.
    // Taken from https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/one_of_n.hpp
    fn set_membership_check_helper(value: u64, set: Vec<u64>) -> Result<(), R1CSError> {
        let G: GroupElementVector = get_generators("G", 64).into();
        let H: GroupElementVector = get_generators("H", 64).into();
        let g =  GroupElement::from_msg_hash("g".as_bytes());
        let h =  GroupElement::from_msg_hash("h".as_bytes());

        let set_length = set.len();

        let (proof, commitments) = {
            // Set all indices to 0 except the one where `value` is
            let bit_map: Vec<u64> = set.iter().map(|elem| {
                if *elem == value { 1 } else { 0 }
            }).collect();

            let mut comms = vec![];

            let mut prover_transcript = Transcript::new(b"SetMemebershipTest");

            let mut prover = Prover::new(&g, &h, &mut prover_transcript);

            let mut bit_vars = vec![];
            for b in bit_map {
                let _b = FieldElement::from(b);
                let (com, var) = prover.commit(_b.clone(), FieldElement::random(None));
                let quantity = AllocatedQuantity {
                    variable: var,
                    assignment: Some(_b),
                };
                assert!(bit_gadget(&mut prover, quantity).is_ok());
                comms.push(com);
                bit_vars.push(quantity);
            }

            // The bit vector sum should be 1
            assert!(vector_sum_gadget(&mut prover, &bit_vars, 1).is_ok());

            let _value = FieldElement::from(value);
            let (com_value, var_value) = prover.commit(_value, FieldElement::random(None));
            let quantity_value = AllocatedQuantity {
                variable: var_value,
                assignment: Some(_value),
            };
            assert!(vector_product_gadget(&mut prover, &set, &bit_vars, &quantity_value).is_ok());
            comms.push(com_value);

            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove(&G, &H)?;

            (proof, comms)
        };

        println!("Proving done");
        let mut verifier_transcript = Transcript::new(b"SetMemebershipTest");
        let mut verifier = Verifier::new(&mut verifier_transcript);

        let mut bit_vars = vec![];

        for i in 0..set_length {
            let var = verifier.commit(commitments[i]);
            let quantity = AllocatedQuantity {
                variable: var,
                assignment: None,
            };
            assert!(bit_gadget(&mut verifier, quantity).is_ok());
            bit_vars.push(quantity);
        }

        assert!(vector_sum_gadget(&mut verifier, &bit_vars, 1).is_ok());

        let var_val = verifier.commit(commitments[set_length]);
        let quantity_value = AllocatedQuantity {
            variable: var_val,
            assignment: None,
        };

        assert!(vector_product_gadget(&mut verifier, &set, &bit_vars, &quantity_value).is_ok());

//        println!("Verifier commitments {:?}", &commitments);

        Ok(verifier.verify(&proof, &g, &h, &G, &H)?)
    }
}
