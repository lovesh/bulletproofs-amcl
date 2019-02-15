#[macro_use] extern crate bulletproofs_amcl as bulletproofs;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;
use bulletproofs::types::BigNum;
use bulletproofs::constants::CurveOrder;
use bulletproofs::utils::negate_field_element;


// Ensure `v` is a bit, hence 0 or 1
pub fn bit_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity
) -> Result<(), R1CSError> {
    // TODO: Possible to save reallocation of `v` in `bit`?
    let (a, b, o) = cs.allocate(|| {
        let bit= v.assignment.ok_or(R1CSError::MissingAssignment)?.get(0) as u64;
        Ok((BigNum::new_int((1 - bit) as isize), BigNum::new_int(bit as isize), field_element_zero!()))
    })?;

    // Might not be necessary if above TODO is addressed
    // Variable b is same as v so b +
    let neg_v: LinearCombination = vec![(v.variable, field_element_neg_one!())].iter().collect();
    cs.constrain(b + neg_v);

    // Enforce a * b = 0, so one of (a,b) is zero
    cs.constrain(o.into());

    // Might not be necessary if above TODO is addressed
    // Enforce that a = 1 - b, so they both are 1 or 0.
    cs.constrain(a + (b - field_element_one!()));

    Ok(())
}

// Ensure sum of items of `vector` is `sum`
pub fn vector_sum_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vector: &[AllocatedQuantity],
    sum: u64
) -> Result<(), R1CSError> {
    let mut constraints = vec![(Variable::One(), negate_field_element(&BigNum::new_int(sum as isize)))];
    for i in vector {
        constraints.push((i.variable, field_element_one!()));
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
    let mut constraints = vec![(value.variable, field_element_neg_one!())];

    for i in 0..items.len() {

        // TODO: Possible to save reallocation of elements of `vector` in `bit`?
        let (a, b, o) = cs.allocate(|| {
            let bit: u64 = vector[i].assignment.ok_or(R1CSError::MissingAssignment)?.get(0) as u64;
            let val = if bit == 1 {
                value.assignment.ok_or(R1CSError::MissingAssignment)?
            } else {
                field_element_zero!()
            };
            Ok((BigNum::new_int(items[i] as isize), BigNum::new_int(bit as isize), val))
        })?;

        constraints.push((o, field_element_one!()));

        // Constrain `a` to be same as items[i]
        let item_var: LinearCombination = vec![(Variable::One(), BigNum::new_int(items[i] as isize))].iter().collect();
        cs.constrain(a - item_var);

        // Each `b` is already constrained to be 0 or 1
    }

    // Constrain the sum of output variables to be equal to the value of committed variables
    cs.constrain(constraints.iter().collect());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::utils::hash_on_GroupG1;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::random_field_element;

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
        let G = get_generators("g", 64);
        let H = get_generators("h", 64);
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        let set_length = set.len();

        let (proof, commitments) = {
            // Set all indices to 0 except the one where `value` is
            let bit_map: Vec<u64> = set.iter().map(|elem| {
                if *elem == value { 1 } else { 0 }
            }).collect();

            let mut comms = vec![];

            let mut prover_transcript = Transcript::new(b"SetMemebershipTest");

            let mut prover = Prover::new(&G, &H, &g, &h, &mut prover_transcript);

            let mut bit_vars = vec![];
            for b in bit_map {
                let _b = BigNum::new_int(b as isize);
                let (com, var) = prover.commit(_b, random_scalar!());
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

            let _value = BigNum::new_int(value as isize);
            let (com_value, var_value) = prover.commit(_value, random_scalar!());
            let quantity_value = AllocatedQuantity {
                variable: var_value,
                assignment: Some(_value),
            };
            assert!(vector_product_gadget(&mut prover, &set, &bit_vars, &quantity_value).is_ok());
            comms.push(com_value);

            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove()?;

            (proof, comms)
        };

        println!("Proving done");
        let mut verifier_transcript = Transcript::new(b"SetMemebershipTest");
        let mut verifier = Verifier::new(&G, &H, &g, &h, &mut verifier_transcript);

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

        Ok(verifier.verify(&proof)?)
    }
}