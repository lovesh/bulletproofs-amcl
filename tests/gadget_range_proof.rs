/*
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


/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn positive_no_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    n: usize,
) -> Result<(), R1CSError> {
    let mut constraint = vec![(v.variable, field_element_neg_one!())];
    let mut exp_2 = field_element_one!();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate(|| {
            let q= v.assignment.ok_or(R1CSError::MissingAssignment)?.get(0) as u64;
            let bit: u64 = (q >> i) & 1;
            Ok((BigNum::new_int((1 - bit) as isize), BigNum::new_int(bit as isize), field_element_zero!()))
        })?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - field_element_one!()));

        constraint.push((b, exp_2)  );
        exp_2 = add_field_elements!(&exp_2, &exp_2);
    }

    // Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
    cs.constrain(constraint.iter().collect());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::hash_on_GroupG1;
    use bulletproofs::utils::random_field_element;

    #[test]
    fn bound_check_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng = OsRng::new().unwrap();
        let min = 10;
        let max = 100;

        let v = rng.gen_range(min, max);
        println!("v is {}", &v);
        assert!(bound_check_helper(v, min, max).is_ok());
    }

    fn bound_check_helper(v: u64, min: u64, max: u64) -> Result<(), R1CSError> {
        assert!(v >= min);
        assert!(max >= v);
        // TODO: Use correct bit size of the field
        let n = 32;

        let a = v - min;
        let b = max - v;
        println!("a, b are {} {}", &a, &b);

        let v = BigNum::new_int(v as isize);
        let a = BigNum::new_int(a as isize);
        let b = BigNum::new_int(b as isize);
        let c = BigNum::new_int((max-min) as isize);

        let G = get_generators("g", 64);
        let H = get_generators("h", 64);
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        // Prover's scope
        let (proof, commitments) = {
            let mut comms = vec![];

            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"BoundsTest");

            let mut prover = Prover::new(&G, &H, &g, &h, &mut prover_transcript);

            // Constrain a in [0, 2^n)
            let (com_a, var_a) = prover.commit(a, random_scalar!());
            let quantity_a = AllocatedQuantity {
                variable: var_a,
                assignment: Some(a),
            };
            assert!(positive_no_gadget(&mut prover, quantity_a, n).is_ok());
            comms.push(com_a);

            // Constrain b in [0, 2^n)
            let (com_b, var_b) = prover.commit(b, random_scalar!());
            let quantity_b = AllocatedQuantity {
                variable: var_b,
                assignment: Some(b),
            };
            assert!(positive_no_gadget(&mut prover, quantity_b, n).is_ok());
            comms.push(com_b);

            // Constrain a+b to be same as max-min. This ensures same v is used in both commitments (`com_a` and `com_b`)
            let var_c: LinearCombination =  vec![(Variable::One(), c.clone())].iter().collect();
            prover.constrain(var_a + var_b - var_c);

            println!("For {} in ({}, {}), no of constraints is {}", v, min, max, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove()?;

            (proof, comms)
        };

        println!("Proving done");
        let mut verifier_transcript = Transcript::new(b"BoundsTest");
        let mut verifier = Verifier::new(&G, &H, &g, &h, &mut verifier_transcript);

        let var_a = verifier.commit(commitments[0]);
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: None,
        };
        assert!(positive_no_gadget(&mut verifier, quantity_a, n).is_ok());

        let var_b = verifier.commit(commitments[1]);
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: None,
        };
        assert!(positive_no_gadget(&mut verifier, quantity_b, n).is_ok());

//        println!("Verifier commitments {:?}", &commitments);

        let var_c: LinearCombination = vec![(Variable::One(), c)].iter().collect();
        verifier.constrain(var_a + var_b - var_c);

        // Verifier verifies proof
        Ok(verifier.verify(&proof)?)
    }
}*/
