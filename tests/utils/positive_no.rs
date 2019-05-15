use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn positive_no_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    n: usize
    ,) -> Result<(), R1CSError> {
    let mut constraint_v = vec![(v.variable, FieldElement::minus_one())];
    let mut exp_2 = FieldElement::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints

        let (a, b, o) = cs.allocate_multiplier(v.assignment.map(|q| {
            if (q.shift_right(i)).is_odd() {
                (FieldElement::zero(), FieldElement::one())
            } else {
                (FieldElement::one(), FieldElement::zero())
            }
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - FieldElement::one()));

        constraint_v.push((b, exp_2)  );
        exp_2 = exp_2 + exp_2;
    }

    // Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
    cs.constrain(constraint_v.iter().collect());

    Ok(())
}