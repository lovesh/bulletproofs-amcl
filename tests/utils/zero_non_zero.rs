use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;


/// if x == 0 then y = 0 else y = 1
/// if x != 0 then inv = x^-1 else inv = 0
/// x*(1-y) = 0
/// x*inv = y
/// The idea is described in the Pinocchio paper and i first saw it in https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/isnonzero.cpp

/// Enforces that x is 0.
pub fn is_zero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedQuantity
) -> Result<(), R1CSError> {
    let y: u32 = 0;
    let inv: u32 = 0;

    let x_lc: LinearCombination = vec![(x.variable, FieldElement::one())].iter().collect();
    let one_minus_y_lc: LinearCombination = vec![(Variable::One(), FieldElement::from(1-y))].iter().collect();
    let y_lc: LinearCombination = vec![(Variable::One(), FieldElement::from(y))].iter().collect();
    let inv_lc: LinearCombination = vec![(Variable::One(), FieldElement::from(inv))].iter().collect();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * inv = y
    let (_, _, o2) = cs.multiply(x_lc, inv_lc);
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}

/// Enforces that x is 0.
pub fn is_nonzero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedQuantity,
    x_inv: AllocatedQuantity,
) -> Result<(), R1CSError> {
    let y: u32 = 1;

    let x_lc: LinearCombination = vec![(x.variable, FieldElement::one())].iter().collect();
    let one_minus_y_lc: LinearCombination = vec![(Variable::One(), FieldElement::from(1-y))].iter().collect();
    let y_lc: LinearCombination = vec![(Variable::One(), FieldElement::from(y))].iter().collect();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * x_inv = y
    let inv_lc: LinearCombination = vec![(x_inv.variable, FieldElement::one())].iter().collect();
    let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    // Ensure x_inv is the really the inverse of x by ensuring x*x_inv = 1
    let (_, x_inv_var, o3) = cs.multiply(x_lc, inv_lc);
    // Output wire should be 1
    let one_lc: LinearCombination = vec![(Variable::One(), FieldElement::one())].iter().collect();
    cs.constrain(o3 - one_lc);
    Ok(())
}