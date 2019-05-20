extern crate merlin;
extern crate rand;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};


/// Constrain a linear combination to be equal to a scalar
pub fn constrain_lc_with_scalar<CS: ConstraintSystem>(cs: &mut CS, lc: LinearCombination, scalar: &FieldElement) {
    cs.constrain(lc - LinearCombination::from(*scalar));
}

pub mod positive_no;
pub mod zero_non_zero;
pub mod mimc;
pub mod sharkmimc;