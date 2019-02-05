use crate::types::BigNum;

use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};
use crate::utils::negate_field_element;

type Scalar = BigNum;

#[derive(Copy, Clone, Debug)]
pub enum Variable {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
}

#[derive(Copy, Clone, Debug)]
pub struct AllocatedQuantity {
    pub variable: Variable,
    pub assignment: Option<BigNum>
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug)]
pub struct LinearCombination {
    pub terms: Vec<(Variable, Scalar)>,
}

impl Default for LinearCombination {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl From<Variable> for LinearCombination {
    fn from(v: Variable) -> LinearCombination {
        let one = BigNum::new_int(1);
        LinearCombination {
            terms: vec![(v, one)],
        }
    }
}

// Arithmetic on linear combinations

impl Neg for LinearCombination {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = negate_field_element(s);
        }
        self
    }
}

impl<L: Into<LinearCombination>> Add<L> for LinearCombination {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().cloned());
        LinearCombination { terms: self.terms }
    }
}

impl<L: Into<LinearCombination>> Sub<L> for LinearCombination {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms
            .extend(rhs.into().terms.iter().map(|(var, coeff)| (*var, negate_field_element(coeff))));
        LinearCombination { terms: self.terms }
    }
}

// Arithmetic on variables produces linear combinations

impl Add<Variable> for Scalar {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, BigNum::new_int(1))],
        }
    }
}

impl Neg for Variable {
    type Output = LinearCombination;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}
