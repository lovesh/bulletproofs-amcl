use crate::utils::field_elem::FieldElement;

use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};


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
    pub assignment: Option<FieldElement>
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug)]
pub struct LinearCombination {
    pub terms: Vec<(Variable, FieldElement)>,
}

impl Default for LinearCombination {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl From<Variable> for LinearCombination {
    fn from(v: Variable) -> LinearCombination {
        let one = FieldElement::one();
        LinearCombination {
            terms: vec![(v, one)],
        }
    }
}

impl From<FieldElement> for LinearCombination {
    fn from(s: FieldElement) -> LinearCombination {
        LinearCombination {
            terms: vec![(Variable::One(), s)],
        }
    }
}

impl FromIterator<(Variable, FieldElement)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
        where
            T: IntoIterator<Item = (Variable, FieldElement)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a> FromIterator<&'a (Variable, FieldElement)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
        where
            T: IntoIterator<Item = &'a (Variable, FieldElement)>,
    {
        LinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl Neg for LinearCombination {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = s.negation();
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
            .extend(rhs.into().terms.iter().map(|(var, coeff)| (*var, coeff.negation())));
        LinearCombination { terms: self.terms }
    }
}

// Arithmetic on variables produces linear combinations

impl Add<Variable> for FieldElement {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, FieldElement::one())],
        }
    }
}

impl<L: Into<LinearCombination>> Sub<L> for Variable {
    type Output = LinearCombination;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination::from(self) - other.into()
    }
}

impl Neg for Variable {
    type Output = LinearCombination;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

impl<L: Into<LinearCombination>> Add<L> for Variable {
    type Output = LinearCombination;

    fn add(self, other: L) -> Self::Output {
        LinearCombination::from(self) + other.into()
    }
}

// Arithmetic on FieldElement with variables produces linear combinations

impl Sub<Variable> for FieldElement {
    type Output = LinearCombination;

    fn sub(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, FieldElement::minus_one())],
        }
    }
}

impl Mul<Variable> for FieldElement {
    type Output = LinearCombination;

    fn mul(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(other, self)],
        }
    }
}

