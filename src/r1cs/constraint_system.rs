//! Definition of the constraint system trait.


use crate::types::BigNum;
use crate::r1cs::linear_combination::LinearCombination;
use crate::r1cs::linear_combination::Variable;
use crate::errors::R1CSError;

type Scalar = BigNum;

/// The interface for a constraint system, abstracting over the prover
/// and verifier's roles.
///
/// Statements to be proved by an [`R1CSProof`](::r1cs::R1CSProof) are specified by
/// programmatically constructing constraints.  These constraints need
/// to be identical between the prover and verifier, since the prover
/// and verifier need to construct the same statement.
///
/// To prevent code duplication or mismatches between the prover and
/// verifier, gadgets for the constraint system should be written
/// using the `ConstraintSystem` trait, so that the prover and
/// verifier share the logic for specifying constraints.
pub trait ConstraintSystem {
    /// Represents a concrete type for the CS in a randomization phase.
    type RandomizedCS: RandomizedConstraintSystem;

    /// Allocate and constrain multiplication variables.
    ///
    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    /// and add the explicit constraints that
    /// ```text
    /// left = left_constraint
    /// right = right_constraint
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable);

    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>;

    /// Enforce the explicit constraint that
    /// ```text
    /// lc = 0
    /// ```
    fn constrain(&mut self, lc: LinearCombination);

    /// Specify additional variables and constraints randomized using a challenge scalar
    /// bound to the assignments of the non-randomized variables.
    ///
    /// If the constraint system’s low-level variables have not been committed yet,
    /// the call returns `Ok()` and saves a callback until later.
    ///
    /// If the constraint system’s low-level variables are committed already,
    /// the callback is invoked immediately and its result is return from this method.
    ///
    /// ### Usage
    ///
    /// Inside the closure you can generate one or more challenges using `challenge_scalar` method.
    ///
    /// ```text
    /// cs.specify_randomized_constraints(move |cs| {
    ///     let z = cs.challenge_scalar(b"some challenge");
    ///     // ...
    /// })
    /// ```
    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>;
}

/// Represents a constraint system in the second phase:
/// when the challenges can be sampled to create randomized constraints.
///
/// Note: this trait also includes `ConstraintSystem` trait
/// in order to allow composition of gadgets: e.g. a shuffle gadget can be used in both phases.
pub trait RandomizedConstraintSystem: ConstraintSystem {
    /// Generates a challenge scalar.
    ///
    /// ### Usage
    ///
    /// This method is available only within the scope of a closure provided
    /// to `specify_randomized_constraints`, which implements
    /// the "randomization" phase of the protocol.
    ///
    /// Arbitrary number of challenges can be generated with additional calls.
    ///
    /// ```text
    /// cs.specify_randomized_constraints(move |cs| {
    ///     let z = cs.challenge_scalar(b"some challenge");
    ///     // ...
    /// })
    /// ```
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}
