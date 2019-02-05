//! Definition of the proof struct.


use crate::types::GroupG1;
use crate::types::BigNum;
use crate::inner_product::InnerProductArgumentProof;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
///
/// Statements are specified by writing gadget functions which add
/// constraints to a [`ConstraintSystem`](::r1cs::ConstraintSystem)
/// implementation.  To construct an [`R1CSProof`], a prover constructs
/// a [`ProverCS`](::r1cs::ProverCS), then passes it to gadget
/// functions to build the constraint system, then consumes the
/// constraint system using
/// [`ProverCS::prove`](::r1cs::ProverCS::prove) to produce an
/// [`R1CSProof`].  To verify an [`R1CSProof`], a verifier constructs a
/// [`VerifierCS`](::r1cs::VerifierCS), then passes it to the same
/// gadget functions to (re)build the constraint system, then consumes
/// the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: GroupG1,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: GroupG1,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: GroupG1,
    /// Commitment to the values of input wires in the second phase.
    pub(super) A_I2: GroupG1,
    /// Commitment to the values of output wires in the second phase.
    pub(super) A_O2: GroupG1,
    /// Commitment to the blinding factors in the second phase.
    pub(super) S2: GroupG1,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: GroupG1,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: GroupG1,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: GroupG1,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: GroupG1,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: GroupG1,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: BigNum,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: BigNum,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: BigNum,
    /// Proof data for the inner-product argument.
    pub(super) ipp_proof: InnerProductArgumentProof,
}
