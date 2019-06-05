/// Represents an error during the proving or verifying of a constraint system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum R1CSError {
    /// Occurs when there are insufficient generators for the proof.
    InvalidGeneratorsLength,
    /// Occurs when verification of an
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    VerificationError,
    /// This error occurs when the proof encoding is malformed.
    FormatError,
    /// Occurs when trying to use a missing variable assignment.
    /// Used by gadgets that build the constraint system to signal that
    /// a variable assignment is not provided when the prover needs it.
    MissingAssignment,

    /// Occurs when a gadget receives an inconsistent input.
    GadgetError {
        /// The description of the reasons for the error.
        description: String,
    },
}
