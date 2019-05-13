use super::types::BigNum;

#[derive(Debug, Clone, Copy)]
pub enum ValueError {
    UnequalSizeVectors(usize, usize),
    IncorrectSize(usize),
    NonPowerOf2(usize),
    OutOfRange(usize),
    NegativeValue(BigNum)
}

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
    }
}

#[macro_export]
macro_rules! check_vector_size_for_equality {
    ( $a:expr, $b:expr ) => {
        {
            if $a.len() != $b.len() {
                Err(ValueError::UnequalSizeVectors($a.len(), $b.len()))
            } else {
                Ok(())
            }
        }
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_vector_size_equality() {
        let a1 = vec![1, 4, 6, 8];
        let a2 = vec![4, 5, 2, 1];
        assert!(check_vector_size_for_equality!(a1, a2).is_ok());

        let a3 = vec![1, 4, 6];
        assert!(check_vector_size_for_equality!(a3, a2).is_err());
    }
}
