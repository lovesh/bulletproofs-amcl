use super::types::BigNum;

#[derive(Debug, Clone, Copy)]
pub enum ValueError {
    UnequalSizeVectors(usize, usize),
    IncorrectSize(usize),
    NonPowerOf2(usize),
    OutOfRange(usize),
    NegativeValue(BigNum)
}

#[macro_export]
macro_rules! check_vector_size_for_equality {
    ( $a:ident, $b:ident ) => {
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
