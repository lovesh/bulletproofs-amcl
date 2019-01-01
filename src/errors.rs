#[derive(Debug, Clone, Copy)]
pub enum ValueError {
    UnequalSizeVectors(usize, usize),
    IncorrectSize(usize),
    NonPowerOf2(usize)
}

/*macro_rules! check_vector_size_for_equality {
    ( $a:ident, $b:ident ) => {
        {
            if $a.len() != $b.len() {
            return Err(ValueError::UnequalSizeVectors($a.len(), $b.len()))
            }
            Ok(())
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
        check_vector_size_for_equality!(a1, a2);
    }
}*/
