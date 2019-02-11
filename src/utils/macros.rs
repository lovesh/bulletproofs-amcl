#[macro_export]
macro_rules! add_group_elements {
    ( $( $elem:expr ),* ) => {
        {
            let mut sum = GroupG1::new();
            $(
                sum.add($elem);
            )*
            sum
        }
    };
}

#[macro_export]
macro_rules! add_field_elements {
    ( $( $elem:expr ),* ) => {
        {
            let mut sum = BigNum::new();
            $(
                sum.add($elem);
                sum.rmod(&CurveOrder);
            )*
            sum
        }
    };
}

#[macro_export]
macro_rules! field_element_zero {
    ( ) => {
        BigNum::new()
    };
}

#[macro_export]
macro_rules! field_element_one {
    ( ) => {
        BigNum::new_int(1)
    };
}

#[macro_export]
macro_rules! field_element_neg_one {
    ( ) => {
        {
            let o = BigNum::new_int(1);
            negate_field_element(&o)
        }
    };
}

#[macro_export]
macro_rules! random_scalar {
    ( ) => {
        random_field_element(None)
    };
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::types::{BigNum, GroupG1};
    use crate::utils::{random_field_element, are_field_elements_equal, scalar_point_multiplication};
    use crate::constants::{CurveOrder, GeneratorG1};

    #[test]
    fn test_field_elem_addition() {
        let a = random_field_element(None);
        let b = random_field_element(None);
        let c = random_field_element(None);

        let sum =  add_field_elements!(&a, &b, &c);

        let mut expected_sum = BigNum::new();
        expected_sum.add(&a);
        expected_sum.rmod(&CurveOrder);
        expected_sum.add(&b);
        expected_sum.rmod(&CurveOrder);
        expected_sum.add(&c);
        expected_sum.rmod(&CurveOrder);
        assert!(are_field_elements_equal(&sum, &expected_sum));
    }

    #[test]
    fn test_group_elem_addition() {
        let _a = random_field_element(None);
        let a = scalar_point_multiplication(&_a, &GeneratorG1);
        let _b = random_field_element(None);
        let b = scalar_point_multiplication(&_b, &GeneratorG1);
        let _c = random_field_element(None);
        let c = scalar_point_multiplication(&_c, &GeneratorG1);

        let mut sum =  add_group_elements!(&a, &b, &c);

        let mut expected_sum = GroupG1::new();
        expected_sum.inf();
        expected_sum.add(&a);
        expected_sum.add(&b);
        expected_sum.add(&c);
        assert!(sum.equals(&mut expected_sum));
    }
}