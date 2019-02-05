use crate::utils::negate_field_element;

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