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
