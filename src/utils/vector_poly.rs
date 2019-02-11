use crate::types::BigNum;
use crate::utils::field_elements_inner_product;
use crate::utils::add_field_element_vectors;
use crate::utils::field_elements_multiplication;
use crate::utils::subtract_field_elements;
use crate::constants::CurveOrder;

type Scalar = BigNum;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<Scalar>, pub Vec<Scalar>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
pub struct VecPoly3(
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2(pub Scalar, pub Scalar, pub Scalar);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
pub struct Poly6 {
    pub t1: Scalar,
    pub t2: Scalar,
    pub t3: Scalar,
    pub t4: Scalar,
    pub t5: Scalar,
    pub t6: Scalar,
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![field_element_zero!(); n], vec![field_element_zero!(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1) -> Poly2 {
        // Uses Karatsuba's method
        // TODO: Remove unwraps
        let l = self;
        let r = rhs;

        let t0 = field_elements_inner_product(&l.0, &r.0).unwrap();
        let t2 = field_elements_inner_product(&l.1, &r.1).unwrap();

        let l0_plus_l1 = add_field_element_vectors(&l.0, &l.1).unwrap();
        let r0_plus_r1 = add_field_element_vectors(&r.0, &r.1).unwrap();

        let t1 = subtract_field_elements(&field_elements_inner_product(&l0_plus_l1, &r0_plus_r1).unwrap(),
                                         &add_field_elements!(&t0, &t2));

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![field_element_zero!(); n];
        for i in 0..n {
            out[i] = add_field_elements!(&self.0[i], &field_elements_multiplication(&self.1[i], &x));
        }
        out
    }
}

impl VecPoly3 {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![field_element_zero!(); n],
            vec![field_element_zero!(); n],
            vec![field_element_zero!(); n],
            vec![field_element_zero!(); n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6 {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.
        // TODO: Remove unwraps

        let t1 = field_elements_inner_product(&lhs.1, &rhs.0).unwrap();
        let t2 = add_field_elements!(&field_elements_inner_product(&lhs.1, &rhs.1).unwrap(), &field_elements_inner_product(&lhs.2, &rhs.0).unwrap());
        let t3 = add_field_elements!(&field_elements_inner_product(&lhs.2, &rhs.1).unwrap(), &field_elements_inner_product(&lhs.3, &rhs.0).unwrap());
        let t4 = add_field_elements!(&field_elements_inner_product(&lhs.1, &rhs.3).unwrap(), &field_elements_inner_product(&lhs.3, &rhs.1).unwrap());
        let t5 = field_elements_inner_product(&lhs.2, &rhs.3).unwrap();
        let t6 = field_elements_inner_product(&lhs.3, &rhs.3).unwrap();

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![field_element_zero!(); n];
        for i in 0..n {
            // out[i] += self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
            out[i] = add_field_elements!(
                &self.0[i],
                &field_elements_multiplication(
                    &x,
                    &add_field_elements!(
                        &self.1[i],
                        &field_elements_multiplication(
                            &x,
                            &add_field_elements!(
                                &self.2[i],
                                &field_elements_multiplication(&x, &self.3[i])
                            )
                        )
                    )
                )
            );
        }
        out
    }
}

impl Poly2 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        // self.0 + x * (self.1 + x * self.2)
        add_field_elements!(
            &self.0,
            &field_elements_multiplication(
                &x,
                &add_field_elements!(
                    &self.1,
                    &field_elements_multiplication(
                        &x,
                        &self.2
                    )
                )
            )
        )
    }
}

impl Poly6 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        // x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
        field_elements_multiplication(
             &x,
             &add_field_elements!(
                    &self.t1,
                    &field_elements_multiplication(
                        &x,
                        &add_field_elements!(
                            &self.t2,
                            &field_elements_multiplication(
                                &x,
                                &add_field_elements!(
                                    &self.t3,
                                    &field_elements_multiplication(
                                        &x,
                                        &add_field_elements!(
                                            &self.t4,
                                            &field_elements_multiplication(
                                                &x,
                                                &add_field_elements!(
                                                    &self.t5,
                                                    &field_elements_multiplication(&x, &self.t6)
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
        )
    }
}
