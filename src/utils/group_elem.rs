use crate::amcl::rand::RAND;
use crate::constants::{MODBYTES, CurveOrder, GeneratorG1, GroupG1_SIZE, NLEN, FieldElementZero};
use crate::types::{BigNum, GroupG1};
use amcl::sha3::{SHAKE256, SHA3};
use crate::utils::{get_seeded_RNG, hash_msg};
use crate::errors::ValueError;
use std::cmp::Ordering;
use std::ops::{Index, IndexMut, Add, AddAssign, Sub};
use crate::utils::field_elem::{FieldElement, FieldElementVector};
use std::fmt;


#[macro_export]
macro_rules! add_group_elems {
    ( $( $elem:expr ),* ) => {
        {
            let mut sum = GroupElement::new();
            $(
                sum += $elem;
            )*
            sum
        }
    };
}

#[derive(Copy, Clone, Debug)]
pub struct GroupElement {
    value: GroupG1
}

impl fmt::Display for GroupElement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut c = self.value.clone();
        write!(f, "{}", c.tostring())
    }
}

impl GroupElement {
    pub fn new() -> Self {
        Self {
            value: GroupG1::new()
        }
    }

    pub fn infinity() -> Self {
        let mut v = GroupG1::new();
        v.inf();
        Self {
            value: v
        }
    }

    pub fn generator() -> Self {
        GroupG1::generator().into()
    }

    pub fn random(order: Option<&BigNum>) -> Self {
        let n = FieldElement::random(order);
        Self::generator().scalar_multiplication(&n)
    }

    pub fn is_infinity(&self) -> bool {
        self.value.is_infinity()
    }

    pub fn set_to_infinity(&mut self) {
        self.value.inf()
    }

    /// Hash message and return output as group element
    pub fn from_msg_hash(msg: &[u8]) -> GroupElement {
        GroupG1::mapit(&hash_msg(msg)).into()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut temp = GroupG1::new();
        temp.copy(&self.value);
        let mut bytes: [u8; GroupG1_SIZE] = [0; GroupG1_SIZE];
        temp.tobytes(&mut bytes, false);
        bytes.to_vec()
    }

    /// Add a group element to itself. `self = self + b`
    pub fn add_assign_(&mut self, b: &Self) {
        self.value.add(&b.value);
    }

    /// Subtract a group element from itself. `self = self - b`
    pub fn sub_assign_(&mut self, b: &Self) {
        self.value.sub(&b.value);
    }

    /// Return sum of a group element and itself. `self + b`
    pub fn plus(&self, b: &Self) -> Self {
        let mut sum = self.value.clone();
        sum.add(&b.value);
        sum.into()
    }

    /// Return difference of a group element and itself. `self - b`
    pub fn minus(&self, b: &Self) -> Self {
        let mut diff = self.value.clone();
        diff.sub(&b.value);
        diff.into()
    }

    /// Multiply point on the curve (element of group G1) with a scalar.
    /// field_element_a * group_element_b
    pub fn scalar_multiplication(&self, a: &FieldElement) -> Self {
        self.value.mul(a.as_bignum()).into()
    }
}

impl From<GroupG1> for GroupElement {
    fn from(x: GroupG1) -> Self {
        Self {
            value: x
        }
    }
}

impl From<&GroupG1> for GroupElement {
    fn from(x: &GroupG1) -> Self {
        Self {
            value: x.clone()
        }
    }
}

impl PartialEq for GroupElement {
    fn eq(&self, other: &GroupElement) -> bool {
        let mut l = self.clone();
        let mut r = other.clone();
        l.value.equals(&mut r.value)
    }
}

impl Add for GroupElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.plus(&other)
    }
}

impl Add<GroupElement> for &GroupElement {
    type Output = GroupElement;

    fn add(self, other: GroupElement) -> GroupElement {
        self.plus(&other)
    }
}

impl<'a> Add<&'a GroupElement> for GroupElement {
    type Output = Self;
    fn add(self, other: &'a GroupElement) -> Self {
        self.plus(other)
    }
}

impl AddAssign for GroupElement {
    fn add_assign(&mut self, other: Self) {
        self.add_assign_(&other)
    }
}

impl Sub for GroupElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self.minus(&other)
    }
}

#[derive(Clone, Debug)]
pub struct GroupElementVector {
    elems: Vec<GroupElement>
}

impl GroupElementVector {
    pub fn new(size: usize) -> Self {
        Self {
            elems: (0..size).map(|_| GroupElement::new()).collect()
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            elems: Vec::<GroupElement>::with_capacity(capacity)
        }
    }

    pub fn as_slice(&self) -> &[GroupElement] {
        &self.elems
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }

    pub fn push(&mut self, value: GroupElement) {
        self.elems.push(value)
    }

    /// Compute sum of all elements of a vector
    pub fn sum(&self) -> GroupElement {
        let mut accum = GroupElement::new();
        for i in 0..self.len() {
            accum += self[i];
        }
        accum
    }

    /// Multiply each field element of the vector with another given field
    /// element `n` (scale the vector)
    pub fn scale(&mut self, n: &FieldElement) {
        for i in 0..self.len() {
            self[i] = self[i].scalar_multiplication(n);
        }
    }

    pub fn scaled_by(&self, n: &FieldElement) -> Self {
        let mut scaled = Self::with_capacity(self.len());
        for i in 0..self.len() {
            scaled.push(self[i].scalar_multiplication(n))
        }
        scaled.into()
    }

    /// Computes inner product of 2 vectors, one of field elements and other of group elements.
    /// [a1, a2, a3, ...field elements].[b1, b2, b3, ...group elements] = (a1*b1 + a2*b2 + a3*b3)
    pub fn inner_product(&self, b: &FieldElementVector) -> Result<GroupElement, ValueError> {
        // TODO: Use a faster multi-scalar multiplication algorithm
        check_vector_size_for_equality!(self, b)?;
        let mut accum = GroupElement::new();
        for i in 0..self.len() {
            accum += self[i].scalar_multiplication(&b[i]);
        }
        Ok(accum)
    }

    /// Calculates Hadamard product of 2 group element vectors.
    /// Hadamard product of `a` and `b` = `a` o `b` = (a0 o b0, a1 o b1, ...).
    /// Here `o` denotes group operation, which in elliptic curve is point addition
    pub fn hadamard_product(&self, b: &Self) -> Result<Self, ValueError> {
        check_vector_size_for_equality!(self, b)?;
        let mut hadamard_product = Self::with_capacity(self.len());
        for i in 0..self.len() {
            hadamard_product.push(self[i].plus(&b[i]));
        }
        Ok(hadamard_product)
    }

    pub fn multi_scalar_multiplication(&self, field_elems: &FieldElementVector) -> Result<GroupElement, ValueError> {
        // TODO Add optimized implementation
        check_vector_size_for_equality!(field_elems, self)?;
        let mut accum = GroupElement::new();
        for i in 0..self.len() {
            accum += self[i].scalar_multiplication(&field_elems[i]);
        }
        Ok(accum)
    }

    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        let (l, r) = self.as_slice().split_at(mid);
        (Self::from(l), Self::from(r))
    }
}

impl From<Vec<GroupElement>> for GroupElementVector {
    fn from(x: Vec<GroupElement>) -> Self {
        Self {
            elems: x
        }
    }
}

impl From<&[GroupElement]> for GroupElementVector {
    fn from(x: &[GroupElement]) -> Self {
        Self {
            elems: x.to_vec()
        }
    }
}

impl Index<usize> for GroupElementVector {
    type Output = GroupElement;

    fn index(&self, idx: usize) -> &GroupElement {
        &self.elems[idx]
    }
}

impl IndexMut<usize> for GroupElementVector {

    fn index_mut(&mut self, idx: usize) -> &mut GroupElement {
        &mut self.elems[idx]
    }
}

impl PartialEq for GroupElementVector {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false
        }
        for i in 0..self.len() {
            if self[i] != other[i] {
                return false
            }
        }
        true
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_multi_scalar_multiplication() {
        let mut fs = vec![];
        let mut gs = vec![];
        let gen: GroupElement = GroupElement::generator();

        for i in 0..5 {
            fs.push(FieldElement::random(None));
            gs.push(gen.scalar_multiplication(&fs[i]));
        }
        let mut res = GroupElementVector::from(gs.as_slice()).multi_scalar_multiplication(
            &FieldElementVector::from(fs.as_slice())).unwrap();

        let mut expected = GroupElement::new();
        for i in 0..fs.len() {
            expected.add_assign_(&gs[i].scalar_multiplication(&fs[i]));
        }

        assert_eq!(expected, res)
    }

    #[test]
    fn test_group_elem_addition() {
        let a = GroupElement::random(None);
        let b = GroupElement::random(None);
        let c = GroupElement::random(None);

        let mut sum =  a + b + c;

        let mut expected_sum = GroupElement::new();
        expected_sum = expected_sum.plus(&a);
        expected_sum = expected_sum.plus(&b);
        expected_sum = expected_sum.plus(&c);
        assert_eq!(sum, expected_sum);
    }
}
