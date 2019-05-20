use rand::RngCore;
use rand::rngs::EntropyRng;

use crate::constants::{MODBYTES, CurveOrder, NLEN, BarrettRedc_k, BarrettRedc_u, BarrettRedc_v};
use crate::types::{BigNum, DoubleBigNum};
use amcl::sha3::{SHAKE256, SHA3};
use crate::utils::{get_seeded_RNG, hash_msg, barrett_reduction};
use crate::errors::ValueError;
use std::cmp::Ordering;
use std::ops::{Index, IndexMut, Add, AddAssign, Sub, SubAssign, Mul};
use std::fmt;
use core::fmt::Display;
use crate::utils::group_elem::GroupElement;
use std::slice::Iter;
use byteorder::BigEndian;


#[macro_export]
macro_rules! add_field_elems {
    ( $( $elem:expr ),* ) => {
        {
            let mut sum = FieldElement::new();
            $(
                sum += $elem;
            )*
            sum
        }
    };
}

#[derive(Copy, Clone, Debug)]
pub struct FieldElement {
    value: BigNum
}

impl fmt::Display for FieldElement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl FieldElement {
    /// Creates a new field element with value 0
    pub fn new() -> Self {
        Self {
            value: BigNum::new()
        }
    }

    pub fn zero() -> Self {
        Self {
            value: BigNum::new()
        }
    }

    pub fn one() -> Self {
        Self {
            value: BigNum::new_int(1)
        }
    }

    pub fn minus_one() -> Self {
        let mut o = Self::one();
        o.negate();
        o
    }

    /// Get a random field element of the curve order. Avoid 0.
    pub fn random(order: Option<&BigNum>) -> Self {
        Self::random_field_element(order).into()
    }

    pub fn is_zero(&self) -> bool {
        BigNum::iszilch(&self.value)
    }

    pub fn is_one(&self) -> bool {
        BigNum::isunity(&self.value)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut temp = BigNum::new_copy(&self.value);
        let mut bytes: [u8; MODBYTES] = [0; MODBYTES];
        temp.tobytes(&mut bytes);
        bytes.to_vec()
    }

    pub fn to_bignum(&self) -> BigNum {
        let mut v = self.value.clone();
        v.rmod(&CurveOrder);
        v
    }

    /// Hash message and return output as field element
    pub fn from_msg_hash(msg: &[u8]) -> Self {
        // TODO: Ensure result is not 0
        let h = &hash_msg(msg);
        h.into()

    }

    /// Add a field element to itself. `self = self + b`
    pub fn add_assign_(&mut self, b: &Self) {
        self.value.add(&b.value);
        self.value.rmod(&CurveOrder);
    }

    /// Subtract a field element from itself. `self = self - b`
    pub fn sub_assign_(&mut self, b: &Self) {
        let neg_b = BigNum::modneg(&b.value, &CurveOrder);
        self.value.add(&neg_b);
        self.value.rmod(&CurveOrder);
    }

    /// Return sum of a field element and itself. `self + b`
    pub fn plus(&self, b: &Self) -> Self {
        let mut sum = self.value.clone();
        sum.add(&b.value);
        sum.rmod(&CurveOrder);
        sum.into()
    }

    /// Return difference of a field element and itself. `self - b`
    pub fn minus(&self, b: &Self) -> Self {
        let mut sum = self.value.clone();
        let neg_b = BigNum::modneg(&b.value, &CurveOrder);
        sum.add(&neg_b);
        sum.rmod(&CurveOrder);
        sum.into()
    }

    /// Multiply 2 field elements modulus the order of the curve.
    /// (field_element_a * field_element_b) % curve_order
    pub fn multiply(&self, b: &Self) -> Self {
        //BigNum::modmul(&self.value, &b.value, &CurveOrder).into()
        let mut a = self.value.clone();
        a.rmod(&CurveOrder);
        let mut b = b.value.clone();
        b.rmod(&CurveOrder);
        let d = BigNum::mul(&a, &b);
        Self::reduce_dmod_curve_order(&d).into()
    }

    /// Calculate square of a field element modulo the curve order, i.e `a^2 % curve_order`
    pub fn square(&self) -> Self {
        //BigNum::modsqr(&self.value, &CurveOrder).into()
        let mut a = self.value.clone();
        a.rmod(&CurveOrder);
        let d = BigNum::sqr(&a);
        Self::reduce_dmod_curve_order(&d).into()
    }

    /// Return negative of field element
    pub fn negation(&self) -> Self {
        // TODO: Implement Neg operator
        let zero = Self::zero();
        zero.minus(&self)
    }

    pub fn negate(&mut self) {
        let zero = Self::zero();
        self.value = zero.minus(&self).value;
    }

    /// Calculate inverse of a field element modulo the curve order, i.e `a^-1 % curve_order`
    pub fn inverse(&self) -> Self {
        let mut inv = self.value.clone();
        inv.invmodp(&CurveOrder);
        inv.into()
    }

    pub fn inverse_mut(&mut self) {
        self.value.invmodp(&CurveOrder);
    }

    pub fn shift_right(&self, k: usize) -> Self {
        let mut t = self.value.clone();
        t.shr(k);
        t.into()
    }

    pub fn shift_left(&self, k: usize) -> Self {
        let mut t = self.value.clone();
        t.shl(k);
        t.into()
    }

    pub fn is_even(&self) -> bool {
        self.value.parity() == 0
    }

    pub fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Gives vectors of bit-vectors for the Big number. Each `Chunk` has a separate bit-vector,
    /// hence upto NLEN bit-vectors possible. NOT SIDE CHANNEL RESISTANT
    pub fn to_bitvectors(&self) -> Vec<Vec<u8>> {
        let mut k = NLEN - 1;
        let mut s = BigNum::new_copy(&self.value);
        s.norm();

        while (k as isize) >= 0 && s.w[k] == 0 {
            k = k.wrapping_sub(1)
        }
        if (k as isize) < 0 {
            return vec![];
        }

        let mut b_vec: Vec<Vec<u8>> = vec![vec![]; k+1];
        for i in 0..k+1 {
            let mut c = s.w[i];
            let mut c_vec: Vec<u8> = vec![];
            while c != 0 {
                c_vec.push((c % 2) as u8);
                c /= 2;
            }
            b_vec[i] = c_vec;
        }
        return b_vec;
    }

    fn random_field_element(order: Option<&BigNum>) -> BigNum {
        // initialise from at least 128 byte string of raw random entropy
        let entropy_size = 256;
        let mut r = get_seeded_RNG(entropy_size);
        let n = match order {
            Some(o) => BigNum::randomnum(&o, &mut r),
            None => BigNum::randomnum(&BigNum::new_big(&CurveOrder), &mut r)
        };
        if n.iszilch() { Self::random_field_element(order) } else { n }
    }

    pub fn to_wnaf(&self, w: usize) -> Vec<i8> {
        // required by the NAF definition
        debug_assert!( w >= 2 );
        // required so that the NAF digits fit in i8
        debug_assert!( w <= 8 );

        use byteorder::{ByteOrder, LittleEndian};

        let mut naf = vec![0i8; MODBYTES * 8];

        let mut x_u64 = vec![0u64; NLEN];
        let mut bytes = self.to_bytes();
        bytes.reverse();
        LittleEndian::read_u64_into(&bytes, &mut x_u64[0..NLEN-1]);

        let width = 1 << w;
        let window_mask = width - 1;

        let mut pos = 0;
        let mut carry = 0;
        while pos < naf.len() {
            // Construct a buffer of bits of the scalar, starting at bit `pos`
            let u64_idx = pos / 64;
            let bit_idx = pos % 64;
            let bit_buf: u64;
            if bit_idx < 64 - w {
                // This window's bits are contained in a single u64
                bit_buf = x_u64[u64_idx] >> bit_idx;
            } else {
                // Combine the current u64's bits with the bits from the next u64
                bit_buf = (x_u64[u64_idx] >> bit_idx) | (x_u64[1+u64_idx] << (64 - bit_idx));
            }

            // Add the carry into the current window
            let window = carry + (bit_buf & window_mask);

            if window & 1 == 0 {
                // If the window value is even, preserve the carry and continue.
                // Why is the carry preserved?
                // If carry == 0 and window & 1 == 0, then the next carry should be 0
                // If carry == 1 and window & 1 == 0, then bit_buf & 1 == 1 so the next carry should be 1
                pos += 1;
                continue;
            }

            if window < width/2 {
                carry = 0;
                naf[pos] = window as i8;
            } else {
                carry = 1;
                naf[pos] = (window as i8) - (width as i8);
            }

            pos += w;
        }

        naf
    }

    /// Takes a bunch of field elements and returns the inverse of all field elements.
    /// Also returns the product of all inverses as its computed as a side effect.
    /// For an input of n elements, rather than doing n inversions, does only 1 inversion but 3n multiplications.
    /// eg `batch_invert([a, b, c, d])` returns ([1/a, 1/b, 1/c, 1/d], 1/a * 1/b * 1/c * 1/d)
    /// Algorithm taken from Guide to Elliptic Curve Cryptography book, "Algorithm 2.26 Simultaneous inversion"
    pub fn batch_invert(elems: &[Self]) -> (Vec<Self>, Self) {
        // TODO: Currently inversion seems to happen faster than multiplication as one of the test below shows.
        // This might be due to the fact that the current field element multiplication algorithm is constant time.
        // Check and add a faster multiplication algorithm if needed.

        debug_assert!( elems.len() > 0 );

        let k = elems.len();

        // TODO: Multiplications below can be sped up by using montgomery multiplication.

        // Construct c as [elems[0], elems[0]*elems[1], elems[0]*elems[1]*elems[2], .... elems[0]*elems[1]*elems[2]*...elems[k-1]]
        let mut c: Vec<Self> = vec![elems[0].clone()];
        for i in 1..k {
            c.push(c[i-1] * elems[i])
        }

        // u = 1 / elems[0]*elems[1]*elems[2]*...elems[k-1]
        let all_inv = c[k-1].inverse();
        let mut u = all_inv;
        let mut inverses = vec![FieldElement::one(); k];

        for i in (1..k).rev() {
            inverses[i] = u * c[i-1];
            u = u * elems[i];
        }

        inverses[0] = u;

        (inverses, all_inv)
    }

    /// Useful for reducing product of BigNums. Uses Barrett reduction
    pub fn reduce_dmod_curve_order(x: &DoubleBigNum) -> BigNum {
        let (k, u, v) = (*BarrettRedc_k, *BarrettRedc_u, *BarrettRedc_v);
        barrett_reduction(&x, &CurveOrder, k, &u, &v)
    }
}

impl From<u8> for FieldElement {
    fn from(x: u8) -> Self {
        Self {
            value: BigNum::new_int(x as isize)
        }
    }
}

impl From<u32> for FieldElement {
    fn from(x: u32) -> Self {
        Self {
            value: BigNum::new_int(x as isize)
        }
    }
}

impl From<u64> for FieldElement {
    fn from(x: u64) -> Self {
        Self {
            value: BigNum::new_int(x as isize)
        }
    }
}

impl From<i32> for FieldElement {
    fn from(x: i32) -> Self {
        Self {
            value: BigNum::new_int(x as isize)
        }
    }
}

impl From<BigNum> for FieldElement {
    fn from(x: BigNum) -> Self {
        Self {
            value: x
        }
    }
}

impl From<&[u8; MODBYTES]> for FieldElement {
    fn from(x: &[u8; MODBYTES]) -> Self {
        let mut n = BigNum::frombytes(x);
        n.rmod(&CurveOrder);
        Self {
            value: n
        }
    }
}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> bool {
        BigNum::comp(&self.value, &other.value) == 0
    }
}

impl PartialOrd for FieldElement {
    fn partial_cmp(&self, other: &FieldElement) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FieldElement {
    fn cmp(&self, other: &FieldElement) -> Ordering {
        match BigNum::comp(&self.value, &other.value) {
            0 => Ordering::Equal,
            -1 => Ordering::Less,
            _ => Ordering::Greater
        }
    }
}

impl Eq for FieldElement {}

impl Add for FieldElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.plus(&other)
    }
}

impl Add<FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn add(self, other: FieldElement) -> FieldElement {
        self.plus(&other)
    }
}

impl<'a> Add<&'a FieldElement> for FieldElement {
    type Output = Self;
    fn add(self, other: &'a FieldElement) -> Self {
        self.plus(other)
    }
}

impl<'a> Add<&'a FieldElement> for &FieldElement {
    type Output = FieldElement;
    fn add(self, other: &'a FieldElement) -> FieldElement {
        self.plus(other)
    }
}

impl AddAssign for FieldElement {
    fn add_assign(&mut self, other: Self) {
        self.add_assign_(&other)
    }
}

impl Sub for FieldElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self.minus(&other)
    }
}

impl Sub<FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn sub(self, other: FieldElement) -> FieldElement {
        self.minus(&other)
    }
}

impl<'a> Sub<&'a FieldElement> for FieldElement {
    type Output = Self;

    fn sub(self, other: &'a FieldElement) -> Self {
        self.minus(&other)
    }
}

impl<'a> Sub<&'a FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn sub(self, other: &'a FieldElement) -> FieldElement {
        self.minus(&other)
    }
}

impl SubAssign for FieldElement {
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign_(&other)
    }
}

impl Mul for FieldElement {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.multiply(&other)
    }
}

impl Mul<FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn mul(self, other: FieldElement) -> FieldElement {
        self.multiply(&other)
    }
}

impl<'a> Mul<&'a FieldElement> for FieldElement {
    type Output = FieldElement;

    fn mul(self, other: &'a FieldElement) -> FieldElement {
        self.multiply(other)
    }
}

impl<'a> Mul<&'a FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn mul(self, other: &'a FieldElement) -> FieldElement {
        self.multiply(other)
    }
}

impl Mul<GroupElement> for FieldElement {
    type Output = GroupElement;

    fn mul(self, other: GroupElement) -> GroupElement {
        other.scalar_mul_const_time(&self)
    }
}

impl Mul<&GroupElement> for FieldElement {
    type Output = GroupElement;

    fn mul(self, other: &GroupElement) -> GroupElement {
        other.scalar_mul_const_time(&self)
    }
}

impl Mul<GroupElement> for &FieldElement {
    type Output = GroupElement;

    fn mul(self, other: GroupElement) -> GroupElement {
        other.scalar_mul_const_time(self)
    }
}

impl Mul<&GroupElement> for &FieldElement {
    type Output = GroupElement;

    fn mul(self, other: &GroupElement) -> GroupElement {
        other.scalar_mul_const_time(self)
    }
}

#[derive(Clone, Debug)]
pub struct FieldElementVector {
    elems: Vec<FieldElement>
}

impl FieldElementVector {
    /// Creates a new field element vector with each element being 0
    pub fn new(size: usize) -> Self {
        Self {
            elems: (0..size).map(|_| FieldElement::new()).collect()
        }
    }

    /// Generate a Vandermonde vector of field elements as:
    /// FieldElementVector::new_vandermonde_vector(k, n) => vec![1, k, k^2, k^3, ... k^n-1]
    /// FieldElementVector::new_vandermonde_vector(0, n) => vec![0, 0, ... n times]
    pub fn new_vandermonde_vector(elem: &FieldElement, size: usize) -> Self {
        if elem.is_zero() {
            Self::new(size)
        } else if elem.is_one() {
            vec![FieldElement::one(); size].into()
        } else {
            let mut v = Vec::<FieldElement>::with_capacity(size);
            v.push(FieldElement::one());
            let mut current = elem.clone();
            for _ in 1..size {
                v.push(current.clone());
                current = current.multiply(elem);
            }
            v.into()
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            elems: Vec::<FieldElement>::with_capacity(capacity)
        }
    }

    /// Get a vector of random field elements
    pub fn random(size: usize, order: Option<&BigNum>) -> Self {
        (0..size).map( | _ | FieldElement::random(order)).collect::<Vec<FieldElement>>().into()
    }

    pub fn as_slice(&self) -> &[FieldElement] {
        &self.elems
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }

    pub fn push(&mut self, value: FieldElement) {
        self.elems.push(value)
    }

    pub fn append(&mut self, other: &mut Self) {
        self.elems.append(&mut other.elems)
    }

    /// Multiply each field element of the vector with another given field
    /// element `n` (scale the vector)
    pub fn scale(&mut self, n: &FieldElement) {
        for i in 0..self.len() {
            self[i] = self[i].multiply(n);
        }
    }

    pub fn scaled_by(&self, n: &FieldElement) -> Self {
        let mut scaled = Vec::<FieldElement>::with_capacity(self.len());
        for i in 0..self.len() {
            scaled.push(self[i].multiply(n))
        }
        scaled.into()
    }

    /// Add 2 vectors of field elements
    pub fn plus(&self, b: &FieldElementVector) ->  Result<FieldElementVector, ValueError> {
        check_vector_size_for_equality!(self, b)?;
        let mut sum_vector = FieldElementVector::with_capacity(self.len());
        for i in 0..self.len() {
            sum_vector.push(self[i] + b.elems[i])
        }
        Ok(sum_vector)
    }

    /// Subtract 2 vectors of field elements
    pub fn minus(&self, b: &FieldElementVector) ->  Result<FieldElementVector, ValueError> {
        check_vector_size_for_equality!(self, b)?;
        let mut diff_vector = FieldElementVector::with_capacity(self.len());
        for i in 0..self.len() {
            diff_vector.push(self[i] - b[i])
        }
        Ok(diff_vector)
    }

    /// Compute sum of all elements of a vector
    pub fn sum(&self) -> FieldElement {
        let mut accum = FieldElement::new();
        for i in 0..self.len() {
            accum += self[i];
        }
        accum
    }

    /// Computes inner product of 2 vectors of field elements
    /// [a1, a2, a3, ...field elements].[b1, b2, b3, ...field elements] = (a1*b1 + a2*b2 + a3*b3) % curve_order
    pub fn inner_product(&self, b: &FieldElementVector) -> Result<FieldElement, ValueError> {
        check_vector_size_for_equality!(self, b)?;
        let mut accum = FieldElement::new();
        for i in 0..self.len() {
            accum += self[i] * b[i];

        }
        Ok(accum)
    }

    /// Calculates Hadamard product of 2 field element vectors.
    /// Hadamard product of `a` and `b` = `a` o `b` = (a0 o b0, a1 o b1, ...).
    /// Here `o` denotes multiply operation
    pub fn hadamard_product(&self, b: &FieldElementVector) -> Result<FieldElementVector, ValueError> {
        check_vector_size_for_equality!(self, b)?;
        let mut hadamard_product = FieldElementVector::with_capacity(self.len());
        for i in 0..self.len() {
            hadamard_product.push(self[i] * b[i]);
        }
        Ok(hadamard_product)
    }

    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        let (l, r) = self.as_slice().split_at(mid);
        (Self::from(l), Self::from(r))
    }

    pub fn iter(&self) -> Iter<FieldElement> {
        self.as_slice().iter()
    }
}

impl From<Vec<FieldElement>> for FieldElementVector {
    fn from(x: Vec<FieldElement>) -> Self {
        Self {
            elems: x
        }
    }
}

impl From<&[FieldElement]> for FieldElementVector {
    fn from(x: &[FieldElement]) -> Self {
        Self {
            elems: x.to_vec()
        }
    }
}

impl Index<usize> for FieldElementVector {
    type Output = FieldElement;

    fn index(&self, idx: usize) -> &FieldElement {
        &self.elems[idx]
    }
}

impl IndexMut<usize> for FieldElementVector {

    fn index_mut(&mut self, idx: usize) -> &mut FieldElement {
        &mut self.elems[idx]
    }
}

impl PartialEq for FieldElementVector {
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

impl IntoIterator for FieldElementVector {
    type Item = FieldElement;
    type IntoIter = ::std::vec::IntoIter<FieldElement>;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.into_iter()
    }
}

// TODO: Implement add/sub/mul ops but need some way to handle error when vectors are of different length


pub fn multiply_row_vector_with_matrix(vector: &FieldElementVector, matrix: &Vec<FieldElementVector>) -> Result<FieldElementVector, ValueError> {
    check_vector_size_for_equality!(vector, matrix)?;
    let out_len = matrix[0].len();
    let mut out = FieldElementVector::new(out_len);
    for i in 0..out_len {
        for j in 0..vector.len() {
            out[i] += vector[j] * matrix[j][i];
        }
    }
    Ok(out)
}

#[cfg(test)]
mod test {
    use super::*;
    use std::time::{Duration, Instant};
    use amcl::bls381::big::BIG;

    #[test]
    fn test_field_elem_multiplication() {
        let a: FieldElement = 5u8.into();
        let b: FieldElement = 18u8.into();
        let c: FieldElement = 90u8.into();
        assert_eq!(a.multiply(&b), c);
        assert_eq!(a * b, c);
    }

    #[test]
    fn test_field_elements_inner_product() {
        let a: FieldElementVector = vec![FieldElement::from(5), FieldElement::one(), FieldElement::from(100), FieldElement::zero()].into();
        let b: FieldElementVector = vec![FieldElement::from(18), FieldElement::one(), FieldElement::from(200), FieldElement::zero()].into();
        let c = FieldElement::from((90 + 1 + 200 * 100) as u32);
        assert_eq!(a.inner_product(&b).unwrap(), c);
    }

    #[test]
    fn test_field_elements_hadamard_product() {
        let a: FieldElementVector = vec![FieldElement::from(5), FieldElement::one(), FieldElement::from(100), FieldElement::zero()].into();
        let b: FieldElementVector = vec![FieldElement::from(18), FieldElement::one(), FieldElement::from(200), FieldElement::zero()].into();
        let h: FieldElementVector = vec![FieldElement::from(90), FieldElement::one(), FieldElement::from(200 * 100), FieldElement::zero()].into();
        let c = FieldElement::from((90 + 1 + 200 * 100) as u32);
        assert_eq!(a.hadamard_product(&b).unwrap(), h);
        assert_eq!(h.sum(), c);
    }

    #[test]
    fn test_scale_field_element_vector() {
        let a: FieldElementVector = vec![FieldElement::from(5), FieldElement::from(1), FieldElement::from(100), FieldElement::from(0)].into();
        let n = FieldElement::from(3);
        let na = a.scaled_by(&n);
        assert_eq!(na[0], FieldElement::from(5 * 3));
        assert_eq!(na[1], FieldElement::from(1 * 3));
        assert_eq!(na[2], FieldElement::from(100 * 3));
        assert_eq!(na[3], FieldElement::from(0));
    }

    #[test]
    fn test_add_field_element_vectors() {
        let a: FieldElementVector = vec![FieldElement::from(5), FieldElement::one(), FieldElement::from(100), FieldElement::zero()].into();
        let b: FieldElementVector = vec![FieldElement::from(18), FieldElement::one(), FieldElement::from(200), FieldElement::zero()].into();
        let c = a.plus(&b).unwrap();
        assert_eq!(c[0], FieldElement::from(5 + 18));
        assert_eq!(c[1], FieldElement::from(1 + 1));
        assert_eq!(c[2], FieldElement::from(100 + 200));
        assert_eq!(c[3], FieldElement::from(0));
    }

    #[test]
    fn test_field_elem_vandermonde_vector() {
        let zero_vec = FieldElementVector::new_vandermonde_vector(&FieldElement::zero(), 5);
        for i in 0..5 {
            assert!(zero_vec[i].is_zero())
        }

        let unit_vec = FieldElementVector::new_vandermonde_vector(&FieldElement::one(), 5);
        for i in 0..4 {
            assert!(unit_vec[i].is_one())
        }

        let two_vec = FieldElementVector::new_vandermonde_vector(&FieldElement::from(2u8), 10);
        let base = 2u32;
        for i in 0..10 {
            assert_eq!(two_vec[i], FieldElement::from(base.pow(i as u32) as u32));
        }
    }

    #[test]
    fn test_to_bitvectors() {
        let n = FieldElement::from(100u32);
        assert_eq!(n.to_bitvectors(), vec![vec![0, 0, 1, 0, 0, 1, 1]]);
        let mut c = vec![0i64; NLEN];
        c[0] = 2;
        c[1] = 100;
        let m: FieldElement = BigNum::new_ints(&c).into();
        assert_eq!(m.to_bitvectors(), vec![vec![0, 1], vec![0, 0, 1, 0, 0, 1, 1]]);
    }

    #[test]
    fn test_negating_field_elems() {
        let a = FieldElement::from(100u32);
        let neg_a = a.negation();
        assert_ne!(a, neg_a);
        let neg_neg_a = neg_a.negation();
        assert_eq!(a, neg_neg_a);
    }

    #[test]
    fn test_field_elem_addition() {
        let a = FieldElement::random(None);
        let b = FieldElement::random(None);
        let c = FieldElement::random(None);

        let sum =  a + b + c;

        let mut expected_sum = FieldElement::new();
        expected_sum = expected_sum.plus(&a);
        expected_sum = expected_sum.plus(&b);
        expected_sum += c;
        assert_eq!(sum, expected_sum);
    }

    #[test]
    fn test_field_elem_subtraction() {
        let a = FieldElement::random(None);
        let b = FieldElement::random(None);
        let c = FieldElement::random(None);

        let sum =  a - b - c;

        let mut expected_sum = FieldElement::new();
        expected_sum = expected_sum.plus(&a);
        expected_sum = expected_sum - b;
        expected_sum -= c;
        assert_eq!(sum, expected_sum);
    }

    #[test]
    fn test_static_field_elems() {
        let zero = FieldElement::zero();
        let one = FieldElement::one();
        let minus_one = FieldElement::minus_one();
        assert_eq!(one + minus_one, zero);
    }

    #[test]
    fn timing_multiplication_inversion() {
        // Timing multiplication and inversion
        let count = 100;
        let elems: Vec<_> = (0..count).map(|_| FieldElement::random(None)).collect();

        let mut res_mul = FieldElement::one();
        let mut start = Instant::now();
        for e in &elems {
            res_mul = res_mul * e;
        }
        println!("Multiplication time for {} elems = {:?}", count, start.elapsed());

        start = Instant::now();
        let mut inverses = vec![];
        for e in &elems {
            inverses.push(e.inverse());
        }
        println!("Inverse time for {} elems = {:?}", count, start.elapsed());

        start = Instant::now();
        let (inverses_1, all_inv) = FieldElement::batch_invert(&elems);
        println!("Batch inverse time for {} elems = {:?}", count, start.elapsed());

        let mut expected_inv_product = FieldElement::one();
        for i in 0..count {
            assert_eq!(inverses[i], inverses_1[i]);
            expected_inv_product = expected_inv_product * inverses[i];
        }

        assert_eq!(expected_inv_product, all_inv);
    }

    #[test]
    fn timing_field_elem_addition() {
        let count = 100;
        let points: Vec<FieldElement> = (0..100).map(|_| FieldElement::random(None)).collect();
        let mut R = FieldElement::random(None);
        let mut start = Instant::now();
        for i in 0..count {
            R = R + points[i];
        }
        println!("Addition time for {} elems = {:?}", count, start.elapsed());
    }
}