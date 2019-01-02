extern crate rand;
extern crate amcl;

use rand::RngCore;
use rand::rngs::EntropyRng;

use self::amcl::rand::{RAND};
use self::amcl::arch::Chunk;
use super::constants::{MODBYTES, CurveOrder, GeneratorG1, GroupG1_SIZE};
use super::types::{BigNum, GroupG1};
use self::amcl::bls381::mpin::{SHA384, hash_id};
use super::errors::ValueError;


pub fn get_seeded_RNG(entropy_size: usize, rng: Option<EntropyRng>) -> RAND {
    // initialise from at least 128 byte string of raw random entropy
    let mut entropy = vec![0; entropy_size];
    match rng {
        Some(mut rng) =>  rng.fill_bytes(&mut entropy.as_mut_slice()),
        None => {
            let mut rng = EntropyRng::new();
            rng.fill_bytes(&mut entropy.as_mut_slice());
        }
    }
    let mut r = RAND::new();
    r.clean();
    r.seed(entropy_size, &entropy);
    r
}

pub fn random_big_number(order: &[Chunk], rng: Option<EntropyRng>) -> BigNum {
    // initialise from at least 128 byte string of raw random entropy
    let entropy_size = 256;
    let mut r = get_seeded_RNG(entropy_size, rng);
    BigNum::randomnum(&BigNum::new_ints(&order), &mut r)
}

pub fn hash_on_GroupG1(msg: &[u8]) -> GroupG1 {
    let mut h: [u8; MODBYTES] = [0; MODBYTES];
    hash_id(SHA384, msg, &mut h);
    GroupG1::mapit(&h)
}

pub fn hash_as_BigNum(msg: &[u8]) -> BigNum {
    let mut h: [u8; MODBYTES] = [0; MODBYTES];
    hash_id(SHA384, msg, &mut h);
    BigNum::frombytes(&h)
}

pub fn get_bytes_for_G1_point(point: &GroupG1) -> Vec<u8> {
    let mut temp = GroupG1::new();
    temp.copy(point);
    let mut bytes: [u8; GroupG1_SIZE] = [0; GroupG1_SIZE];
    temp.tobytes(&mut bytes, false);
    bytes.to_vec()
}

// Multiply 2 field elements modulus the order of the curve.
// field_element_a * field_element_b % curve_order
pub fn field_elements_multiplication(a: &BigNum, b: &BigNum) -> BigNum {
    BigNum::modmul(a, b, &CurveOrder)
}

// Calculate inverse of a field element modulo the curve order, i.e `a^-1 % curve_order`
pub fn field_element_inverse(a: &BigNum) -> BigNum {
    let mut inv = a.clone();
    inv.invmodp(&CurveOrder);
    inv
}

// Calculate square of a field element modulo the curve order, i.e `a^2 % curve_order`
pub fn field_element_square(a: &BigNum) -> BigNum {
    BigNum::modsqr(a, &CurveOrder)
}

// Multiply point on the curve (element of group G1) with a scalar.
// field_element_a * group_element_b
pub fn scalar_point_multiplication(a: &BigNum, b: &GroupG1) -> GroupG1 {
    b.mul(a)
}

// Computes inner product of 2 vectors of field elements
// [a1, a2, a3, ...field elements].[b1, b2, b3, ...field elements] = (a1*b1 + a2*b2 + a3*b3) % curve_order
pub fn field_elements_inner_product(a: &[BigNum], b: &[BigNum]) -> Result<BigNum, ValueError> {
    if a.len() != b.len() {
        return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
    }
    let mut accum = BigNum::new();
    for i in 0..a.len() {
        // Question: What if the next line overflows?
        accum.add(&field_elements_multiplication(&a[i], &b[i]));
        // The modulo can be avoided if result of addition of above is greater than operands. Should benchmark
        accum.rmod(&CurveOrder)
    }
    Ok(accum)
}

// Computes inner product of 2 vectors, one of field elements and other of group elements.
// [a1, a2, a3, ...field elements].[b1, b2, b3, ...group elements] = (a1*b1 + a2*b2 + a3*b3)
pub fn scalar_point_inner_product(a: &[BigNum], b: &[GroupG1]) -> Result<GroupG1, ValueError> {
    if a.len() != b.len() {
        return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
    }
    let mut accum = GroupG1::new();
    for i in 0..a.len() {
        accum.add(&scalar_point_multiplication(&a[i], &b[i]))
    }
    Ok(accum)
}

// Multiply each field element of the given vector `v` with another given field
// element `n` (scale the vector `v`)
pub fn scale_field_element_vector(n: &BigNum, v: &[BigNum]) -> Vec<BigNum> {
    let mut scaled: Vec<BigNum> = Vec::with_capacity(v.len());
    for i in 0..v.len() {
        scaled.push(field_elements_multiplication(n, &v[i]))
    }
    scaled
}

// Add 2 vectors of field elements
pub fn add_field_element_vectors(a: &[BigNum], b: &[BigNum]) ->  Result<Vec<BigNum>, ValueError> {
    if a.len() != b.len() {
        return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
    }
    let mut sum_vector: Vec<BigNum> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let mut sum = BigNum::new();
        sum.add(&a[i]);
        sum.add(&b[i]);
        sum.rmod(&CurveOrder);
        sum_vector.push(sum)
    }
    Ok(sum_vector)
}

// Multiply each group element of the given vector `v` with the given field
// element `n` (scale the vector `v`)
pub fn scale_group_element_vector(n: &BigNum, v: &[GroupG1]) -> Vec<GroupG1> {
    let mut scaled: Vec<GroupG1> = Vec::with_capacity(v.len());
    for i in 0..v.len() {
        scaled.push(scalar_point_multiplication(n, &v[i]))
    }
    scaled
}

// Calculates Hadamard product of 2 group element vectors.
// Hadamard product of `a` and `b` = `a` o `b` = (a0 o b0, a1 o b1, ...).
// Here `o` denotes group operation, which in elliptic curve is point addition
pub fn group_elements_hadamard_product(a: &[GroupG1], b: &[GroupG1]) -> Result<Vec<GroupG1>, ValueError> {
    if a.len() != b.len() {
        return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
    }
    let mut hadamard_product: Vec<GroupG1> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let mut sum = GroupG1::new();
        sum.add(&a[i]);
        sum.add(&b[i]);
        hadamard_product.push(sum)
    }
    Ok(hadamard_product)
}

// Compare 2 field elements for equality
pub fn are_field_elements_equal(a: &BigNum, b: &BigNum) -> bool {
    BigNum::comp(a, b) == 0
}

// Generate a vector of field elements.
// field_elem_vector!(k, n) => vec![1, k, k^2, k^3, ... k^n-1]
// field_elem_vector!(0, n) => vec![0, 0, ... n times]
macro_rules! field_elem_vector {
    ( $elem:expr, $size:expr ) => {
        {
            if $elem == 0 {
                vec![BigNum::new(); $size]
            } else if $elem == 1 {
                vec![BigNum::new_int(1); $size]
            } else {
                let mut v: Vec<BigNum> = vec![];
                v.push(BigNum::new_int(1));
                let k = BigNum::new_int($elem);
                let mut current = BigNum::new_int($elem);
                for i in 1..$size {
                    v.push(current.clone());
                    current = field_elements_multiplication(&current, &k)
                }
                v
            }
        }
    };
}

// TODO: Add macro to add any number of
// 1. field elements
// 2. group elements

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_field_elem_multiplication() {
        let a = BigNum::new_int(5);
        let b = BigNum::new_int(18);
        let c = BigNum::new_int(90);
        assert!(are_field_elements_equal(&field_elements_multiplication(&a, &b), &c))
    }

    #[test]
    fn test_field_elements_inner_product() {
        let a: Vec<BigNum> = vec![BigNum::new_int(5), BigNum::new_int(1), BigNum::new_int(100), BigNum::new_int(0)];
        let b: Vec<BigNum> = vec![BigNum::new_int(18), BigNum::new_int(1), BigNum::new_int(200), BigNum::new_int(0)];
        let c = BigNum::new_int(90+1+200*100);
        assert!(are_field_elements_equal(&field_elements_inner_product(&a, &b).unwrap(), &c))
    }

    #[test]
    fn test_scale_field_element_vector() {
        let a: Vec<BigNum> = vec![BigNum::new_int(5), BigNum::new_int(1), BigNum::new_int(100), BigNum::new_int(0)];
        let n = BigNum::new_int(3);
        let na = scale_field_element_vector(&n, &a);
        assert!(are_field_elements_equal(&na[0], &BigNum::new_int(5*3)));
        assert!(are_field_elements_equal(&na[1], &BigNum::new_int(1*3)));
        assert!(are_field_elements_equal(&na[2], &BigNum::new_int(100*3)));
        assert!(are_field_elements_equal(&na[3], &BigNum::new_int(0)));
    }

    #[test]
    fn test_add_field_element_vectors() {
        let a: Vec<BigNum> = vec![BigNum::new_int(5), BigNum::new_int(1), BigNum::new_int(100), BigNum::new_int(0)];
        let b: Vec<BigNum> = vec![BigNum::new_int(18), BigNum::new_int(1), BigNum::new_int(200), BigNum::new_int(0)];
        let c = add_field_element_vectors(&a, &b).unwrap();
        assert!(are_field_elements_equal(&c[0], &BigNum::new_int(5+18)));
        assert!(are_field_elements_equal(&c[1], &BigNum::new_int(1+1)));
        assert!(are_field_elements_equal(&c[2], &BigNum::new_int(100+200)));
        assert!(are_field_elements_equal(&c[3], &BigNum::new_int(0)));
    }

    #[test]
    fn test_field_elem_vector() {
        let zero_vec: Vec<BigNum> = field_elem_vector!(0, 5);
        for i in 0..5 {
            assert!(zero_vec[i].iszilch())
        }

        let unit_vec: Vec<BigNum> = field_elem_vector!(1, 4);
        for i in 0..4 {
            assert!(unit_vec[i].isunity())
        }

        let two_vec: Vec<BigNum> = field_elem_vector!(2, 10);
        let base = 2u32;
        for i in 0..3 {
            assert!(are_field_elements_equal(&two_vec[i], &BigNum::new_int(base.pow(i as u32) as isize)));
        }
    }
}