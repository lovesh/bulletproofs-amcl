extern crate rand;
extern crate amcl;

#[macro_use]
pub mod macros;

#[macro_use]
pub mod field_elem;
#[macro_use]
pub mod group_elem;
pub mod commitment;
pub mod vector_poly;

use rand::RngCore;
use rand::rngs::EntropyRng;

use self::amcl::rand::RAND;
use super::constants::{MODBYTES, CurveOrder, GeneratorG1, GroupG1_SIZE, NLEN, FieldElementZero};
use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use amcl::sha3::{SHAKE256, SHA3};
use crate::utils::group_elem::GroupElement;
use crate::utils::field_elem::FieldElement;


pub fn get_seeded_RNG(entropy_size: usize) -> RAND {
    // initialise from at least 128 byte string of raw random entropy
    let mut entropy = vec![0; entropy_size];
    let mut rng = EntropyRng::new();
    rng.fill_bytes(&mut entropy.as_mut_slice());
    let mut r = RAND::new();
    r.clean();
    r.seed(entropy_size, &entropy);
    r
}

// Get a random field element of the curve order. Avoid 0.
pub fn random_field_element(order: Option<&BigNum>) -> BigNum {
    // initialise from at least 128 byte string of raw random entropy
    let entropy_size = 256;
    let mut r = get_seeded_RNG(entropy_size);
    let n = match order {
        Some(o) => BigNum::randomnum(&o, &mut r),
        None => BigNum::randomnum(&BigNum::new_big(&CurveOrder), &mut r)
    };
    if n.iszilch() { random_field_element(order) } else { n }
}

pub fn random_field_vector(size: usize, order: Option<&BigNum>) -> Vec<BigNum> {
    (0..size).map( | _ | random_field_element(order)).collect::<Vec<BigNum>>()
}

// Hash message and return output of size equal to curve modulus
pub fn hash_msg(msg: &[u8]) -> [u8; MODBYTES] {
    let mut hasher = SHA3::new(SHAKE256);
    for i in 0..msg.len(){
        hasher.process(msg[i]);
    }
    let mut h: [u8; MODBYTES] = [0; MODBYTES];
    hasher.shake(&mut h,MODBYTES);
    h
}

pub fn hash_on_GroupG1(msg: &[u8]) -> GroupG1 {
    GroupG1::mapit(&hash_msg(msg))
}

pub fn hash_as_BigNum(msg: &[u8]) -> BigNum {
    // TODO: Ensure result is not 0
    let mut n = BigNum::frombytes(&hash_msg(msg));
    n.rmod(&CurveOrder);
    n
}

pub fn get_bytes_for_G1_point(point: &GroupG1) -> Vec<u8> {
    let mut temp = GroupG1::new();
    temp.copy(point);
    let mut bytes: [u8; GroupG1_SIZE] = [0; GroupG1_SIZE];
    temp.tobytes(&mut bytes, false);
    bytes.to_vec()
}

pub fn get_bytes_for_BigNum(n: &BigNum) -> Vec<u8> {
    let mut temp = BigNum::new_copy(&n);
    let mut bytes: [u8; MODBYTES] = [0; MODBYTES];
    temp.tobytes(&mut bytes);
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

// Calculate a-b
pub fn subtract_field_elements(a: &BigNum, b: &BigNum) -> BigNum {
    let mut sum = a.clone();
    let neg_b = BigNum::modneg(&b, &CurveOrder);
    sum.add(&neg_b);
    sum.rmod(&CurveOrder);
    sum
}

// Return negative of field element
pub fn negate_field_element(a: &BigNum) -> BigNum {
    subtract_field_elements(&FieldElementZero, &a)
}

// Multiply point on the curve (element of group G1) with a scalar.
// field_element_a * group_element_b
pub fn scalar_point_multiplication(a: &BigNum, b: &GroupG1) -> GroupG1 {
    b.mul(a)
}

// Computes inner product of 2 vectors of field elements
// [a1, a2, a3, ...field elements].[b1, b2, b3, ...field elements] = (a1*b1 + a2*b2 + a3*b3) % curve_order
pub fn field_elements_inner_product(a: &[BigNum], b: &[BigNum]) -> Result<BigNum, ValueError> {
    check_vector_size_for_equality!(a, b)?;
    let mut accum = BigNum::new();
    for i in 0..a.len() {
        // Question: What if the next line overflows?
        let _m = field_elements_multiplication(&a[i], &b[i]);
        accum.add(&_m);
        // The modulo can be avoided if result of addition of above is greater than operands. Should benchmark
        accum.rmod(&CurveOrder)
    }
    Ok(accum)
}

// Computes inner product of 2 vectors, one of field elements and other of group elements.
// [a1, a2, a3, ...field elements].[b1, b2, b3, ...group elements] = (a1*b1 + a2*b2 + a3*b3)
pub fn scalar_point_inner_product(a: &[BigNum], b: &[GroupG1]) -> Result<GroupG1, ValueError> {
    // TODO: Use a faster multi-scalar multiplication algorithm
    check_vector_size_for_equality!(a, b)?;
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
    check_vector_size_for_equality!(a, b)?;
    let mut sum_vector: Vec<BigNum> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        sum_vector.push(add_field_elements!(&a[i], &b[i]))
    }
    Ok(sum_vector)
}

// Subtract 2 vectors of field elements, a - b
pub fn subtract_field_element_vectors(a: &[BigNum], b: &[BigNum]) ->  Result<Vec<BigNum>, ValueError> {
    check_vector_size_for_equality!(a, b)?;
    let mut diff_vector: Vec<BigNum> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let diff = subtract_field_elements(&a[i], &b[i]);
        diff_vector.push(diff)
    }
    Ok(diff_vector)
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

// Compute sum of all group elements of a vector
pub fn sum_group_elem_vector(a: &[GroupG1]) -> GroupG1 {
    let mut accum = GroupG1::new();
    for i in 0..a.len() {
        accum.add(&a[i])
    }
    accum
}

// Compute sum of all group elements of a vector
pub fn sum_field_elem_vector(a: &[BigNum]) -> BigNum {
    let mut accum = BigNum::new();
    for i in 0..a.len() {
        accum.add(&a[i]);
        accum.rmod(&CurveOrder)
    }
    accum
}

// Calculates Hadamard product of 2 group element vectors.
// Hadamard product of `a` and `b` = `a` o `b` = (a0 o b0, a1 o b1, ...).
// Here `o` denotes group operation, which in elliptic curve is point addition
pub fn group_elements_hadamard_product(a: &[GroupG1], b: &[GroupG1]) -> Result<Vec<GroupG1>, ValueError> {
    check_vector_size_for_equality!(a, b)?;
    let mut hadamard_product: Vec<GroupG1> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        hadamard_product.push(add_group_elements!(&a[i], &b[i]))
    }
    Ok(hadamard_product)
}

// Calculates Hadamard product of 2 field element vectors.
// Hadamard product of `a` and `b` = `a` o `b` = (a0 o b0, a1 o b1, ...).
// Here `o` denotes multiply operation
pub fn field_elements_hadamard_product(a: &[BigNum], b: &[BigNum]) -> Result<Vec<BigNum>, ValueError> {
    check_vector_size_for_equality!(a, b)?;
    let mut hadamard_product: Vec<BigNum> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        hadamard_product.push(field_elements_multiplication(&a[i], &b[i]));
    }
    Ok(hadamard_product)
}

pub fn multi_scalar_multiplication(field_elems: &[BigNum], group_elems: &[GroupG1]) -> Result<GroupG1, ValueError> {
    // TODO Add optimized implementation
    check_vector_size_for_equality!(field_elems, group_elems)?;
    let mut accum = GroupG1::new();
    for (f, g) in field_elems.iter().zip(group_elems.iter()) {
        accum.add(&scalar_point_multiplication(f, g))
    }
    Ok(accum)
}

// Generate a vector of field elements as:
// field_elem_vector!(k, n) => vec![1, k, k^2, k^3, ... k^n-1]
// field_elem_vector!(0, n) => vec![0, 0, ... n times]
pub fn field_elem_power_vector(elem: &BigNum, size: usize) -> Vec<BigNum> {
    if BigNum::iszilch(elem) {
        vec![BigNum::new(); size]
    } else if BigNum::isunity(elem) {
        vec![BigNum::new_int(1); size]
    } else {
        let mut v: Vec<BigNum> = Vec::with_capacity(size);
        v.push(BigNum::new_int(1));
        let mut current = elem.clone();
        for _ in 1..size {
            v.push(current.clone());
            current = field_elements_multiplication(&current, elem)
        }
        v
    }
}

// Compare 2 field elements for equality
pub fn are_field_elements_equal(a: &BigNum, b: &BigNum) -> bool {
    BigNum::comp(a, b) == 0
}

pub fn get_generators(prefix: &str, n: usize) -> Vec<GroupElement> {
    //let prefix = String::from(s);
    let mut gens: Vec<GroupElement> = Vec::with_capacity(n);
    for i in 1..n+1 {
        let s: String = prefix.to_string() + &i.to_string();
        gens.push(GroupElement::from_msg_hash(s.as_bytes()));
    }
    gens
}

// Gives vectors of bit-vectors for the Big number. Each `Chunk` has a separate bit-vector,
// hence upto NLEN bit-vectors possible. NOT SIDE CHANNEL RESISTANT
pub fn to_bitvectors(n: &BigNum) -> Vec<Vec<u8>> {
    let mut k = NLEN - 1;
    let mut s = BigNum::new_copy(n);
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

// Commit to field element vectors `a` and `b` with random field element `c`
// Given group element vectors `g` and `h` and group element `u`, compute
// (a1*g1 + a2*g2 + a3*g3) + (b1*h1 + b2*h2 + b3*h3) + c*u
/*pub fn commit_to_field_element_vectors(g: &[GroupG1], h: &[GroupG1], u: &GroupG1,
                         a: &[BigNum], b: &[BigNum], c: &BigNum) -> Result<GroupG1, ValueError> {
    let a_g = scalar_point_inner_product(a, g)?;
    let b_h = scalar_point_inner_product(b, h)?;
    let c_u = scalar_point_multiplication(c, u);
    Ok(add_group_elements!(&a_g, &b_h, &c_u))
}

// Commit to field element `elem` with randomness `r` given groups elements `g` and `h`, i.e. compute g^elem.h^r
pub fn commit_to_field_element(g: &GroupG1, h: &GroupG1, elem: &BigNum,
                               r: &BigNum) -> GroupG1 {
    let elem_g = scalar_point_multiplication(elem, g);
    let r_h = scalar_point_multiplication(r, h);
    add_group_elements!(&elem_g, &r_h)
}*/


// Generate `n` challenge values. Takes input group elements and a mutable reference to current state.
// Every challenge value includes the previous value too.
// Apart from generating the challenge, updates the mutable state
/*pub fn gen_challenges(input: &[&GroupG1], state: &mut Vec<u8>, n: usize) -> Vec<BigNum> {
    let mut r: Vec<BigNum> = Vec::with_capacity(n);
    for i in 0..input.len() {
        state.extend_from_slice(&get_bytes_for_G1_point(&input[i]));
    }
    r.push(hash_as_BigNum(&state));

    for _ in 1..n {
        let _p = GeneratorG1.mul(&r.last().unwrap());
        state.extend_from_slice(&get_bytes_for_G1_point(&_p));
        r.push(hash_as_BigNum(&state));
    }
    r
}*/
pub fn gen_challenges(input: &[&GroupElement], state: &mut Vec<u8>, n: usize) -> Vec<FieldElement> {
    let mut r = Vec::<FieldElement>::with_capacity(n);
    for i in 0..input.len() {
        state.extend_from_slice(&input[i].to_bytes());
    }
    r.push(FieldElement::from_msg_hash(&state));

    let gen = GroupElement::generator();
    for _ in 1..n {
        let _p = gen * r.last().unwrap();
        state.extend_from_slice(&_p.to_bytes());
        r.push(FieldElement::from_msg_hash(&state));
    }
    r
}

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
        let zero_vec: Vec<BigNum> = field_elem_power_vector(&BigNum::new_int(0), 5);
        for i in 0..5 {
            assert!(zero_vec[i].iszilch())
        }

        let unit_vec: Vec<BigNum> = field_elem_power_vector(&BigNum::new_int(1), 4);
        for i in 0..4 {
            assert!(unit_vec[i].isunity())
        }

        let two_vec: Vec<BigNum> = field_elem_power_vector(&BigNum::new_int(2), 10);
        let base = 2u32;
        for i in 0..3 {
            assert!(are_field_elements_equal(&two_vec[i], &BigNum::new_int(base.pow(i as u32) as isize)));
        }
    }

    #[test]
    fn test_to_bitvectors() {
        let n = BigNum::new_int(100);
        assert_eq!(to_bitvectors(&n), vec![vec![0, 0, 1, 0, 0, 1, 1]]);
        let mut c = vec![0i64; NLEN];
        c[0] = 2;
        c[1] = 100;
        let m = BigNum::new_ints(&c);
        assert_eq!(to_bitvectors(&m), vec![vec![0, 1], vec![0, 0, 1, 0, 0, 1, 1]]);
    }

    #[test]
    fn test_negating_field_elems() {
        let a = BigNum::new_int(100);
        let neg_a = negate_field_element(&a);
        assert!(!are_field_elements_equal(&a, &neg_a));
        let neg_neg_a = negate_field_element(&neg_a);
        assert!(are_field_elements_equal(&a, &neg_neg_a));
    }

    #[test]
    fn test_multi_scalar_multiplication() {
        let mut fs = vec![];
        let mut gs = vec![];

        for i in 0..5 {
            fs.push(random_field_element(None));
            gs.push(scalar_point_multiplication(&fs[i], &GeneratorG1))
        }
        let mut res = multi_scalar_multiplication(&fs, &gs).unwrap();

        let mut expected = GroupG1::new();
        for (f, g) in fs.iter().zip(gs.iter()) {
            expected.add(&scalar_point_multiplication(f, g))
        }

        assert!(expected.equals(&mut res))
    }
}