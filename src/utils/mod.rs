extern crate rand;
extern crate amcl;

#[macro_use]
pub mod field_elem;
#[macro_use]
pub mod group_elem;
pub mod commitment;
pub mod vector_poly;

use rand::RngCore;
use rand::rngs::EntropyRng;

use self::amcl::rand::RAND;
use super::constants::{MODBYTES, CurveOrder, GeneratorG1, GroupG1_SIZE, NLEN};
use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use amcl::sha3::{SHAKE256, SHA3};
use crate::utils::group_elem::GroupElement;
use crate::utils::field_elem::FieldElement;


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

pub fn get_generators(prefix: &str, n: usize) -> Vec<GroupElement> {
    //let prefix = String::from(s);
    let mut gens: Vec<GroupElement> = Vec::with_capacity(n);
    for i in 1..n+1 {
        let s: String = prefix.to_string() + &i.to_string();
        gens.push(GroupElement::from_msg_hash(s.as_bytes()));
    }
    gens
}

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
    use std::time::{Duration, Instant};
    use amcl::bls381::big::BIG;
    use crate::amcl::bls381::fp::FP;
    use crate::amcl::bls381::ecp::ECP;

    #[test]
    fn timing_fp_big() {

        let count = 100;
        let elems: Vec<_> = (0..count).map(|_| FieldElement::random(None)).collect();
        let bigs: Vec<_> = elems.iter().map(|f|f.to_bignum()).collect();
        let fs: Vec<_> = bigs.iter().map(|b| FP::new_big(&b)).collect();
        let mut res_mul = BIG::new_int(1 as isize);
        let mut start = Instant::now();
        for b in &bigs {
            res_mul = BigNum::modmul(&res_mul, &b, &CurveOrder);
        }
        println!("Multiplication time for {} BIGs = {:?}", count, start.elapsed());

        let mut res_mul = FP::new_int(1 as isize);
        start = Instant::now();
        for f in &fs {
            res_mul.mul(&f);
        }
        println!("Multiplication time for {} FPs = {:?}", count, start.elapsed());

        let mut inverses_b: Vec<BigNum> = vec![];
        let mut inverses_f: Vec<FP> = vec![];

        start = Instant::now();
        for b in &bigs {
            let mut i = b.clone();
            i.invmodp(&CurveOrder);
            inverses_b.push(i);
        }
        println!("Inverse time for {} BIGs = {:?}", count, start.elapsed());
        for i in 0..count {
            let r = BigNum::modmul(&inverses_b[i], &bigs[i], &CurveOrder);
            assert_eq!(BigNum::comp(&r, &BigNum::new_int(1 as isize)), 0);
        }

        start = Instant::now();
        for f in &fs {
            let mut i = f.clone();
            i.inverse();
            inverses_f.push(i);
        }
        println!("Inverse time for {} FPs = {:?}", count, start.elapsed());
        for i in 0..count {
            let mut c = inverses_f[i].clone();
            c.mul(&fs[i]);
            assert!(c.equals(&FP::new_int(1 as isize)));
        }
    }

    #[test]
    fn timing_ecp() {
        let count = 100;
        let mut a = vec![];
        let mut b = vec![];
        let mut g = vec![];
        let mut h = vec![];

        let mut r1 = vec![];
        let mut r2 = vec![];

        for _ in 0..count {
            a.push(FieldElement::random(None).to_bignum());
            b.push(FieldElement::random(None).to_bignum());
            g.push(GroupElement::random(None).to_ecp());
            h.push(GroupElement::random(None).to_ecp());
        }

        let mut start = Instant::now();
        for i in 0..count {
            r1.push(g[i].mul2(&a[i], &h[i], &b[i]));
        }
        println!("mul2 time for {} = {:?}", count, start.elapsed());

        start = Instant::now();
        for i in 0..count {
            let mut _1 = g[i].mul(&a[i]);
            _1.add(&h[i].mul(&b[i]));
            r2.push( _1);
        }
        println!("mul+add time for {} = {:?}", count, start.elapsed());

        for i in 0..count {
            assert!(r1[i].equals(&mut r2[i]))
        }
    }
}

