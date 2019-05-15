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
use crate::utils::field_elem::FieldElement;
use crate::utils::group_elem::GroupElement;


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
