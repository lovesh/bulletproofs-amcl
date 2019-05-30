#![allow(non_snake_case)]

extern crate amcl;

#[macro_use]
extern crate lazy_static;

pub use self::amcl::bls381 as ECCurve;
//pub use self::amcl::bn254 as ECCurve;

#[macro_use]
pub mod errors;

#[macro_use]
pub mod utils;

pub mod types;
pub mod constants;
pub mod inner_product;
pub mod range_proof;
mod transcript;

mod new_ipp;

pub mod r1cs;
