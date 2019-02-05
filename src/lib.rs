extern crate amcl;

pub use self::amcl::bls381 as BLSCurve;
//pub use self::amcl::bn254 as BLSCurve;

#[macro_use]
mod errors;

#[macro_use]
mod utils;

pub mod types;
pub mod constants;
pub mod inner_product;
pub mod range_proof;

#[macro_use]
extern crate lazy_static;

pub mod r1cs;