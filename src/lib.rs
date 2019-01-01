extern crate amcl;

pub use self::amcl::bls381 as BLSCurve;

pub mod types;
pub mod constants;
pub mod inner_product;

mod utils;
mod errors;

#[macro_use]
extern crate lazy_static;