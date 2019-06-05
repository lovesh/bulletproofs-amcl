#![allow(non_snake_case)]

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate amcl_wrapper;

#[macro_use]
pub mod errors;

#[macro_use]
pub mod utils;

pub mod inner_product;
#[macro_use]
pub mod range_proof;
mod transcript;

mod new_ipp;

pub mod r1cs;
