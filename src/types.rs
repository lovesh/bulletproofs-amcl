extern crate amcl;

use std::fmt;
use super::BLSCurve::big::BIG;
use super::BLSCurve::fp::FP;
use super::BLSCurve::ecp::ECP;

pub type BigNum = BIG;
//pub type BigNum = FP;
pub type GroupG1 = ECP;
