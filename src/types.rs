extern crate amcl;

use super::BLSCurve::big::BIG;
use super::BLSCurve::fp::FP;
use super::BLSCurve::ecp::ECP;

pub type BigNum = BIG;
pub type PrimeFieldElem = FP;
pub type GroupG1 = ECP;
