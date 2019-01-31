extern crate amcl;

use super::BLSCurve::rom;
use super::BLSCurve::big::{NLEN as curve_NLEN, MODBYTES as curve_MODBYTES, BASEBITS as curve_BASEBITS};
use super::types::{BigNum, GroupG1};

pub const MODBYTES: usize = curve_MODBYTES;
pub const BASEBITS: usize = curve_BASEBITS;
pub const NLEN: usize = curve_NLEN;
// Byte size of element in group G1, 1 extra byte for compression
pub const GroupG1_SIZE: usize = (2 * MODBYTES + 1) as usize;

lazy_static! {
    pub static ref GeneratorG1: GroupG1 = GroupG1::generator();
    pub static ref CurveOrder: BigNum = BigNum::new_ints(&rom::CURVE_ORDER);
}
