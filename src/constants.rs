extern crate amcl;

use self::amcl::arch::Chunk;
use self::amcl::bls381::rom;
use self::amcl::bls381::big::{NLEN, MODBYTES as curve_MODBYTES};
use super::types::{BigNum, GroupG1};

pub const MODBYTES: usize = curve_MODBYTES;
// Byte size of element in group G1, 1 extra byte for compression
pub const GroupG1_SIZE: usize = (2 * MODBYTES + 1) as usize;

lazy_static! {
    pub static ref GeneratorG1: GroupG1 = GroupG1::generator();
    pub static ref CurveOrder: BigNum = BigNum::new_ints(&rom::CURVE_ORDER);
}
