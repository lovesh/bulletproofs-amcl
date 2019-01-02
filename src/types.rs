extern crate amcl;

use std::fmt;
use self::amcl::bls381::big::BIG;
use self::amcl::bls381::ecp::ECP;

pub type BigNum = BIG;
pub type GroupG1 = ECP;


/*impl fmt::Display for BigNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut c = self.clone();
        write!(f, "{}", c.tostring())
    }
}*/
