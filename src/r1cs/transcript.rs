//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.
use merlin::Transcript;
use crate::types::BigNum;
use crate::types::GroupG1;
use crate::utils::get_bytes_for_BigNum;
use crate::utils::get_bytes_for_G1_point;

pub trait TranscriptProtocol {
    /// Commit a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);
    /// Commit a `scalar` with the given `label`.
    fn commit_scalar(&mut self, label: &'static [u8], scalar: &BigNum);
    /// Commit a `point` with the given `label`.
    fn commit_point(&mut self, label: &'static [u8], point: &GroupG1);
    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> BigNum;
}

impl TranscriptProtocol for Transcript {
    fn r1cs_domain_sep(&mut self) {
        self.commit_bytes(b"dom-sep", b"r1cs v1");
    }

    fn commit_scalar(&mut self, label: &'static [u8], scalar: &BigNum) {
        self.commit_bytes(label, &get_bytes_for_BigNum(scalar));
    }

    fn commit_point(&mut self, label: &'static [u8], point: &GroupG1) {
        self.commit_bytes(label, &get_bytes_for_G1_point(point));
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> BigNum {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        BigNum::frombytes(&buf)
    }
}
