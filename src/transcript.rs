//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.
use merlin::Transcript;
use crate::utils::field_elem::FieldElement;
use crate::utils::group_elem::G1;
use crate::constants::MODBYTES;


pub trait TranscriptProtocol {
    /// Commit a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);
    /// Commit a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);
    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);
    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);
    /// Commit a `scalar` with the given `label`.
    fn commit_scalar(&mut self, label: &'static [u8], scalar: &FieldElement);
    /// Commit a `point` with the given `label`.
    fn commit_point(&mut self, label: &'static [u8], point: &G1);
    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> FieldElement;
}


impl TranscriptProtocol for Transcript {
    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.commit_bytes(b"dom-sep", b"ipp v1");
        self.commit_bytes(b"n", &n.to_le_bytes());
    }

    fn r1cs_domain_sep(&mut self) {
        self.commit_bytes(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.commit_bytes(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.commit_bytes(b"dom-sep", b"r1cs-2phase");
    }

    fn commit_scalar(&mut self, label: &'static [u8], scalar: &FieldElement) {
        self.commit_bytes(label, &scalar.to_bytes());
    }

    fn commit_point(&mut self, label: &'static [u8], point: &G1) {
        self.commit_bytes(label, &point.to_bytes());
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> FieldElement {
        let mut buf = [0u8; MODBYTES];
        self.challenge_bytes(label, &mut buf);

        FieldElement::from(&buf)
    }
}
