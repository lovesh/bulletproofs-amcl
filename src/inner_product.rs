use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use super::utils::{scalar_point_inner_product, scalar_point_multiplication,
                   get_bytes_for_G1_point, hash_as_BigNum, field_elements_inner_product,
                   field_element_inverse, scale_field_element_vector, add_field_element_vectors,
                   scale_group_element_vector, group_elements_hadamard_product};

struct InnerProductArgument<'a> {
    g: &'a [GroupG1],
    h: &'a [GroupG1],
    u: &'a GroupG1,
    P: &'a GroupG1,
    size: usize
}

struct InnerProductArgumentProof {
    pub L: Vec<GroupG1>,
    pub R: Vec<GroupG1>,
    pub a: BigNum,
    pub b: BigNum
}

impl<'a> InnerProductArgument<'a> {
    pub fn new(g: &'a [GroupG1], h: &'a [GroupG1], u: &'a GroupG1,
               P: &'a GroupG1) -> Result<InnerProductArgument<'a>, ValueError> {
        if g.len() != h.len() {
            return Err(ValueError::UnequalSizeVectors(g.len(), h.len()))
        }
        if !g.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(g.len()))
        }
        Ok(InnerProductArgument { g, h, u, P, size:  g.len()})
    }

    pub fn gen_proof(&self, a: &[BigNum], b: &[BigNum]) -> Result<InnerProductArgumentProof, ValueError> {
        let mut L: Vec<GroupG1> = vec![];
        let mut R: Vec<GroupG1> = vec![];
        if a.len() != b.len() {
            return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
        }
        let mut state: Vec<u8> = vec![];
        self._gen_proof(self.g, self.h, a, b,L, R, &mut state)
    }

    pub fn verify_proof_recursive(&self, proof: &InnerProductArgumentProof) -> Result<bool, ValueError> {
        if proof.L.len() != proof.R.len() {
            return Err(ValueError::UnequalSizeVectors(proof.L.len(), proof.R.len()))
        }
        let mut state: Vec<u8> = vec![];
        self._verify_proof_recursive(&self.g, &self.h, &proof.L, &proof.R, &self.P, &mut state)
    }

    // TODO: Add verification using multi-exponentiation

    fn _verify_proof_recursive(&self, g: &[GroupG1], h: &[GroupG1], L: &[GroupG1], R: &[GroupG1],
                               P: &GroupG1, mut state: &mut Vec<u8>) -> Result<bool, ValueError> {

        unimplemented!()
    }

    fn _gen_proof(&self, g: &[GroupG1], h: &[GroupG1], a: &[BigNum], b: &[BigNum], mut L: Vec<GroupG1>,
                  mut R: Vec<GroupG1>, mut state: &mut Vec<u8>) -> Result<InnerProductArgumentProof, ValueError> {
        match a.len() {
            1 => {
                Ok(InnerProductArgumentProof {
                    L,
                    R,
                    a: a[0].clone(),
                    b: b[0].clone()
                })
            },
            n => {
                let n_prime = n / 2;
                let (g1, g2) = g.split_at(n_prime);
                let (h1, h2) = h.split_at(n_prime);
                let (a1, a2) = a.split_at(n_prime);
                let (b1, b2) = b.split_at(n_prime);

                // H(0^n_prime, a1, b2, 0^n_prime, <a1, b2>), not using `hash` to avoid working on 0^n_prime
                let a1_g2 = scalar_point_inner_product(&a1, &g2)?;
                let b2_h1 = scalar_point_inner_product(&b2, &h1)?;
                let a1_b2= field_elements_inner_product(&a1, &b2)?;
                let a1_b2_u = scalar_point_multiplication(&a1_b2, &self.u);
                let mut _L = GroupG1::new();
                _L.add(&a1_g2);
                _L.add(&b2_h1);
                _L.add(&a1_b2_u);

                // H(a2, 0^n_prime, 0^n_prime, b1, <a2, b1>), not using `hash` to avoid working on 0^n_prime
                let a2_g1 = scalar_point_inner_product(&a2, &g1)?;
                let b1_h2 = scalar_point_inner_product(&b1, &h2)?;
                let a2_b1= field_elements_inner_product(&a2, &b1)?;
                let a2_b1_u = scalar_point_multiplication(&a2_b1, &self.u);
                let mut _R = GroupG1::new();
                _R.add(&a2_g1);
                _R.add(&b1_h2);
                _R.add(&a2_b1_u);

                L.push(_L);
                R.push(_R);

                // The challenge should include the transcript till now, i.e including current `L` and `R`
                let x = Self::gen_challenge(&L, &R, &self.P, state);
                let x_inv = field_element_inverse(&x);

                // a' = x.a1 + x^-1.a2
                let a_prime_1 = scale_field_element_vector(&x, &a1);
                let a_prime_2 = scale_field_element_vector(&x_inv, &a2);
                let a_prime = add_field_element_vectors(&a_prime_1, &a_prime_2)?;

                // b' = x^-1.b1 + x.b2
                let b_prime_1 = scale_field_element_vector(&x_inv, &b1);
                let b_prime_2 = scale_field_element_vector(&x, &b2);
                let b_prime = add_field_element_vectors(&b_prime_1, &b_prime_2)?;

                // g' = (x^-1.g1 o x.g2)
                let g_prime_1 = scale_group_element_vector(&x_inv, &g1);
                let g_prime_2 = scale_group_element_vector(&x, &g2);
                let g_prime = group_elements_hadamard_product(&g_prime_1, &g_prime_2)?;

                // h' = (x.h1 o x^-1.h2)
                let h_prime_1 = scale_group_element_vector(&x, &h1);
                let h_prime_2 = scale_group_element_vector(&x_inv, &h2);
                let h_prime = group_elements_hadamard_product(&h_prime_1, &h_prime_2)?;

                self._gen_proof(&g_prime, &h_prime, &a_prime, &b_prime,
                                 L, R, state)
            }
        }
    }

    //  hash function H : Z_p^2n+1 -> G1
    // H(a_1, a'_2, b_1, b'_2, c) = g[:n/2]^a_1.g[n/2:]^a'_2.h[:n/2]^b_1.h[n/2:]^b'_2.u^c
    fn hash(g: &[GroupG1], h: &[GroupG1], a1: &[BigNum], a2_prime: &[BigNum], b1: &[BigNum],
                b2_prime: &[BigNum], u: &GroupG1, c: &BigNum) -> Result<GroupG1, ValueError> {
        if g.len() != h.len() {
            return Err(ValueError::UnequalSizeVectors(g.len(), h.len()))
        }
        if !g.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(g.len()))
        }

        let n = g.len();
        let n_prime = n / 2;

        if a1.len() != n_prime {
            return Err(ValueError::IncorrectSize(n_prime))
        }
        if a2_prime.len() != n_prime {
            return Err(ValueError::IncorrectSize(n_prime))
        }
        if b1.len() != n_prime {
            return Err(ValueError::IncorrectSize(n_prime))
        }
        if b2_prime.len() != n_prime {
            return Err(ValueError::IncorrectSize(n_prime))
        }

        let (g1, g2) = g.split_at(n_prime);
        let (h1, h2) = h.split_at(n_prime);

        let mut accum = GroupG1::new();
        let a1_g1 = scalar_point_inner_product(a1, g1)?;
        accum.add(&a1_g1);
        let a2_prime_g2 = scalar_point_inner_product(a2_prime, g2)?;
        accum.add(&a2_prime_g2);
        let b1_h1 = scalar_point_inner_product(b1, h1)?;
        accum.add(&b1_h1);
        let b2_prime_h2 = scalar_point_inner_product(b2_prime, h2)?;
        accum.add(&b2_prime_h2);
        let c_u = scalar_point_multiplication(c, u);
        accum.add(&c_u);

        Ok(accum)
    }

    // Generate challenge. Takes input group elements and a mutable reference to current state.
    // Apart from generating the challenge, updates the mutable state
    fn gen_challenge(L: &[GroupG1], R: &[GroupG1], P: &GroupG1, state: &mut Vec<u8>) -> BigNum {
        for i in 0..L.len() {
            state.extend_from_slice(&get_bytes_for_G1_point(&L[i]));
        }
        for i in 0..R.len() {
            state.extend_from_slice(&get_bytes_for_G1_point(&R[i]));
        }
        state.extend_from_slice(&get_bytes_for_G1_point(P));
        hash_as_BigNum(&state)
    }
}
