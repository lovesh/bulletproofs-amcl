use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use super::utils::{scalar_point_inner_product, scalar_point_multiplication,
                   get_bytes_for_G1_point, hash_as_BigNum, field_elements_inner_product,
                   field_element_inverse, scale_field_element_vector, add_field_element_vectors,
                   scale_group_element_vector, group_elements_hadamard_product,
                   field_elements_multiplication, field_element_square, commit_to_field_element_vectors, gen_challenges};

pub struct InnerProductArgument<'a> {
    G: &'a [GroupG1],
    H: &'a [GroupG1],
    u: &'a GroupG1,
    P: &'a GroupG1,
    size: usize
}

pub struct InnerProductArgumentProof {
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
        Ok(InnerProductArgument { G: g, H: h, u, P, size:  g.len()})
    }

    // Generate proof of knowledge of vectors `a` and `b`
    pub fn gen_proof(&self, a: &[BigNum], b: &[BigNum]) -> Result<InnerProductArgumentProof, ValueError> {
        let L: Vec<GroupG1> = vec![];
        let R: Vec<GroupG1> = vec![];
        if a.len() != b.len() {
            return Err(ValueError::UnequalSizeVectors(a.len(), b.len()))
        }
        let mut state: Vec<u8> = vec![];
        self._gen_proof(self.G, self.H, a, b, L, R, &mut state)

        // Uncomment next line and comment above line for debugging
        //self._gen_proof(self.g, self.h, a, b,L, R, &mut state, &self.P)
    }

    // TODO: Add verification using multi-exponentiation

    pub fn verify_proof_recursively(&self, proof: &InnerProductArgumentProof) -> Result<bool, ValueError> {
        if proof.L.len() != proof.R.len() {
            return Err(ValueError::UnequalSizeVectors(proof.L.len(), proof.R.len()))
        }
        let mut state: Vec<u8> = vec![];
        self._verify_proof_recursively(&self.G, &self.H, &proof.L, &proof.R, &proof.a, &proof.b, &self.P, &mut state)
    }

    fn _gen_proof(&self, g: &[GroupG1], h: &[GroupG1], a: &[BigNum], b: &[BigNum], mut L: Vec<GroupG1>,
                  mut R: Vec<GroupG1>, state: &mut Vec<u8>) -> Result<InnerProductArgumentProof, ValueError> {
                // Uncomment next line and comment above line for debugging
                  //mut R: Vec<GroupG1>, state: &mut Vec<u8>, P: &GroupG1) -> Result<InnerProductArgumentProof, ValueError> {
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
                let a1_b2= field_elements_inner_product(&a1, &b2)?;
                let _L = commit_to_field_element_vectors(&g2, &h1, &self.u, &a1, &b2, &a1_b2)?;

                // H(a2, 0^n_prime, 0^n_prime, b1, <a2, b1>), not using `hash` to avoid working on 0^n_prime
                let a2_b1= field_elements_inner_product(&a2, &b1)?;
                let _R = commit_to_field_element_vectors(&g1, &h2, &self.u, &a2, &b1, &a2_b1)?;

                // The challenge should include the transcript till now, i.e including current `L` and `R`
                let x = gen_challenges(&[&_L, &_R, &self.P], state, 1)[0];
                let x_inv = field_element_inverse(&x);

                // Next lines only for debugging
                /*let x_sqr = field_element_square(&x);
                let x_inv_sqr = field_element_square(&x_inv);
                let P_prime = Self::calculate_new_P(P, &x_sqr, &x_inv_sqr, &_L, &_R);
                println!("During proving, for n {}, challenge is {}, new P is {}", &n, &x, &P_prime);*/

                L.push(_L);
                R.push(_R);

                // a' = x.a1 + x^-1.a2
                let a_prime_1 = scale_field_element_vector(&x, &a1);
                let a_prime_2 = scale_field_element_vector(&x_inv, &a2);
                let a_prime = add_field_element_vectors(&a_prime_1, &a_prime_2)?;

                // b' = x^-1.b1 + x.b2
                let b_prime_1 = scale_field_element_vector(&x_inv, &b1);
                let b_prime_2 = scale_field_element_vector(&x, &b2);
                let b_prime = add_field_element_vectors(&b_prime_1, &b_prime_2)?;

                let g_prime = Self::calculate_new_g(g1, g2, &x, &x_inv)?;
                let h_prime = Self::calculate_new_h(h1, h2, &x, &x_inv)?;

                /*println!("During proving, for n {}, new g is {:?}", &n, &g_prime);
                println!("During proving, for n {}, new h is {:?}", &n, &h_prime);*/

                self._gen_proof(&g_prime, &h_prime, &a_prime, &b_prime,
                                 L, R, state)
                            // Uncomment next line and comment above line for debugging
                                 //L, R, state, &P_prime)
            }
        }
    }

    fn _verify_proof_recursively(&self, g: &[GroupG1], h: &[GroupG1], L: &[GroupG1], R: &[GroupG1],
                                 a: &BigNum, b: &BigNum, P: &GroupG1, state: &mut Vec<u8>) -> Result<bool, ValueError> {
        match g.len() {
            1 => {
                let g_a = scalar_point_multiplication(&a, &g[0]);
                let h_b = scalar_point_multiplication(&b, &h[0]);
                let c = field_elements_multiplication(&a, &b);
                let u_c = scalar_point_multiplication(&c, &self.u);
                let mut sum = add_group_elements!(&g_a, &h_b, &u_c);
                let mut _P = GroupG1::new();
                _P.copy(&P);
                Ok(sum.equals(&mut _P))
            },
            n => {
                let _L = &L[0];
                let _R = &R[0];
                let x = gen_challenges(&[&_L, &_R, &self.P], state, 1)[0];
                let x_sqr = field_element_square(&x);
                let x_inv = field_element_inverse(&x);
                let x_inv_sqr = field_element_square(&x_inv);

                let P_prime = Self::calculate_new_P(&P, &x_sqr, &x_inv_sqr, &_L, &_R);

//                println!("During verification, for n {}, challenge is {}, new P is {}, L R {} {}", &n, &x, &self.P, &_L, &_R);

                let n_prime = n / 2;
                let (g1, g2) = g.split_at(n_prime);
                let (h1, h2) = h.split_at(n_prime);

                let g_prime = Self::calculate_new_g(g1, g2, &x, &x_inv)?;
                let h_prime = Self::calculate_new_h(h1, h2, &x, &x_inv)?;

                /*println!("During verification, for n {}, new g is {:?}", &n, &g_prime);
                println!("During verification, for n {}, new h is {:?}", &n, &h_prime);*/

                self._verify_proof_recursively(&g_prime, &h_prime, L.split_at(1).1,
                                               R.split_at(1).1, a, b, &P_prime, state)
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

        let a1_g1 = scalar_point_inner_product(a1, g1)?;
        let a2_prime_g2 = scalar_point_inner_product(a2_prime, g2)?;
        let b1_h1 = scalar_point_inner_product(b1, h1)?;
        let b2_prime_h2 = scalar_point_inner_product(b2_prime, h2)?;
        let c_u = scalar_point_multiplication(c, u);

        Ok(add_group_elements!(&a1_g1, &a2_prime_g2, &b1_h1, &b2_prime_h2))
    }

    // g' = (x^-1.g1 o x.g2)
    fn calculate_new_g(g1: &[GroupG1], g2: &[GroupG1], x: &BigNum,
                       x_inv: &BigNum) -> Result<Vec<GroupG1>, ValueError> {
        let g_prime_1 = scale_group_element_vector(x_inv, &g1);
        let g_prime_2 = scale_group_element_vector(x, &g2);
        group_elements_hadamard_product(&g_prime_1, &g_prime_2)
    }

    // h' = (x.h1 o x^-1.h2)
    fn calculate_new_h(h1: &[GroupG1], h2: &[GroupG1], x: &BigNum,
                       x_inv: &BigNum) -> Result<Vec<GroupG1>, ValueError> {
        let h_prime_1 = scale_group_element_vector(&x, &h1);
        let h_prime_2 = scale_group_element_vector(&x_inv, &h2);
        group_elements_hadamard_product(&h_prime_1, &h_prime_2)
    }

    // P = L^x^2.P.R^x^-2
    fn calculate_new_P(old_P: &GroupG1, x_sqr: &BigNum, x_inv_sqr: &BigNum, L: &GroupG1, R: &GroupG1) -> GroupG1 {
        let _P1 = scalar_point_multiplication(x_sqr, L);
        let _P2 = scalar_point_multiplication(x_inv_sqr, R);
        add_group_elements!(old_P, &_P1, &_P2)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::utils::hash_on_GroupG1;

    #[test]
    fn test_inner_product_argument() {
        let g: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let h: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let u = hash_on_GroupG1("u".as_bytes());
        let a: Vec<BigNum> = vec![1, 2, 3, 4].iter().map(| i | BigNum::new_int(*i as isize)).collect();
        let b: Vec<BigNum> = vec![5, 6, 7, 8].iter().map(| i | BigNum::new_int(*i as isize)).collect();

        let g_a = scalar_point_inner_product(&a, &g).unwrap();
        let h_b = scalar_point_inner_product(&b, &h).unwrap();
        let c = field_elements_inner_product(&a, &b).unwrap();
        let u_c = scalar_point_multiplication(&c, &u);

        let P = add_group_elements!(&g_a, &h_b, &u_c);

        // Correct proof
        let ipa = InnerProductArgument::new(&g, &h, &u, &P).unwrap();
        let proof = ipa.gen_proof(&a, &b).unwrap();
        let res = ipa.verify_proof_recursively(&proof);
        assert!(res.is_ok());
        let r = res.unwrap();
        assert!(r);

        // Incorrect proof
        let d: Vec<BigNum> = vec![6, 6, 7, 8].iter().map(| i | BigNum::new_int(*i as isize)).collect();
        let incorrect_proof = ipa.gen_proof(&a, &d).unwrap();
        let res1 = ipa.verify_proof_recursively(&incorrect_proof).unwrap();
        assert!(!res1);
    }

    #[test]
    fn test_input_validation() {
        let g: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let h: Vec<GroupG1> = vec!["h1", "h2"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let u = hash_on_GroupG1("u".as_bytes());
        let a: Vec<BigNum> = vec![1, 2, 3, 4].iter().map(| i | BigNum::new_int(*i as isize)).collect();
        let b: Vec<BigNum> = vec![5, 6, 7, 8].iter().map(| i | BigNum::new_int(*i as isize)).collect();

        let g_a = scalar_point_inner_product(&a, &g).unwrap();
        let g_b = scalar_point_inner_product(&b, &g).unwrap();
        let c = field_elements_inner_product(&a, &b).unwrap();
        let u_c = scalar_point_multiplication(&c, &u);

        let P = add_group_elements!(&g_a, &g_b, &u_c);

        let ipc = InnerProductArgument::new(&g, &h, &u, &P);
        assert!(ipc.is_err());
    }
}
