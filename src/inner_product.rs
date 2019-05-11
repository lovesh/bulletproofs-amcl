use super::errors::ValueError;
use super::utils::gen_challenges;
use crate::utils::field_elem::{FieldElement, FieldElementVector};
use crate::utils::group_elem::{GroupElement, GroupElementVector};
use crate::utils::commitment::*;


#[allow(non_snake_case)]
pub struct InnerProductArgument<'a> {
    G: &'a GroupElementVector,
    H: &'a GroupElementVector,
    u: &'a GroupElement,
    P: &'a GroupElement,
    size: usize
}

#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct InnerProductArgumentProof {
    pub L: GroupElementVector,
    pub R: GroupElementVector,
    pub a: FieldElement,
    pub b: FieldElement
}

impl<'a> InnerProductArgument<'a> {
    pub fn new(g: &'a GroupElementVector, h: &'a GroupElementVector, u: &'a GroupElement,
               P: &'a GroupElement) -> Result<InnerProductArgument<'a>, ValueError> {
        check_vector_size_for_equality!(g, h)?;
        if !g.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(g.len()))
        }
        Ok(InnerProductArgument { G: g, H: h, u, P, size:  g.len()})
    }

    // Generate proof of knowledge of vectors `a` and `b`
    pub fn gen_proof(&self, a: &FieldElementVector, b: &FieldElementVector) -> Result<InnerProductArgumentProof, ValueError> {
        check_vector_size_for_equality!(a, b)?;
        let L = GroupElementVector::new(0);
        let R = GroupElementVector::new(0);
        let mut state: Vec<u8> = vec![];
        self._gen_proof(self.G, self.H, a, b, L, R, &mut state)

        // Uncomment next line and comment above line for debugging
        //self._gen_proof(self.G, self.H, a, b,L, R, &mut state, &self.P)
    }

    // TODO: Add verification using multi-exponentiation

    pub fn verify_proof_recursively(&self, proof: &InnerProductArgumentProof) -> Result<bool, ValueError> {
        let (l, r) = (&proof.L, &proof.R);
        check_vector_size_for_equality!(l, r)?;
        let mut state: Vec<u8> = vec![];
        self._verify_proof_recursively(&self.G, &self.H, &proof.L, &proof.R, &proof.a, &proof.b, &self.P, &mut state)
    }

    fn _gen_proof(&self, g: &GroupElementVector, h: &GroupElementVector, a: &FieldElementVector, b: &FieldElementVector, mut L: GroupElementVector,
                  mut R: GroupElementVector, state: &mut Vec<u8>) -> Result<InnerProductArgumentProof, ValueError> {
                // Uncomment next line and comment above line for debugging
                  //mut R: GroupElementVector, state: &mut Vec<u8>, P: &GroupElement) -> Result<InnerProductArgumentProof, ValueError> {
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
                let a1_b2= a1.inner_product(&b2)?;
                let _L = commit_to_field_element_vectors(&g2, &h1, &self.u, &a1, &b2, &a1_b2)?;

                // H(a2, 0^n_prime, 0^n_prime, b1, <a2, b1>), not using `hash` to avoid working on 0^n_prime
                let a2_b1= a2.inner_product(&b1)?;
                let _R = commit_to_field_element_vectors(&g1, &h2, &self.u, &a2, &b1, &a2_b1)?;

                // The challenge should include the transcript till now, i.e including current `L` and `R`
                let x = gen_challenges(&[&_L, &_R, &self.P], state, 1)[0];
                let x_inv = x.inverse();

                // Next lines only for debugging
                /*let x_sqr = x.square();
                let x_inv_sqr = x_inv.square();
                let P_prime = Self::calculate_new_P(P, &x_sqr, &x_inv_sqr, &_L, &_R);
                println!("During proving, for n {}, challenge is {}, new P is {}", &n, &x, &P_prime);*/

                L.push(_L);
                R.push(_R);

                // a' = x.a1 + x^-1.a2
                let a_prime = a1.scaled_by(&x).plus(&a2.scaled_by(&x_inv))?;

                // b' = x^-1.b1 + x.b2
                let b_prime = b1.scaled_by(&x_inv).plus(&b2.scaled_by(&x))?;

                let g_prime = Self::calculate_new_g(&g1, &g2, &x, &x_inv)?;
                let h_prime = Self::calculate_new_h(&h1, &h2, &x, &x_inv)?;

                /*println!("During proving, for n {}, new g is {:?}", &n, &g_prime);
                println!("During proving, for n {}, new h is {:?}", &n, &h_prime);*/

                self._gen_proof(&g_prime, &h_prime, &a_prime, &b_prime,
                                 L, R, state)
                            // Uncomment next line and comment above line for debugging
                                 //L, R, state, &P_prime)
            }
        }
    }

    fn _verify_proof_recursively(&self, g: &GroupElementVector, h: &GroupElementVector, L: &GroupElementVector, R: &GroupElementVector,
                                 a: &FieldElement, b: &FieldElement, P: &GroupElement, state: &mut Vec<u8>) -> Result<bool, ValueError> {
        match g.len() {
            1 => {
                let g_a = g[0] * a;
                let h_b = h[0] * b;
                let c = a * b;
                let u_c = self.u * c;
                let sum = g_a + h_b + u_c;
                Ok(sum == *P)
            },
            n => {
                let _L = &L[0];
                let _R = &R[0];
                let x = gen_challenges(&[&_L, &_R, &self.P], state, 1)[0];
                let x_sqr = x.square();
                let x_inv = x.inverse();
                let x_inv_sqr = x_inv.square();

                let P_prime = Self::calculate_new_P(&P, &x_sqr, &x_inv_sqr, &_L, &_R);

//                println!("During verification, for n {}, challenge is {}, new P is {}, L R {:?} {:?}", &n, &x, &self.P, &_L, &_R);

                let n_prime = n / 2;
                let (g1, g2) = g.split_at(n_prime);
                let (h1, h2) = h.split_at(n_prime);

                let g_prime = Self::calculate_new_g(&g1, &g2, &x, &x_inv)?;
                let h_prime = Self::calculate_new_h(&h1, &h2, &x, &x_inv)?;

                /*println!("During verification, for n {}, new g is {:?}", &n, &g_prime);
                println!("During verification, for n {}, new h is {:?}", &n, &h_prime);*/

                let (_, newL) =  L.as_slice().split_at(1);
                let newL = GroupElementVector::from(newL);
                let (_, newR) =  R.as_slice().split_at(1);
                let newR = GroupElementVector::from(newR);
                self._verify_proof_recursively(&g_prime, &h_prime, &newL,
                                               &newR, a, b, &P_prime, state)
            }
        }
    }

    //  hash function H : Z_p^2n+1 -> G1
    // H(a_1, a'_2, b_1, b'_2, c) = g[:n/2]^a_1.g[n/2:]^a'_2.h[:n/2]^b_1.h[n/2:]^b'_2.u^c
    fn hash(g: &GroupElementVector, h: &GroupElementVector, a1: &FieldElementVector, a2_prime: &FieldElementVector, b1: &FieldElementVector,
                b2_prime: &FieldElementVector, u: &GroupElement, c: &FieldElement) -> Result<GroupElement, ValueError> {
        check_vector_size_for_equality!(g, h)?;
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

        let a1_g1 = g1.inner_product_var_time(&a1)?;
        let a2_prime_g2 = g2.inner_product_var_time(a2_prime)?;
        let b1_h1 = h1.inner_product_var_time(&b1)?;
        let b2_prime_h2 = h2.inner_product_var_time(b2_prime)?;

        let u_c = u * c;

        Ok(a1_g1 + a2_prime_g2 + b1_h1 + b2_prime_h2+ u_c)
    }

    // g' = (x^-1.g1 o x.g2)
    fn calculate_new_g(g1: &GroupElementVector, g2: &GroupElementVector, x: &FieldElement,
                       x_inv: &FieldElement) -> Result<GroupElementVector, ValueError> {
        g1.scaled_by(x_inv).hadamard_product(&g2.scaled_by(x))
    }

    // h' = (x.h1 o x^-1.h2)
    fn calculate_new_h(h1: &GroupElementVector, h2: &GroupElementVector, x: &FieldElement,
                       x_inv: &FieldElement) -> Result<GroupElementVector, ValueError> {
        h1.scaled_by(x).hadamard_product(&h2.scaled_by(x_inv))
    }

    // P = L^x^2.P.R^x^-2
    fn calculate_new_P(old_P: &GroupElement, x_sqr: &FieldElement, x_inv_sqr: &FieldElement, L: &GroupElement, R: &GroupElement) -> GroupElement {
        let _P1 = L * x_sqr;
        let _P2 = R * x_inv_sqr;
        old_P + _P1 + _P2
    }

    // Construct H' = H^(y^-n)
    pub fn compute_h_prime(H: &GroupElementVector, y: &FieldElement) -> GroupElementVector {
        let y_inv = y.inverse();
        let y_inv_vandm_vec = FieldElementVector::new_vandermonde_vector(&y_inv, H.len());

        // Construct H' = H^(y^-n)
        let mut H_prime = GroupElementVector::with_capacity(H.len());
        for i in 0..H.len() {
            H_prime.push(H[i] * y_inv_vandm_vec[i]);
        }
        H_prime
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_inner_product_argument() {
        let g: GroupElementVector = vec!["g1", "g2", "g3", "g4"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let h: GroupElementVector = vec!["h1", "h2", "h3", "h4"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let u = GroupElement::from_msg_hash("u".as_bytes());
        let a: FieldElementVector = vec![1, 2, 3, 4].iter().map(| i | FieldElement::from(*i as u8)).collect::<Vec<FieldElement>>().into();
        let b: FieldElementVector = vec![5, 6, 7, 8].iter().map(| i | FieldElement::from(*i as u8)).collect::<Vec<FieldElement>>().into();

        let g_a = g.inner_product_var_time(&a).unwrap();
        let h_b = h.inner_product_var_time(&b).unwrap();
        let c = a.inner_product(&b).unwrap();
        let u_c = u * c;

        let P = g_a + h_b + u_c;

        // Correct proof
        let ipa = InnerProductArgument::new(&g, &h, &u, &P).unwrap();
        let proof = ipa.gen_proof(&a, &b).unwrap();
        let res = ipa.verify_proof_recursively(&proof);
        assert!(res.is_ok());
        let r = res.unwrap();
        assert!(r);

        // Incorrect proof
        let d: FieldElementVector = vec![6, 6, 7, 8].iter().map(| i | FieldElement::from(*i as u8)).collect::<Vec<FieldElement>>().into();
        let incorrect_proof = ipa.gen_proof(&a, &d).unwrap();
        let res1 = ipa.verify_proof_recursively(&incorrect_proof).unwrap();
        assert!(!res1);
    }

    #[test]
    fn test_input_validation() {
        let g: GroupElementVector = vec!["g1", "g2", "g3", "g4"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let h: GroupElementVector = vec!["h1", "h2"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let u = GroupElement::from_msg_hash("u".as_bytes());
        let a: FieldElementVector = vec![1, 2, 3, 4].iter().map(| i | FieldElement::from(*i as u8)).collect::<Vec<FieldElement>>().into();
        let b: FieldElementVector = vec![5, 6, 7, 8].iter().map(| i | FieldElement::from(*i as u8)).collect::<Vec<FieldElement>>().into();

        let g_a = g.inner_product_var_time(&a).unwrap();
        let h_b = h.inner_product_var_time(&b);
        assert!(h_b.is_err());
        let c = a.inner_product(&b).unwrap();
        let u_c = u * c;

        let P = g_a + u_c;

        let ipc = InnerProductArgument::new(&g, &h, &u, &P);
        assert!(ipc.is_err());
    }
}
