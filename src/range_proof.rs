use super::errors::ValueError;
use super::utils::gen_challenges;
use crate::utils::field_elem::{FieldElement, FieldElementVector};
use crate::utils::group_elem::{GroupElement, GroupElementVector};
use crate::utils::commitment::*;
use crate::constants::{GeneratorG1, CurveOrder};
use crate::inner_product::{InnerProductArgument, InnerProductArgumentProof};

// TODO: Sidechannel resistance. Make sure that range proof for a value with 1 bit set
// takes same time and memory as a value with all bits set.

pub struct RangeProofProtocol<'a> {
    G: &'a GroupElementVector,
    H: &'a GroupElementVector,
    g: &'a GroupElement,
    h: &'a GroupElement,
    V: &'a GroupElement,
    size: usize,
    one_vandm_vec: FieldElementVector,
    two_vandm_vec: FieldElementVector
}

pub struct RangeProof {
    A: GroupElement,
    S: GroupElement,
    T1: GroupElement,
    T2: GroupElement,
    tau_x: FieldElement,
    mu: FieldElement,
    t_hat: FieldElement,
    IPA_proof: InnerProductArgumentProof,
    // `l` and `r` are only for debugging.
    /*l: FieldElementVector,
    r: FieldElementVector,*/
}

impl<'a> RangeProofProtocol<'a> {
    pub fn new(G: &'a GroupElementVector, H: &'a GroupElementVector, g: &'a GroupElement, h: &'a GroupElement,
               V: &'a GroupElement) -> Result<RangeProofProtocol<'a>, ValueError> {
        check_vector_size_for_equality!(G, H)?;
        if !G.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(G.len()))
        }

        let size = G.len();
        let one_vandm_vec = FieldElementVector::new_vandermonde_vector(&FieldElement::from(1), size);
        let two_vandm_vec = FieldElementVector::new_vandermonde_vector(&FieldElement::from(2), size);

        Ok(RangeProofProtocol { G, H, g, h, V, size, one_vandm_vec, two_vandm_vec})
    }

    // Generate a range proof of `v` for randomness `lambda`
    pub fn gen_proof(&self, v: &FieldElement, lambda: &FieldElement) -> Result<RangeProof, ValueError> {
        if v < &FieldElement::zero() {
            return Err(ValueError::NegativeValue(*v.as_bignum()));
        }

        let mut _bitvectors = v.to_bitvectors();
        let mut _a_L = match _bitvectors.len() {
            0 => vec![0],
            1 => _bitvectors.pop().unwrap(),
            _ => panic!("Won't handle numbers greater than 1 limb")
        };

        if _a_L.len() > self.size {
            return Err(ValueError::OutOfRange(_a_L.len()))
        } else if _a_L.len() < self.size {
            _a_L.extend(vec![0; self.size - _a_L.len()])
        }

        let mut state: Vec<u8> = vec![];

        let a_L: FieldElementVector = _a_L.iter().map(| a | FieldElement::from(*a)).collect::<Vec<FieldElement>>().into();
        let a_R = a_L.minus(&self.one_vandm_vec)?;

        // For debugging only, comment in production
        /*let pr = a_L.inner_product(&self.two_pow_vec)?;
        if *v != pr {
            println!("a_L is {:?}", &a_L);
            println!("2n is {:?}", &self.two_pow_vec);
            println!("inner product is {:?}", &pr);
            println!("v is {:?}", &v);
            panic!("value wrongly decomposed to bitvector")
        }*/

        // Commit to vectors `a_L` and `a_R`
        let alpha = FieldElement::random(None);
        let A = commit_to_field_element_vectors(&self.G, &self.H, &self.h, &a_L, &a_R, &alpha)?;

        // Generate blinding vectors `s_L` and `s_R` to blind `a_L` and `a_R` respectively
        let s_L = FieldElementVector::random(self.size, None);
        let s_R = FieldElementVector::random(self.size, None);

        // Commit to vectors `s_L` and `s_R`
        let rho = FieldElement::random(None);
        let S = commit_to_field_element_vectors(&self.G, &self.H, &self.h,
                                                &s_L, &s_R, &rho)?;

        let challenges = gen_challenges(&[&A, &S], &mut state, 2);
        let y = challenges[0];
        let z = challenges[1];

        let z_one: FieldElementVector = vec![z.clone(); self.size].into();
        let z_sqr = z.square();
        let z_sqr_two = self.two_vandm_vec.scaled_by(&z_sqr);
        let y_vandm_vector = FieldElementVector::new_vandermonde_vector(&y, self.size);

        // For debugging only, comment in production
        /*// <a_L, a_R o y^n> = 0
        let ar_yn = a_R.hadamard_product(&y_vandm_vector)?;
        let ip = a_L.inner_product(&ar_yn)?;
        if !FieldElement::is_zero(&ip) {
            panic!("ip is {:?}", &ip);
        }
        // <a_L - 1^n - a_R, y^n> = 0
        let a_L_minus1 = a_L.minus(&self.one_pow_vec)?;
        let a_L_minus1_minus_a_R = a_L_minus1.minus(&a_R)?;
        let ip1 = a_L_minus1_minus_a_R.inner_product(&y_vandm_vector)?;
        if !FieldElement::is_zero(&ip1) {
            panic!("ip1 is {:?}", &ip1);
        }*/

        // Calculate coefficients of l(X), r(X) and t(X)
        // Constant coefficient of polynomial l(X)
        let l_X_const = a_L.minus(&z_one)?;

        // Constant coefficient of polynomial r(X)
        let a_R_plus_z_one = a_R.plus(&z_one)?;
        let y_n_hadmard_a_R_plus_z_one = y_vandm_vector.hadamard_product(&a_R_plus_z_one)?;
        let r_X_const = y_n_hadmard_a_R_plus_z_one.plus(&z_sqr_two)?;
        // Linear coefficient of polynomial r(X)
        let r_X_linear = &y_vandm_vector.hadamard_product(&s_R)?;

        // For debugging only, comment in production
        /*let v_z_sqr = v.multiply(&z_sqr);
        let p1 = z_sqr.multiply(&pr);
        let p2 = z.multiply(&ip1);
        if &add_field_elems!(&p1, &p2, &ip) != &v_z_sqr {
            panic!("v_z_sqr {:?}", &v_z_sqr);
        }
        let t0 = l_X_const.inner_product(&r_X_const)?;
        let delta = self.calc_delta_y_z(&y, &z)?;
        let t00: FieldElement =  add_field_elems!(&v_z_sqr, &delta);
        if t0 != t00 {
            panic!("t0 not equal to v.z^2 + delta(y, z)")
        }*/

        // Linear coefficient of polynomial t(X), `t1`
        let t1_1 = l_X_const.inner_product(&r_X_linear)?;
        let t1_2 = s_L.inner_product(&r_X_const)?;
        let t1 = t1_1 + t1_2;

        // Quadratic coefficient of polynomial t(X), `t2`
        let t2 = s_L.inner_product(&r_X_linear)?;

        // Commit to `t1` and `t2`, as `T1` and `T2`
        let tau1 = FieldElement::random(None);
        let T1 = commit_to_field_element(&self.g, &self.h, &t1, &tau1);
        let tau2 = FieldElement::random(None);
        let T2 = commit_to_field_element(&self.g, &self.h, &t2, &tau2);

        let x = gen_challenges(&[&T1, &T2], &mut state, 1)[0];

        // Compute l(X) and r(X) at `x` as l(x) and r(x)
        let l = l_X_const.plus(&s_L.scaled_by(&x))?;
        let r = r_X_const.plus(&r_X_linear.scaled_by(&x))?;

        // Compute inner product of l(x) and r(x) as t_hat
        let t_hat = l.inner_product(&r)?;

        let x_sqr = x.square();

        // For debugging only, comment in production
        /*let t: FieldElement = add_field_elements!(&t0, &field_elements_multiplication(&x, &t1), &field_elements_multiplication(&x_sqr, &t2));
        if !are_field_elements_equal(&t, &t_hat) {
            panic!("Polynomial evaluation not satisfied")
        }*/

        // Blinding value for t_hat
        let tau2_x_sqr = tau2.multiply(&x_sqr);
        let tau1_x = tau1.multiply(&x);
        let z_sqr_lambda = z_sqr.multiply(lambda);
        let tau_x: FieldElement =  tau2_x_sqr + tau1_x + z_sqr_lambda;

        let mu: FieldElement = alpha + rho.multiply(&x);

        // Compute proof of knowledge for vectors `l` and `r` using the inner product argument

        // Compute another generator for inner product argument
        let u = Self::compute_gen_for_inner_product_arg(&t_hat, &tau_x, &mu, &mut state);
        //println!("During proving, u is {}", &u);

        let H_prime = InnerProductArgument::compute_h_prime(&self.H, &y);

        let g_l = self.G.inner_product_const_time(&l).unwrap();
        let h_r = H_prime.inner_product_const_time(&r).unwrap();
        let u_t_hat = u * t_hat;

        let P = g_l + h_r + u_t_hat;
        let ipa = InnerProductArgument::new(&self.G, &H_prime, &u, &P).unwrap();
        let proof = ipa.gen_proof(&l, &r).unwrap();

        // For debugging only, comment in production
        /*let res = ipa.verify_proof_recursively(&proof)?;
        if !res {
            panic!("Inner product argument proof not verified")
        }*/

        Ok(RangeProof {
            A,
            S,
            T1,
            T2,
            tau_x,
            mu,
            t_hat,
            IPA_proof: proof,
            // `l` and `r` are only for debugging.
            /*l,
            r,*/
        })
    }

    pub fn verify_proof(&self, proof: &RangeProof) -> Result<bool, ValueError> {
        let mut state: Vec<u8> = vec![];

        let challenges = gen_challenges(&[&proof.A, &proof.S], &mut state, 2);
        let y = challenges[0];
        let z = challenges[1];

        let delta = self.calc_delta_y_z(&y, &z)?;
        let z_sqr = z.square();
        let x = gen_challenges(&[&proof.T1, &proof.T2], &mut state, 1)[0];
        let x_sqr = x.square();

        // check that t_hat = t(x) = t0 + t1.x + t2.x^2

        // lhs = g^t_hat.h^tau_x
        let lhs = commit_to_field_element(&self.g, &self.h, &proof.t_hat, &proof.tau_x);

        // rhs = V^(z^2).g^delta.T1^x.T2^(x^2)
        let V_z_sqr = self.V * z_sqr;
        let g_delta = self.g * delta;
        let T1_x = proof.T1 * x;
        let T2_x_sqr = proof.T2 * x_sqr;
        let rhs = V_z_sqr + g_delta + T1_x + T2_x_sqr;

        if lhs != rhs {
            println!("Polynomial evaluation not satisfied");
            return Ok(false)
        }

        // Calculate P = A.S^x.G^-z.H_prime^(z.y^n+z^2.2^n)

        // G^-z
        let G_neg_z = self.G.scaled_by(&z.negation()).sum();

        let H_prime = InnerProductArgument::compute_h_prime(&self.H, &y);

        // H'^(z.y^n+z^2.2^n)

        // z.y^n+z^2.2^n
        let y_vandm_vector = FieldElementVector::new_vandermonde_vector(&y, self.size);
        let z_y_n = y_vandm_vector.scaled_by(&z);
        let z_sqr = z.square();
        let z_sqr_two = self.two_vandm_vec.scaled_by(&z_sqr);
        let exp = z_sqr_two.plus(&z_y_n)?;

        let H_prime_exp = H_prime.inner_product_var_time(&exp)?;

        let P = proof.A + proof.S * x + G_neg_z + H_prime_exp;

        // For debugging only
        /*let h_mu = scalar_point_multiplication(&proof.mu, &self.h);
        let g_l = scalar_point_inner_product(&proof.l, &self.G)?;
        let h_prime_r = scalar_point_inner_product(&proof.r, &H_prime)?;
        let mut s: GroupElement = add_group_elements!(&h_mu, &g_l, &h_prime_r);
        if !s.equals(&mut P) {
            panic!("P not formed correctly");
        }*/

        // Compute P.h^-mu
        let h_neg_mu = self.h  * proof.mu.negation();
        let mut newP = P + h_neg_mu;

        let u = Self::compute_gen_for_inner_product_arg(&proof.t_hat, &proof.tau_x, &proof.mu, &mut state);
        //println!("During verify, u is {}", &u);

        // Compute P.h^-mu.u^t_hat
        let u_t_hat = u * proof.t_hat;
        newP = newP + u_t_hat;

        let ipa = InnerProductArgument::new(&self.G, &H_prime, &u, &newP).unwrap();
        ipa.verify_proof_recursively(&proof.IPA_proof)
    }

    /*// Construct H' = H^(y^-n)
    fn compute_h_prime(&self, y: &FieldElement) -> GroupElementVector {
        let y_inv = field_element_inverse(y);
        let y_inv_pow_vec = field_elem_power_vector(&y_inv, self.size);

        // Construct H' = H^(y^-n)
        let mut H_prime = Vec::with_capacity(self.size);
        for i in 0..self.size {
            H_prime.push(scalar_point_multiplication(&y_inv_pow_vec[i], &self.H[i]));
        }
        H_prime
    }*/

    fn compute_gen_for_inner_product_arg(t_hat: &FieldElement, tau_x: &FieldElement, mu: &FieldElement, state: &mut Vec<u8>) -> GroupElement {
        let gen = GroupElement::generator();
        let input = gen * (t_hat + tau_x + mu);
        let _u = gen_challenges(&[&input], state, 1)[0];
        gen * _u
    }

    fn calc_delta_y_z(&self, y: &FieldElement, z: &FieldElement) -> Result<FieldElement, ValueError>{
        let z_sqr = z.square();
        let z_cube = z_sqr.multiply(&z);

        // `one_two_inner_product` is same as sum of elements of `two_power_vector`
        //let one_two_inner_product = field_elements_inner_product(&self.one_pow_vec, &self.two_pow_vec)?;
        let one_two_inner_product = self.two_vandm_vec.sum();

        let y_vandm_vector = FieldElementVector::new_vandermonde_vector(&y, self.size);
        // `one_y_inner_product` is same as sum of elements of `y_vandm_vector`
        //let one_y_inner_product = field_elements_inner_product(&self.one_pow_vec, &y_vandm_vector)?;
        let one_y_inner_product = y_vandm_vector.sum();

        let z_minus_z_sqr = z.minus(&z_sqr);

        let _1 = z_minus_z_sqr.multiply(&one_y_inner_product);
        let _2 = z_cube.multiply(&one_two_inner_product);
        let delta = _1.minus(&_2);
        Ok(delta)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_range_proof_4() {
        let n = 4;
        let G: GroupElementVector = vec!["g1", "g2", "g3", "g4"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let H: GroupElementVector = vec!["h1", "h2", "h3", "h4"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let g = GroupElement::from_msg_hash("g".as_bytes());
        let h = GroupElement::from_msg_hash("h".as_bytes());

        for i in 0..15 {
            let v = FieldElement::from(i);
            let lambda = FieldElement::random(None);
            let V = commit_to_field_element(&g, &h, &v, &lambda);

            let rpp = RangeProofProtocol::new(&G, &H, &g, &h, &V).unwrap();
            println!("Generate range proof for {}", i);
            let proof = rpp.gen_proof(&v, &lambda).unwrap();
            println!("Proof generated");

            println!("Verify range proof for {}", i);
            assert!(rpp.verify_proof(&proof).unwrap());
            println!("Proof successfully verified");
        }
    }

    // TODO: Refactor tests, remove code duplication
    #[test]
    fn test_range_proof_8() {
        let n = 8;
        let G: GroupElementVector = vec!["g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let H: GroupElementVector = vec!["h1", "h2", "h3", "h4", "h5", "h6", "h7", "h8"].iter().map(| s | GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let g = GroupElement::from_msg_hash("g".as_bytes());
        let h = GroupElement::from_msg_hash("h".as_bytes());

        for i in 0..127 {
            let v = FieldElement::from(i);
            let lambda = FieldElement::random(None);
            let V = commit_to_field_element(&g, &h, &v, &lambda);

            let rpp = RangeProofProtocol::new(&G, &H, &g, &h, &V).unwrap();
            println!("Generate range proof for {}", i);
            let proof = rpp.gen_proof(&v, &lambda).unwrap();
            println!("Proof generated");

            println!("Verify range proof for {}", i);
            assert!(rpp.verify_proof(&proof).unwrap());
            println!("Proof successfully verified");
        }
    }

    #[test]
    fn test_range_proof_bounds() {
        let n = 8;
        let G: GroupElementVector = vec!["g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8"].iter().map(|s| GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let H: GroupElementVector = vec!["h1", "h2", "h3", "h4", "h5", "h6", "h7", "h8"].iter().map(|s| GroupElement::from_msg_hash(s.as_bytes())).collect::<Vec<GroupElement>>().into();
        let g = GroupElement::from_msg_hash("g".as_bytes());
        let h = GroupElement::from_msg_hash("h".as_bytes());


    }
}