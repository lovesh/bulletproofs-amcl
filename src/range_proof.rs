use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use super::utils::*;
use crate::utils::commit_to_field_element_vectors;
use crate::inner_product::{InnerProductArgument, InnerProductArgumentProof};
use crate::constants::{GeneratorG1, CurveOrder};

// TODO: Sidechannel resistance. Make sure that range proof for a value with 1 bit set
// takes same time and memory as a value with all bits set.

pub struct RangeProofProtocol<'a> {
    G: &'a [GroupG1],
    H: &'a [GroupG1],
    g: &'a GroupG1,
    h: &'a GroupG1,
    V: &'a GroupG1,
    size: usize,
    one_pow_vec: Vec<BigNum>,
    two_pow_vec: Vec<BigNum>
}

pub struct RangeProof {
    A: GroupG1,
    S: GroupG1,
    T1: GroupG1,
    T2: GroupG1,
    tau_x: BigNum,
    mu: BigNum,
    t_hat: BigNum,
    IPA_proof: InnerProductArgumentProof,
    // `l` and `r` are only for debugging.
    /*l: Vec<BigNum>,
    r: Vec<BigNum>,*/
}

impl<'a> RangeProofProtocol<'a> {
    pub fn new(G: &'a [GroupG1], H: &'a [GroupG1], g: &'a GroupG1, h: &'a GroupG1,
               V: &'a GroupG1) -> Result<RangeProofProtocol<'a>, ValueError> {
        check_vector_size_for_equality!(G, H);
        if !G.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(G.len()))
        }

        let size = G.len();
        let one_pow_vec = field_elem_power_vector(&BigNum::new_int(1), size);
        let two_pow_vec = field_elem_power_vector(&BigNum::new_int(2), size);

        Ok(RangeProofProtocol { G, H, g, h, V, size, one_pow_vec, two_pow_vec})
    }

    // Generate a range proof of `v` for randomness `lambda`
    pub fn gen_proof(&self, v: &BigNum, lambda: &BigNum) -> Result<RangeProof, ValueError> {
        if BigNum::comp(v, &BigNum::new()) == -1 {
            return Err(ValueError::NegativeValue(*v));
        }

        let mut _bitvectors = to_bitvectors(v);
        let mut _a_L = match _bitvectors.len() {
            0 => vec![0],
            1 => _bitvectors.pop().unwrap(),
            _ => panic!("Won't handle numbers greater than 1 limb")
        };

        if _a_L.len() > self.size {
            return Err(ValueError::OutOfRange(_a_L.len()))
        } else if _a_L.len() < self.size {
            _a_L.extend(vec![0; (self.size-_a_L.len())])
        }

        let mut state: Vec<u8> = vec![];

        let a_L: Vec<BigNum> = _a_L.iter().map(| a | BigNum::new_int(*a as isize)).collect();
        let a_R = subtract_field_element_vectors(&a_L, &self.one_pow_vec)?;

        // For debugging only, comment in production
        /*let pr = field_elements_inner_product(&a_L, &self.two_pow_vec)?;
        if !are_field_elements_equal(&v, &pr) {
            println!("a_L is {:?}", &a_L);
            println!("2n is {:?}", &self.two_pow_vec);
            println!("inner product is {:?}", &pr);
            println!("v is {:?}", &v);
            panic!("value wrongly decomposed to bitvector")
        }*/

        // Commit to vectors `a_L` and `a_R`
        let alpha = random_field_element(None);
        let A = commit_to_field_element_vectors(&self.G, &self.H, &self.h, &a_L, &a_R, &alpha)?;

        // Generate blinding vectors `s_L` and `s_R` to blind `a_L` and `a_R` respectively
        let s_L = random_field_vector(self.size, None);
        let s_R = random_field_vector(self.size, None);

        // Commit to vectors `s_L` and `s_R`
        let rho = random_field_element(None);
        let S = commit_to_field_element_vectors(&self.G, &self.H, &self.h,
                                                &s_L, &s_R, &rho)?;

        let challenges = gen_challenges(&[&A, &S], &mut state, 2);
        let y = challenges[0];
        let z = challenges[1];

        let z_one = vec![z.clone(); self.size];
        let z_sqr = field_element_square(&z);
        let z_sqr_two = scale_field_element_vector(&z_sqr, &self.two_pow_vec);
        let y_power_vector = field_elem_power_vector(&y, self.size);

        // For debugging only, comment in production
        /*let ar_yn = field_elements_hadamard_product(&a_R, &y_power_vector)?;
        let ip = field_elements_inner_product(&a_L, &ar_yn)?;
        if !BigNum::iszilch(&ip) {
            panic!("ip is {:?}", &ip);
        }
        let a_L_minus1 = subtract_field_element_vectors(&a_L, &self.one_pow_vec)?;
        let a_L_minus1_minus_a_R = subtract_field_element_vectors(&a_L_minus1, &a_R)?;
        let ip1 = field_elements_inner_product(&a_L_minus1_minus_a_R,
                                               &y_power_vector)?;
        if !BigNum::iszilch(&ip1) {
            panic!("ip1 is {:?}", &ip1);
        }*/

        // Calculate coefficients of l(X), r(X) and t(X)
        // Constant coefficient of polynomial l(X)
        let l_X_const = subtract_field_element_vectors(&a_L, &z_one)?;

        // Constant coefficient of polynomial r(X)
        let a_R_plus_z_one = add_field_element_vectors(&a_R, &z_one)?;
        let y_n_hadmard_a_R_plus_z_one = field_elements_hadamard_product(&y_power_vector, &a_R_plus_z_one)?;
        let r_X_const = add_field_element_vectors(
            &y_n_hadmard_a_R_plus_z_one,
            &z_sqr_two
        )?;
        // Linear coefficient of polynomial r(X)
        let r_X_linear = &field_elements_hadamard_product(&y_power_vector, &s_R)?;

        // For debugging only, comment in production
        /*let v_z_sqr = field_elements_multiplication(v, &z_sqr);
        let p1 = field_elements_multiplication(&z_sqr, &pr);
        let p2 = field_elements_multiplication(&z, &ip1);
        if !are_field_elements_equal(&add_field_elements!(&p1, &p2, &ip), &v_z_sqr) {
            panic!("v_z_sqr {:?}", &v_z_sqr);
        }
        let t0 = field_elements_inner_product(&l_X_const, &r_X_const)?;
        let delta = self.calc_delta_y_z(&y, &z)?;
        let t00: BigNum =  add_field_elements!(&v_z_sqr, &delta);
        if !are_field_elements_equal(&t0, &t00) {
            panic!("t0 not equal to v.z^2 + delta(y, z)")
        }*/

        // Linear coefficient of polynomial t(X), `t1`
        let t1_1 = field_elements_inner_product(&l_X_const, &r_X_linear)?;
        let t1_2 = field_elements_inner_product(&s_L, &r_X_const)?;
        let t1 = add_field_elements!(&t1_1, &t1_2);

        // Quadratic coefficient of polynomial t(X), `t2`
        let t2 = field_elements_inner_product(
            &s_L,
            &r_X_linear
        )?;

        // Commit to `t1` and `t2`, as `T1` and `T2`
        let tau1 = random_field_element(None);
        let T1 = commit_to_field_element(&self.g, &self.h, &t1, &tau1);
        let tau2 = random_field_element(None);
        let T2 = commit_to_field_element(&self.g, &self.h, &t2, &tau2);

        let x = gen_challenges(&[&T1, &T2], &mut state, 1)[0];

        // Compute l(X) and r(X) at `x` as l(x) and r(x)
        let l = add_field_element_vectors(&l_X_const,
                                          &scale_field_element_vector(&x, &s_L))?;
        let r = add_field_element_vectors(&r_X_const,
                                          &scale_field_element_vector(&x, &r_X_linear))?;

        // Compute inner product of l(x) and r(x) as t_hat
        let t_hat = field_elements_inner_product(&l, &r)?;

        let x_sqr = field_element_square(&x);

        // For debugging only, comment in production
        /*let t: BigNum = add_field_elements!(&t0, &field_elements_multiplication(&x, &t1), &field_elements_multiplication(&x_sqr, &t2));
        if !are_field_elements_equal(&t, &t_hat) {
            panic!("Polynomial evaluation not satisfied")
        }*/

        // Blinding value for t_hat
        let tau2_x_sqr = field_elements_multiplication(&tau2, &x_sqr);
        let tau1_x = field_elements_multiplication(&tau1, &x);
        let z_sqr_lambda = field_elements_multiplication(&z_sqr, lambda);
        let tau_x: BigNum = add_field_elements!(&tau2_x_sqr, &tau1_x, &z_sqr_lambda);

        let mu: BigNum = add_field_elements!(&alpha, &field_elements_multiplication(&rho, &x));

        // Compute proof of knowledge for vectors `l` and `r` using the inner product argument

        // Compute another generator for inner product argument
        let u = Self::compute_gen_for_inner_product_arg(&t_hat, &tau_x, &mu, &mut state);
        //println!("During proving, u is {}", &u);

        let H_prime = self.compute_h_prime(&y);

        let g_l = scalar_point_inner_product(&l, &self.G).unwrap();
        let h_r = scalar_point_inner_product(&r, &H_prime).unwrap();
        let u_t_hat = scalar_point_multiplication(&t_hat, &u);

        let P = add_group_elements!(&g_l, &h_r, &u_t_hat);
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
        let z_sqr = field_element_square(&z);
        let x = gen_challenges(&[&proof.T1, &proof.T2], &mut state, 1)[0];
        let x_sqr = field_element_square(&x);

        // check that t_hat = t(x) = t0 + t1.x + t2.x^2

        // lhs = g^t_hat.h^tau_x
        let mut lhs = commit_to_field_element(&self.g, &self.h, &proof.t_hat, &proof.tau_x);

        // rhs = V^(z^2).g^delta.T1^x.T2^(x^2)
        let V_z_sqr = scalar_point_multiplication(&z_sqr, &self.V);
        let g_delta = scalar_point_multiplication(&delta, &self.g);
        let T1_x = scalar_point_multiplication(&x, &proof.T1);
        let T2_x_sqr = scalar_point_multiplication(&x_sqr, &proof.T2);
        let mut rhs = add_group_elements!(&V_z_sqr, &g_delta, &T1_x, &T2_x_sqr);

        if !lhs.equals(&mut rhs) {
            println!("Polynomial evaluation not satisfied");
            return Ok(false)
        }

        // Calculate P = A.S^x.G^-z.H_prime^(z.y^n+z^2.2^n)

        // G^-z
        let neg_z = BigNum::modneg(&z, &CurveOrder);
        let _G_neg_z = scale_group_element_vector(&neg_z, &self.G);
        let G_neg_z = sum_group_elem_vector(&_G_neg_z);

        let H_prime = self.compute_h_prime(&y);

        // H'^(z.y^n+z^2.2^n)

        // z.y^n+z^2.2^n
        let y_power_vector = field_elem_power_vector(&y, self.size);
        let z_y_n = scale_field_element_vector(&z, &y_power_vector);
        let z_sqr = field_element_square(&z);
        let z_sqr_two = scale_field_element_vector(&z_sqr, &self.two_pow_vec);
        let exp = add_field_element_vectors(&z_y_n, &z_sqr_two)?;

        let H_prime_exp = scalar_point_inner_product(&exp, &H_prime)?;

        let P = add_group_elements!(&proof.A, &scalar_point_multiplication(&x, &proof.S), &G_neg_z, &H_prime_exp);

        // For debugging only
        /*let h_mu = scalar_point_multiplication(&proof.mu, &self.h);
        let g_l = scalar_point_inner_product(&proof.l, &self.G)?;
        let h_prime_r = scalar_point_inner_product(&proof.r, &H_prime)?;
        let mut s: GroupG1 = add_group_elements!(&h_mu, &g_l, &h_prime_r);
        if !s.equals(&mut P) {
            panic!("P not formed correctly");
        }*/

        // Compute P.h^-mu
        let neg_mu = BigNum::modneg(&proof.mu, &CurveOrder);
        let h_neg_mu = scalar_point_multiplication(&neg_mu, &self.h);
        let mut newP = add_group_elements!(&P, &h_neg_mu);

        let u = Self::compute_gen_for_inner_product_arg(&proof.t_hat, &proof.tau_x, &proof.mu, &mut state);
        //println!("During verify, u is {}", &u);

        // Compute P.h^-mu.u^t_hat
        let u_t_hat = scalar_point_multiplication(&proof.t_hat, &u);
        newP = add_group_elements!(&newP, &u_t_hat);

        let ipa = InnerProductArgument::new(&self.G, &H_prime, &u, &newP).unwrap();
        ipa.verify_proof_recursively(&proof.IPA_proof)
    }

    // Construct H' = H^(y^-n)
    fn compute_h_prime(&self, y: &BigNum) -> Vec<GroupG1> {
        let y_inv = field_element_inverse(y);
        let y_inv_pow_vec = field_elem_power_vector(&y_inv, self.size);

        // Construct H' = H^(y^-n)
        let mut H_prime = Vec::with_capacity(self.size);
        for i in 0..self.size {
            H_prime.push(scalar_point_multiplication(&y_inv_pow_vec[i], &self.H[i]));
        }
        H_prime
    }

    fn compute_gen_for_inner_product_arg(t_hat: &BigNum, tau_x: &BigNum, mu: &BigNum, state: &mut Vec<u8>) -> GroupG1 {
        let _u = gen_challenges(&[
            &(scalar_point_multiplication(&t_hat, &GeneratorG1)),
            &(scalar_point_multiplication(&tau_x, &GeneratorG1)),
            &(scalar_point_multiplication(&mu, &GeneratorG1)),
        ], state, 1)[0];
        scalar_point_multiplication(&_u, &GeneratorG1)
    }

    fn calc_delta_y_z(&self, y: &BigNum, z: &BigNum) -> Result<BigNum, ValueError>{
        let z_sqr = field_element_square(&z);
        let z_cube = field_elements_multiplication(&z, &z_sqr);

        // `one_two_inner_product` is same as sum of elements of `two_power_vector`
        //let one_two_inner_product = field_elements_inner_product(&self.one_pow_vec, &self.two_pow_vec)?;
        let one_two_inner_product = sum_field_elem_vector(&self.two_pow_vec);

        let y_power_vector = field_elem_power_vector(&y, self.size);
        // `one_y_inner_product` is same as sum of elements of `y_power_vector`
        //let one_y_inner_product = field_elements_inner_product(&self.one_pow_vec, &y_power_vector)?;
        let one_y_inner_product = sum_field_elem_vector(&y_power_vector);

        let z_minus_z_sqr = subtract_field_elements(&z, &z_sqr);

        let _1 = field_elements_multiplication(&z_minus_z_sqr, &one_y_inner_product);
        let _2 = field_elements_multiplication(&z_cube, &one_two_inner_product);
        let delta = subtract_field_elements(&_1, &_2);
        Ok(delta)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::hash_on_GroupG1;

    #[test]
    fn test_range_proof_4() {
        let n = 4;
        let G: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let H: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        for i in 0..15 {
            let v = BigNum::new_int(i);
            let lambda = random_field_element(None);
            let V = commit_to_field_element(&g, &h, &v, &lambda);

            let rpp = RangeProofProtocol::new(G.as_slice(), H.as_slice(), &g, &h, &V).unwrap();
            println!("Generate range proof for {}", i);
            let proof = rpp.gen_proof(&v, &lambda).unwrap();
            println!("Proof generated");

            println!("Verify range proof for {}", i);
            assert!(rpp.verify_proof(&proof).unwrap());
            println!("Proof successfully verified");
        }
    }

    // TODO: Refactor test, remove code duplication
    #[test]
    fn test_range_proof_8() {
        let n = 8;
        let G: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let H: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4", "h5", "h6", "h7", "h8"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        for i in 0..127 {
            let v = BigNum::new_int(i);
            let lambda = random_field_element(None);
            let V = commit_to_field_element(&g, &h, &v, &lambda);

            let rpp = RangeProofProtocol::new(G.as_slice(), H.as_slice(), &g, &h, &V).unwrap();
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
        let G: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8"].iter().map(|s| hash_on_GroupG1(s.as_bytes())).collect();
        let H: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4", "h5", "h6", "h7", "h8"].iter().map(|s| hash_on_GroupG1(s.as_bytes())).collect();
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());


    }
}