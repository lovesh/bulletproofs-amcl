use super::types::{BigNum, GroupG1};
use super::errors::ValueError;
use super::utils::{to_bitvectors, subtract_field_element_vectors, random_field_element,
                   scalar_point_inner_product, scalar_point_multiplication, random_field_vector, gen_challenges};
use crate::utils::commit_to_field_element_vectors;
use crate::inner_product::{InnerProductArgument, InnerProductArgumentProof};
use crate::constants::{GeneratorG1, CurveOrder};
use crate::utils::field_element_square;
use crate::utils::field_elements_multiplication;
use crate::utils::field_elements_inner_product;
use crate::utils::field_elem_power_vector;
use crate::utils::scale_field_element_vector;
use crate::utils::add_field_element_vectors;
use crate::utils::field_elements_hadamard_product;
use crate::utils::commit_to_field_element;
use crate::utils::are_field_elements_equal;
use crate::utils::subtract_field_elements;


pub struct RangeProofProtocol<'a> {
    G: &'a [GroupG1],
    H: &'a [GroupG1],
    g: &'a GroupG1,
    h: &'a GroupG1,
    V: &'a GroupG1,
    size: usize
}

pub struct RangeProof {
    A: GroupG1,
    S: GroupG1,
    tau_x: BigNum,
    mu: BigNum,
    t_hat: BigNum,
    IPA_proof: InnerProductArgumentProof
}

impl<'a> RangeProofProtocol<'a> {
    pub fn new(G: &'a [GroupG1], H: &'a [GroupG1], g: &'a GroupG1, h: &'a GroupG1,
               V: &'a GroupG1) -> Result<RangeProofProtocol<'a>, ValueError> {
        if G.len() != G.len() {
            return Err(ValueError::UnequalSizeVectors(G.len(), H.len()))
        }
        if !G.len().is_power_of_two() {
            return Err(ValueError::NonPowerOf2(G.len()))
        }
        Ok(RangeProofProtocol { G, H, g, h, V, size: G.len() })
    }

    // Generate a range proof of `v` for randomness `lambda`
    pub fn gen_proof(&self, v: &BigNum, lambda: &BigNum) -> Result<RangeProof, ValueError> {
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

        // These can be stored in the struct avoiding computing everytime
        let one_power_vector = field_elem_power_vector(&BigNum::new_int(1), self.size);
        let two_power_vector = field_elem_power_vector(&BigNum::new_int(2), self.size);

        let a_L: Vec<BigNum> = _a_L.iter().map(| a | BigNum::new_int(*a as isize)).collect();
        let a_R = subtract_field_element_vectors(&a_L, &one_power_vector)?;

        // For debugging only, comment in production
        let pr = field_elements_inner_product(&a_L, &two_power_vector)?;
        if !are_field_elements_equal(&v, &pr) {
            println!("a_L is {:?}", &a_L);
            println!("2n is {:?}", &two_power_vector);
            println!("inner product is {:?}", &pr);
            println!("v is {:?}", &v);
            panic!("value wrongly decomposed to bitvector")
        }

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
        let y = BigNum::new_int(0);//challenges[0];
        let z = BigNum::new_int(1);//challenges[1];

        let z_one = vec![z.clone(); self.size];
        let z_sqr = field_element_square(&z);
        let z_sqr_two = scale_field_element_vector(&z_sqr, &two_power_vector);
        let y_power_vector = field_elem_power_vector(&y, self.size);

        // For debugging only, comment in production
        let ar_yn = field_elements_hadamard_product(&a_R, &y_power_vector)?;
        let ip = field_elements_inner_product(&a_L, &ar_yn)?;
        if !BigNum::iszilch(&ip) {
            panic!("ip is {:?}", &ip);
        }
        let a_L_minus1 = subtract_field_element_vectors(&a_L, &one_power_vector)?;
        let a_L_minus1_minus_a_R = subtract_field_element_vectors(&a_L_minus1, &a_R)?;
        let ip1 = field_elements_inner_product(&a_L_minus1_minus_a_R,
                                               &y_power_vector)?;
        if !BigNum::iszilch(&ip1) {
            panic!("ip1 is {:?}", &ip1);
        }

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
        let v_z_sqr = field_elements_multiplication(v, &z_sqr);
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
        }

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
        let t: BigNum = add_field_elements!(&t0, &field_elements_multiplication(&x, &t1), &field_elements_multiplication(&x_sqr, &t2));
        if !are_field_elements_equal(&t, &t_hat) {
            panic!("Polynomial evaluation not satisfied")
        }

        // Blinding value for t_hat
        let tau2_x_sqr = field_elements_multiplication(&tau2, &x_sqr);
        let tau1_x = field_elements_multiplication(&tau1, &x);
        let z_sqr_lambda = field_elements_multiplication(&z_sqr, lambda);
        let tau_x: BigNum = add_field_elements!(&tau2_x_sqr, &tau1_x, &z_sqr_lambda);

        let mu: BigNum = add_field_elements!(&alpha, &field_elements_multiplication(&rho, &x));

        // Compute proof of knowledge for vectors `l` and `r` using the inner product argument

        // Compute another generator for inner product argument
        let _u = gen_challenges(&[
            &(scalar_point_multiplication(&t_hat, &GeneratorG1)),
            &(scalar_point_multiplication(&tau_x, &GeneratorG1)),
            &(scalar_point_multiplication(&mu, &GeneratorG1)),
        ], &mut state, 1)[0];
        let u = scalar_point_multiplication(&_u, &GeneratorG1);

        let g_l = scalar_point_inner_product(&l, &self.G).unwrap();
        let h_r = scalar_point_inner_product(&r, &self.H).unwrap();
        let u_t_hat = scalar_point_multiplication(&t_hat, &u);

        let P = add_group_elements!(&g_l, &h_r, &u_t_hat);
        let ipa = InnerProductArgument::new(&self.G, &self.H, &u, &P).unwrap();
        let proof = ipa.gen_proof(&l, &r).unwrap();

        // For debugging only, comment in production
        let res = ipa.verify_proof_recursively(&proof)?;
        if !res {
            panic!("Inner product argument proof not verified")
        }

        Ok(RangeProof {
            A,
            S,
            tau_x,
            mu,
            t_hat,
            IPA_proof: proof
        })
    }

    fn calc_delta_y_z(&self, y: &BigNum, z: &BigNum) -> Result<BigNum, ValueError>{
        let z_sqr = field_element_square(&z);
        let z_cube = field_elements_multiplication(&z, &z_sqr);

        // These can be stored in the struct avoiding computing everytime
        let one_power_vector = field_elem_power_vector(&BigNum::new_int(1), self.size);
        let two_power_vector = field_elem_power_vector(&BigNum::new_int(2), self.size);
        // `one_two_inner_product` is same as sum of elements of `two_power_vector`
        let one_two_inner_product = field_elements_inner_product(&one_power_vector, &two_power_vector)?;

        let y_power_vector = field_elem_power_vector(&y, self.size);
        // `one_y_inner_product` is same as sum of elements of `y_power_vector`
        let one_y_inner_product = field_elements_inner_product(&one_power_vector, &y_power_vector)?;

        /*let mut z_minus_z_sqr = z.clone();
        z_minus_z_sqr.sub(&z_sqr);
        z_minus_z_sqr.rmod(&CurveOrder);*/
        let z_minus_z_sqr = subtract_field_elements(&z, &z_sqr);

        let _1 = field_elements_multiplication(&z_minus_z_sqr, &one_y_inner_product);
        let _2 = field_elements_multiplication(&z_cube, &one_two_inner_product);
        /*_1.sub(&_2);
        _1.rmod(&CurveOrder);*/
        let delta = subtract_field_elements(&_1, &_2);
        Ok(delta)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::hash_on_GroupG1;

    #[test]
    fn test_range_proof() {
        let n = 4;
        let G: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let H: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4"].iter().map(| s | hash_on_GroupG1(s.as_bytes())).collect();
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());
        let v = BigNum::new_int(10);
        let lambda = random_field_element(None);
        let V = commit_to_field_element(&g, &h, &v, &lambda);

        let rpp = RangeProofProtocol::new(G.as_slice(), H.as_slice(), &g, &h, &V).unwrap();
        let proof = rpp.gen_proof(&v, &lambda).unwrap();
    }
}