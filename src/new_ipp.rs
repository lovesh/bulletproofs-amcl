use merlin::Transcript;
use crate::transcript::TranscriptProtocol;
use crate::inner_product::InnerProductArgumentProof;
use crate::utils::field_elem::{FieldElement, FieldElementVector};
use crate::utils::group_elem::{GroupElement, GroupElementVector};
use core::iter;
use crate::errors::R1CSError;
use crate::constants::CurveOrder;

pub struct NewIPP {}
impl NewIPP {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create_ipp(
        transcript: &mut Transcript,
        Q: &GroupElement,
        G_factors: &FieldElementVector,
        H_factors: &FieldElementVector,
        G_vec: &GroupElementVector,
        H_vec: &GroupElementVector,
        a_vec: &FieldElementVector,
        b_vec: &FieldElementVector,
    ) -> InnerProductArgumentProof {

        let mut n = G_vec.len();

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        // All of the input vectors must have the same length.
        assert_eq!(H_vec.len(), n);
        assert_eq!(a_vec.len(), n);
        assert_eq!(b_vec.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = G_vec.clone();
        let mut H = H_vec.clone();
        let mut a = a_vec.clone();
        let mut b = b_vec.clone();

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = GroupElementVector::with_capacity(lg_n);
        let mut R_vec = GroupElementVector::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n = n / 2;
            let (mut a_L, a_R) = a.split_at(n);
            let (mut b_L, b_R) = b.split_at(n);
            let (mut G_L, G_R) = G.split_at(n);
            let (mut H_L, H_R) = H.split_at(n);
            let (G_factors_L, G_factors_R) = G_factors.split_at(n);
            let (H_factors_L, H_factors_R) = H_factors.split_at(n);

            let c_L = a_L.inner_product(&b_R).unwrap();
            let c_R = a_R.inner_product(&b_L).unwrap();

            let mut L_0 = vec![];
            L_0.extend(a_L.inner_product(&G_factors_R));
            L_0.extend(b_R.inner_product(&H_factors_L));
            L_0.push(c_L);

            let mut L_1 = vec![];
            L_1.extend(&G_R);
            L_1.extend(&H_L);
            L_1.push(Q.clone());

            let L = GroupElementVector::from(L_1).multi_scalar_mul_const_time(&L_0.into()).unwrap();

            let mut R_0 = vec![];
            R_0.extend(a_R.inner_product(&G_factors_L));
            R_0.extend(b_L.inner_product(&H_factors_R));
            R_0.push(c_R);

            let mut R_1 = vec![];
            R_1.extend(&G_L);
            R_1.extend(&H_R);
            R_1.push(Q.clone());

            let R = GroupElementVector::from(R_1).multi_scalar_mul_const_time(&R_0.into()).unwrap();

            L_vec.push(L);
            R_vec.push(R);

            transcript.commit_point(b"L", &L);
            transcript.commit_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = (u_inv * G_factors_L[i])*G_L[i] + (u * G_factors_R[i])* G_R[i];
                H_L[i] = (u * H_factors_L[i])*H_L[i] + (u_inv * H_factors_R[i])*H_R[i];
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n = n / 2;
            let (mut a_L, a_R) = a.split_at(n);
            let (mut b_L, b_R) = b.split_at(n);
            let (mut G_L, G_R) = G.split_at(n);
            let (mut H_L, H_R) = H.split_at(n);

            let c_L = a_L.inner_product(&b_R).unwrap();
            let c_R = a_R.inner_product(&b_L).unwrap();

            let mut L_1 = vec![];
            L_1.extend(&G_R);
            L_1.extend(&H_L);
            L_1.push(Q.clone());
            let mut L_0 = vec![];
            L_0.extend(&a_L);
            L_0.extend(&b_R);
            L_0.push(c_L);

            let L = GroupElementVector::from(L_1).multi_scalar_mul_const_time(&L_0.into()).unwrap();

            let mut R_1 = vec![];
            R_1.extend(&G_L);
            R_1.extend(&H_R);
            R_1.push(Q.clone());
            let mut R_0 = vec![];
            R_0.extend(&a_R);
            R_0.extend(&b_L);
            R_0.push(c_R);

            let R = GroupElementVector::from(R_1).multi_scalar_mul_const_time(&R_0.into()).unwrap();

            L_vec.push(L);
            R_vec.push(R);

            transcript.commit_point(b"L", &L);
            transcript.commit_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = (u_inv * G_L[i]) + (u * G_R[i]);
                H_L[i] = (u * H_L[i]) + (u_inv * H_R[i]);
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductArgumentProof {
            L: L_vec,
            R: R_vec,
            a: a[0],
            b: b[0],
        }
    }

    pub fn verify_ipp(
        n: usize,
        transcript: &mut Transcript,
        G_factors: &[FieldElement],
        H_factors: &[FieldElement],
        P: &GroupElement,
        Q: &GroupElement,
        G: &[GroupElement],
        H: &[GroupElement],
        a: &FieldElement,
        b: &FieldElement,
        L_vec: &[GroupElement],
        R_vec: &[GroupElement],
    ) -> Result<(), R1CSError>
    {
        let (u_sq, u_inv_sq, s) = Self::verification_scalars(&L_vec, &R_vec, n, transcript).unwrap();

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| field_elements_multiplication(&field_elements_multiplication(&a, &s_i), &g_i))
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| field_elements_multiplication(&field_elements_multiplication(&b, &s_i_inv), &h_i));

        let neg_u_sq = u_sq.iter().map(|ui| negate_field_element(&ui));
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| negate_field_element(&ui));

        let _1: Vec<BigNum> = iter::once(field_elements_multiplication(&a, &b))
            .chain(g_times_a_times_s)
            .chain(h_times_b_div_s)
            .chain(neg_u_sq)
            .chain(neg_u_inv_sq).collect();

        let mut _2: Vec<GroupElement> = vec![];
        _2.push(*Q);
        _2.extend(G);
        _2.extend(H);
        _2.extend(L_vec);
        _2.extend(R_vec);

        let mut expect_P = multi_scalar_multiplication(
            &_1,
            &_2,
        ).unwrap();

        if expect_P.equals(&mut P.clone()) {
            Ok(())
        } else {
            Err(R1CSError::VerificationError)
        }
    }

    pub fn verification_scalars(L_vec: &[GroupElement], R_vec: &[GroupElement], n: usize,
                                transcript: &mut Transcript) -> Result<(Vec<FieldElement>, Vec<FieldElement>, Vec<FieldElement>), R1CSError> {
        let lg_n = L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(R1CSError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(R1CSError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in L_vec.iter().zip(R_vec.iter()) {
            transcript.commit_point(b"L", L);
            transcript.commit_point(b"R", R);
            let u = transcript.challenge_scalar(b"u");
            challenges.push(u);
        }

        // 2. Compute u_k^2...u_1^2, 1/(u_k...u_1), 1/u_k^2, ..., 1/u_1^2

        let mut challenges_sq = Vec::with_capacity(lg_n);
        let mut challenges_inv_sq = Vec::with_capacity(lg_n);
        let mut product_chal_inv = field_element_one!();
        for c in &challenges {
            let inv = field_element_inverse(c);
            challenges_sq.push(field_element_square(c));
            challenges_inv_sq.push(field_element_square(&inv));
            product_chal_inv = field_elements_multiplication(&product_chal_inv, &inv);
        }

        // 3. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.push(product_chal_inv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(field_elements_multiplication(&s[i - k], &u_lg_i_sq));
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use crate::utils::hash_on_GroupG1;
    use crate::utils::get_generators;
    use crate::types::BigNum;
    use crate::utils::random_field_element;
    use crate::utils::field_elem_power_vector;

    #[test]
    fn test_ipp() {
        let n = 4;
        let G = get_generators("g", n);
        let H = get_generators("h", n);
        let Q = hash_on_GroupG1("Q".as_bytes());

        let a: Vec<BigNum> = vec![1, 2, 3, 4].iter().map(| i | BigNum::new_int(*i as isize)).collect();
        let b: Vec<BigNum> = vec![5, 6, 7, 8].iter().map(| i | BigNum::new_int(*i as isize)).collect();

        let G_factors: Vec<FieldElement> = iter::repeat(BigNum::new_int(1)).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = BigNum::new_int(1);//random_field_element(None);
        let H_factors: Vec<FieldElement> = field_elem_power_vector(&y_inv, n);

        let mut new_trans = Transcript::new(b"innerproduct");
        let ipp_proof = NewIPP::create_ipp(
            &mut new_trans,
            &Q,
            &G_factors,
            &H_factors,
            &G,
            &H,
            &a,
            &b,
        );

        let b_prime: Vec<FieldElement> = b.iter().zip(H_factors.iter()).map(|(bi, yi)| field_elements_multiplication(&bi, &yi)).collect();
        let c = field_elements_inner_product(&a, &b).unwrap();
        let mut _1 = vec![];
        _1.extend(&a);
        _1.extend(&b_prime);
        _1.push(c);
        let mut _2 = vec![];
        _2.extend(&G);
        _2.extend(&H);
        _2.push(Q);
        let P = multi_scalar_multiplication(
            &_1,
            &_2,
        ).unwrap();

        let mut new_trans1 = Transcript::new(b"innerproduct");
        NewIPP::verify_ipp(n, &mut new_trans1, &G_factors, &H_factors,
                         &P, &Q, &G, &H, &ipp_proof.a, &ipp_proof.b, &ipp_proof.L, &ipp_proof.R).unwrap();
    }
}