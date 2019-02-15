use merlin::Transcript;
use crate::r1cs::transcript::TranscriptProtocol;

use crate::errors::R1CSError;
use crate::r1cs::linear_combination::LinearCombination;
use crate::types::BigNum;
use crate::types::GroupG1;
use crate::constants::CurveOrder;
use crate::r1cs::constraint_system::ConstraintSystem;
use crate::r1cs::linear_combination::Variable;
use crate::r1cs::constraint_system::RandomizedConstraintSystem;
use crate::utils::field_elements_multiplication;
use crate::utils::commit_to_field_element;
use crate::utils::negate_field_element;
use crate::r1cs::proof::R1CSProof;
use core::mem;
use crate::utils::field_element_inverse;
use crate::utils::random_field_element;
use crate::utils::scalar_point_inner_product;
use crate::utils::vector_poly::*;
use crate::utils::get_bytes_for_BigNum;
use crate::utils::field_elem_power_vector;
use crate::utils::subtract_field_elements;
use crate::utils::scalar_point_multiplication;
use crate::inner_product::InnerProductArgument;
use crate::utils::field_elements_inner_product;
use crate::inner_product::InnerProductArgumentProof;
use crate::utils::multi_scalar_multiplication;
use core::iter;
use crate::utils::field_element_square;
use crate::new_ipp::NewIPP;
use crate::utils::commit_to_field_element_vectors;

type Scalar = BigNum;

/// A [`ConstraintSystem`] implementation for use by the prover.
///
/// The prover commits high-level variables and their blinding factors `(v, v_blinding)`,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the proving code calls `prove`
/// which consumes the `Prover` instance, samples random challenges
/// that instantiate the randomized constraints, and creates a complete proof.
pub struct Prover<'a, 'b> {
    G: &'b [GroupG1],
    H: &'b [GroupG1],
    g: &'b GroupG1,
    h: &'b GroupG1,
    transcript: &'a mut Transcript,
    /// The constraints accumulated so far.
    constraints: Vec<LinearCombination>,
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<Scalar>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<Scalar>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<Scalar>,
    /// High-level witness data (value openings to V commitments)
    v: Vec<Scalar>,
    /// High-level witness data (blinding openings to V commitments)
    v_blinding: Vec<Scalar>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    deferred_constraints: Vec<Box<Fn(&mut RandomizingProver<'a, 'b>) -> Result<(), R1CSError>>>,
}

/// Prover in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingProver<'a, 'b> {
    prover: Prover<'a, 'b>,
}

impl<'a, 'b> Prover<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(
        G: &'b [GroupG1],
        H: &'b [GroupG1],
        g: &'b GroupG1,
        h: &'b GroupG1,
        transcript: &'a mut Transcript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Prover {
            G,
            H,
            g,
            h,
            transcript,
            v: Vec::new(),
            v_blinding: Vec::new(),
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            deferred_constraints: Vec::new(),
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitment to the external variable for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a GroupG1 point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, v: Scalar, v_blinding: Scalar) -> (GroupG1, Variable) {
        let i = self.v.len();
        self.v.push(v);
        self.v_blinding.push(v_blinding);

        // Add the commitment to the transcript.
        //let V = self.pc_gens.commit(v, v_blinding).compress();
        let V = commit_to_field_element(&self.g, &self.h, &v, &v_blinding);
        self.transcript.commit_point(b"V", &V);

        (V, Variable::Committed(i))
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![field_element_zero!(); n];
        let mut wR = vec![field_element_zero!(); n];
        let mut wO = vec![field_element_zero!(); n];
        let mut wV = vec![field_element_zero!(); m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        // wL[*i] += exp_z * coeff;
                        let p = field_elements_multiplication(&exp_z, &coeff);
                        wL[*i] = add_field_elements!(&wL[*i], &p);
                    }
                    Variable::MultiplierRight(i) => {
                        // wR[*i] += exp_z * coeff;
                        let p = field_elements_multiplication(&exp_z, &coeff);
                        wR[*i] = add_field_elements!(&wR[*i], &p);
                    }
                    Variable::MultiplierOutput(i) => {
                        // wO[*i] += exp_z * coeff;
                        let p = field_elements_multiplication(&exp_z, &coeff);
                        wO[*i] = add_field_elements!(&wO[*i], &p);
                    }
                    Variable::Committed(i) => {
                        // wV[*i] -= exp_z * coeff;
                        let p = field_elements_multiplication(&exp_z, &coeff);
                        wV[*i] = subtract_field_elements(&wV[*i], &p);
                    }
                    Variable::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            // exp_z *= z;
            exp_z = field_elements_multiplication(&exp_z, &z);
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .fold(BigNum::new(),|sum, (var, coeff)| {
                let val = match var {
                    Variable::MultiplierLeft(i) => self.a_L[*i],
                    Variable::MultiplierRight(i) => self.a_R[*i],
                    Variable::MultiplierOutput(i) => self.a_O[*i],
                    Variable::Committed(i) => self.v[*i],
                    Variable::One() => field_element_one!(),
                };
                // sum + coeff * val
                add_field_elements!(&sum, &field_elements_multiplication(coeff, &val))
            })
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Note: the wrapper could've used &mut instead of ownership,
        // but specifying lifetimes for boxed closures is not going to be nice,
        // so we move the self into wrapper and then move it back out afterwards.
        let mut callbacks = mem::replace(&mut self.deferred_constraints, Vec::new());
        let mut wrapped_self = RandomizingProver { prover: self };
        for callback in callbacks.drain(..) {
            callback(&mut wrapped_self)?;
        }
        Ok(wrapped_self.prover)
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(mut self) -> Result<R1CSProof, R1CSError> {

        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript.commit_u64(b"m", self.v.len() as u64);

        // Commit to the first-phase low-level witness variables.
        let n1 = self.a_L.len();

        if self.G.len() < n1 {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let G_n1: &[GroupG1] = &self.G[0..n1];
        let H_n1: &[GroupG1] = &self.H[0..n1];

        let i_blinding1 = random_scalar!();
        let o_blinding1 = random_scalar!();
        let s_blinding1 = random_scalar!();

        let s_L1: Vec<Scalar> = (0..n1).map(|_| random_scalar!()).collect();
        let s_R1: Vec<Scalar> = (0..n1).map(|_| random_scalar!()).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I1 = commit_to_field_element_vectors(G_n1, H_n1, self.h, &self.a_L, &self.a_R, &i_blinding1).unwrap();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O1 = add_group_elements!(
            &scalar_point_inner_product(&self.a_O, &G_n1).unwrap(),
            &scalar_point_multiplication(&o_blinding1, self.h)
        );

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S1 = commit_to_field_element_vectors(G_n1, H_n1, self.h, &s_L1, &s_R1, &s_blinding1).unwrap();

        self.transcript.commit_point(b"A_I1", &A_I1);
        self.transcript.commit_point(b"A_O1", &A_O1);
        self.transcript.commit_point(b"S1", &S1);

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        // Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.a_L.len();
        let n2 = n - n1;
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        if self.G.len() < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let G_n2: &[GroupG1] = &self.G[n1..n];
        let H_n2: &[GroupG1] = &self.H[n1..n];
        let a_L_n2 = &self.a_L[n1..];
        let a_R_n2 = &self.a_R[n1..];
        let a_O_n2 = &self.a_O[n1..];

        // Commit to the second-phase low-level witness variables

        let i_blinding2 = random_scalar!();
        let o_blinding2 = random_scalar!();
        let s_blinding2 = random_scalar!();

        let s_L2: Vec<Scalar> = (0..n2).map(|_| random_scalar!()).collect();
        let s_R2: Vec<Scalar> = (0..n2).map(|_| random_scalar!()).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I2 = commit_to_field_element_vectors(G_n2, H_n2, self.h, &a_L_n2, &a_R_n2, &i_blinding2).unwrap();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O2 = add_group_elements!(
            &scalar_point_inner_product(&a_O_n2, &G_n2).unwrap(),
            &scalar_point_multiplication(&o_blinding2, self.h)
        );

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S2 = commit_to_field_element_vectors(G_n2, H_n2, self.h, &s_L2, &s_R2, &s_blinding2).unwrap();

        self.transcript.commit_point(b"A_I2", &A_I2);
        self.transcript.commit_point(b"A_O2", &A_O2);
        self.transcript.commit_point(b"S2", &S2);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let mut l_poly = VecPoly3::zero(n);
        let mut r_poly = VecPoly3::zero(n);

        let mut exp_y = field_element_one!(); // y^n starting at n=0
        let y_inv = field_element_inverse(&y);
        let exp_y_inv = field_elem_power_vector(&y_inv, padded_n);

        let sLsR = s_L1
            .iter()
            .chain(s_L2.iter())
            .zip(s_R1.iter().chain(s_R2.iter()));
        for (i, (sl, sr)) in sLsR.enumerate() {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = add_field_elements!(&self.a_L[i], &field_elements_multiplication(&exp_y_inv[i], &wR[i]));
            // l_poly.2 = a_O
            l_poly.2[i] = self.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = *sl;
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = subtract_field_elements(&wO[i], &exp_y);
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = add_field_elements!(&field_elements_multiplication(&exp_y, &self.a_R[i]), &wL[i]);
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = field_elements_multiplication(&exp_y, &sr);

            exp_y = field_elements_multiplication(&exp_y, &y); // y^i -> y^(i+1)
        }

        let t_poly = VecPoly3::special_inner_product(&l_poly, &r_poly);

        let t_1_blinding = random_scalar!();
        let t_3_blinding = random_scalar!();
        let t_4_blinding = random_scalar!();
        let t_5_blinding = random_scalar!();
        let t_6_blinding = random_scalar!();

        let T_1 = commit_to_field_element(&self.g, &self.h, &t_poly.t1, &t_1_blinding);
        let T_3 = commit_to_field_element(&self.g, &self.h, &t_poly.t3, &t_3_blinding);
        let T_4 = commit_to_field_element(&self.g, &self.h, &t_poly.t4, &t_4_blinding);
        let T_5 = commit_to_field_element(&self.g, &self.h, &t_poly.t5, &t_5_blinding);
        let T_6 = commit_to_field_element(&self.g, &self.h, &t_poly.t6, &t_6_blinding);

        self.transcript.commit_point(b"T_1", &T_1);
        self.transcript.commit_point(b"T_3", &T_3);
        self.transcript.commit_point(b"T_4", &T_4);
        self.transcript.commit_point(b"T_5", &T_5);
        self.transcript.commit_point(b"T_6", &T_6);

        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = field_elements_inner_product(&wV, &self.v_blinding).unwrap();

        let t_blinding_poly = Poly6 {
            t1: t_1_blinding,
            t2: t_2_blinding,
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let mut l_vec = l_poly.eval(x);
        l_vec.append(&mut vec![field_element_zero!(); pad]);

        let mut r_vec = r_poly.eval(x);
        r_vec.append(&mut vec![field_element_zero!(); pad]);

        // XXX this should refer to the notes to explain why this is correct
        for i in n..padded_n {
            r_vec[i] = negate_field_element(&exp_y);
            exp_y = field_elements_multiplication(&exp_y, &y); // y^i -> y^(i+1)
        }

        // i_blinding = i_blinding1 + u * i_blinding2
        let i_blinding = add_field_elements!(&i_blinding1, &field_elements_multiplication(&u, &i_blinding2));
        // o_blinding = o_blinding1 + u * o_blinding2;
        let o_blinding = add_field_elements!(&o_blinding1, &field_elements_multiplication(&u, &o_blinding2));
        // s_blinding = s_blinding1 + u * s_blinding2;
        let s_blinding = add_field_elements!(&s_blinding1, &field_elements_multiplication(&u, &s_blinding2));

        // e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding))
        let e_blinding = field_elements_multiplication(
            &x,
            &add_field_elements!(
                &i_blinding,
                &field_elements_multiplication(
                    &x,
                    &add_field_elements!(
                        &o_blinding,
                        &field_elements_multiplication(&x, &s_blinding)
                    )
                )
              )
        );

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = scalar_point_multiplication(&w, &self.g);

        /*let G_l_vec = scalar_point_inner_product(&l_vec, &self.G[0..padded_n]).unwrap();
        let H_r_vec = scalar_point_inner_product(&r_vec, &self.H[0..padded_n]).unwrap();
        let c = field_elements_inner_product(&l_vec, &r_vec).unwrap();
        let Q_c = scalar_point_multiplication(&c, &Q);
        let P = add_group_elements!(&G_l_vec, &H_r_vec, &Q_c);

        let ipa = InnerProductArgument::new(&self.G[0..padded_n], &self.H[0..padded_n], &Q, &P).unwrap();
        let ipp_proof = ipa.gen_proof(&l_vec, &r_vec).unwrap();*/

        let G_factors = iter::repeat(field_element_one!())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad))
            .collect::<Vec<_>>();
        let H_factors = exp_y_inv.clone()
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y, u_or_1)| field_elements_multiplication(&y, &u_or_1))
            .collect::<Vec<_>>();

        //let mut new_trans = Transcript::new(b"innerproduct");
        let ipp_proof = NewIPP::create_ipp(
            self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            &self.G[0..padded_n],
            &self.H[0..padded_n],
            &l_vec,
            &r_vec,
        );

        /*let r_prime: Vec<Scalar> = r_vec.iter().zip(exp_y_inv.iter()).map(|(bi, yi)| field_elements_multiplication(&bi, &yi)).collect();
        let c = field_elements_inner_product(&l_vec, &r_vec).unwrap();
        let mut _1 = vec![];
        _1.extend(&l_vec);
        _1.extend(&r_prime);
        _1.push(c);
        let mut _2 = vec![];
        _2.extend(&self.G[..padded_n]);
        _2.extend(&self.H[..padded_n]);
        _2.push(Q);
        let P = multi_scalar_multiplication(
            &_1,
            &_2,
        ).unwrap();

        let mut new_trans1 = Transcript::new(b"innerproduct");
        Self::verify_ipp(padded_n, &mut new_trans1, &G_factors, &H_factors,
                         &P, &Q, &self.G[..padded_n], &self.H[..padded_n],
                         &ipp_proof.a, &ipp_proof.b, &ipp_proof.L, &ipp_proof.R)?;*/

        Ok(R1CSProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T_1,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            //P
        })
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }
}

impl<'a, 'b> ConstraintSystem for Prover<'a, 'b> {
    type RandomizedCS = RandomizingProver<'a, 'b>;

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        // o = l * r;
        let o = field_elements_multiplication(&l, &r);

        let (l_var, r_var, o_var) = _allocate_vars(self, l, r, o);

        // Constrain l,r,o:
        left.terms.push((l_var, field_element_neg_one!()));
        right.terms.push((r_var, field_element_neg_one!()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
        where
            F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let (l, r, o) = assign_fn()?;

        Ok(_allocate_vars(self, l, r, o))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'a, 'b> ConstraintSystem for RandomizingProver<'a, 'b> {
    type RandomizedCS = Self;

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.prover.multiply(left, right)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
        where
            F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        self.prover.allocate(assign_fn)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.prover.constrain(lc)
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        callback(self)
    }
}

impl<'a, 'b> RandomizedConstraintSystem for RandomizingProver<'a, 'b> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.prover.transcript.challenge_scalar(label)
    }
}

// Allocate variables for l, r and o and assign values
fn _allocate_vars(prover: &mut Prover, l: Scalar, r: Scalar, o: Scalar) -> (Variable, Variable, Variable) {
    // Create variables for l,r,o ...
    let l_var = Variable::MultiplierLeft(prover.a_L.len());
    let r_var = Variable::MultiplierRight(prover.a_R.len());
    let o_var = Variable::MultiplierOutput(prover.a_O.len());
    // ... and assign them
    prover.a_L.push(l);
    prover.a_R.push(r);
    prover.a_O.push(o);

    (l_var, r_var, o_var)
}

