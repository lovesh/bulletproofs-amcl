use core::mem;
use merlin::Transcript;
use crate::r1cs::transcript::TranscriptProtocol;

use crate::r1cs::linear_combination::LinearCombination;
use crate::errors::R1CSError;
use crate::r1cs::constraint_system::ConstraintSystem;
use crate::r1cs::linear_combination::Variable;
use crate::r1cs::constraint_system::RandomizedConstraintSystem;
use crate::r1cs::proof::R1CSProof;
use crate::types::GroupG1;
use crate::utils::negate_field_element;
use crate::types::BigNum;
use crate::utils::field_elements_multiplication;
use crate::utils::random_field_element;
use crate::utils::subtract_field_elements;
use crate::utils::field_element_inverse;
use crate::utils::field_elem_power_vector;
use crate::utils::field_element_square;
use crate::utils::field_elements_inner_product;
use crate::inner_product::InnerProductArgument;
use crate::utils::scalar_point_multiplication;
use crate::constants::CurveOrder;
use crate::utils::multi_scalar_multiplication;

type Scalar = BigNum;

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<'a, 'b> {
    G: &'b [GroupG1],
    H: &'b [GroupG1],
    g: &'b GroupG1,
    h: &'b GroupG1,
    transcript: &'a mut Transcript,
    constraints: Vec<LinearCombination>,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<GroupG1>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    deferred_constraints: Vec<Box<Fn(&mut RandomizingVerifier<'a, 'b>) -> Result<(), R1CSError>>>,
}

/// Verifier in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingVerifier<'a, 'b> {
    verifier: Verifier<'a, 'b>,
}

impl<'a, 'b> ConstraintSystem for Verifier<'a, 'b> {
    type RandomizedCS = RandomizingVerifier<'a, 'b>;

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, field_element_neg_one!()));
        right.terms.push((r_var, field_element_neg_one!()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), R1CSError>
        where
            F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
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

impl<'a, 'b> ConstraintSystem for RandomizingVerifier<'a, 'b> {
    type RandomizedCS = Self;

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.verifier.multiply(left, right)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
        where
            F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        self.verifier.allocate(assign_fn)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.verifier.constrain(lc)
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        callback(self)
    }
}

impl<'a, 'b> RandomizedConstraintSystem for RandomizingVerifier<'a, 'b> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.verifier.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Verifier<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(
        G: &'b [GroupG1],
        H: &'b [GroupG1],
        g: &'b GroupG1,
        h: &'b GroupG1,
        transcript: &'a mut Transcript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Verifier {
            G,
            H,
            g,
            h,
            transcript,
            num_vars: 0,
            V: Vec::new(),
            constraints: Vec::new(),
            deferred_constraints: Vec::new(),
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: GroupG1) -> Variable {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript.commit_point(b"V", &commitment);

        Variable::Committed(i)
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let n = self.num_vars;
        let m = self.V.len();

        let mut wL = vec![field_element_zero!(); n];
        let mut wR = vec![field_element_zero!(); n];
        let mut wO = vec![field_element_zero!(); n];
        let mut wV = vec![field_element_zero!(); m];
        let mut wc = field_element_zero!();

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
                        // wc -= exp_z * coeff;
                        let p = field_elements_multiplication(&exp_z, &coeff);
                        wc = subtract_field_elements(&wc, &p);
                    }
                }
            }
            // exp_z *= z;
            exp_z = field_elements_multiplication(&exp_z, &z);
        }

        (wL, wR, wO, wV, wc)
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Note: the wrapper could've used &mut instead of ownership,
        // but specifying lifetimes for boxed closures is not going to be nice,
        // so we move the self into wrapper and then move it back out afterwards.
        let mut callbacks = mem::replace(&mut self.deferred_constraints, Vec::new());
        let mut wrapped_self = RandomizingVerifier { verifier: self };
        for callback in callbacks.drain(..) {
            callback(&mut wrapped_self)?;
        }
        Ok(wrapped_self.verifier)
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    pub fn verify(mut self, proof: &R1CSProof) -> Result<(), R1CSError> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript.commit_u64(b"m", self.V.len() as u64);

        let n1 = self.num_vars;
        self.transcript.commit_point(b"A_I1", &proof.A_I1);
        self.transcript.commit_point(b"A_O1", &proof.A_O1);
        self.transcript.commit_point(b"S1", &proof.S1);

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.num_vars;
        let n2 = n - n1;
        let padded_n = self.num_vars.next_power_of_two();
        let pad = padded_n - n;

        use std::iter;

        if self.G.len() < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        self.transcript.commit_point(b"A_I2", &proof.A_I2);
        self.transcript.commit_point(b"A_O2", &proof.A_O2);
        self.transcript.commit_point(b"S2", &proof.S2);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.transcript.commit_point(b"T_1", &proof.T_1);
        self.transcript.commit_point(b"T_3", &proof.T_3);
        self.transcript.commit_point(b"T_4", &proof.T_4);
        self.transcript.commit_point(b"T_5", &proof.T_5);
        self.transcript.commit_point(b"T_6", &proof.T_6);

        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.commit_scalar(b"t_x", &proof.t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript
            .commit_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.transcript.challenge_scalar(b"w");
        let Q = scalar_point_multiplication(&w, &self.g);

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = field_element_inverse(&y);
        let y_inv_vec = field_elem_power_vector(&y_inv, padded_n);
        let yneg_wR = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| field_elements_multiplication(&wRi, &exp_y_inv))
            .chain(iter::repeat(field_element_zero!()).take(pad))
            .collect::<Vec<Scalar>>();

        let delta = field_elements_inner_product(&yneg_wR[0..n], &wL).unwrap();

        // define parameters for P check
        // Get IPP variables

        let ipa = InnerProductArgument::new(&self.G[0..padded_n], &self.H[0..padded_n], &Q, &proof.P).unwrap();
        let res = ipa.verify_proof_recursively(&proof.ipp_proof).unwrap();
        if !res {
            return Err(R1CSError::VerificationError);
        }
        // Create a `TranscriptRng` from the transcript. The verifier
        // has no witness data to commit, so this just mixes external
        // randomness into the existing transcript.
        let r = random_scalar!();

        let x_sqr = field_element_square(&x);
        let x_cube = field_elements_multiplication(&x, &x_sqr);
        let r_x_sqr = field_elements_multiplication(&r, &x_sqr);

        // group the T_scalars and T_points together
        let T_scalars = [
            field_elements_multiplication(&r, &x),
            field_elements_multiplication(&x, &r_x_sqr),
            field_elements_multiplication(&r_x_sqr, &x_sqr),
            field_elements_multiplication(&r_x_sqr, &x_cube),
            field_elements_multiplication(&r_x_sqr, &field_elements_multiplication(&x_sqr, &x_sqr))
        ];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let mut arg1 = vec![
            x,
            x_sqr,
            x_cube,
            field_elements_multiplication(&u, &x),
            field_elements_multiplication(&u, &x_sqr),
            field_elements_multiplication(&u, &x_cube)
        ];
        arg1.extend(wV.iter().map(|wVi| field_elements_multiplication(&wVi, &r_x_sqr)));
        arg1.extend(&T_scalars);

        // w * (proof.t_x - a * b) + r * (x_sqr * (wc + delta) - proof.t_x)
        arg1.push(add_field_elements!(
            &field_elements_multiplication(
                &w,
                &subtract_field_elements(&proof.t_x, &field_elements_multiplication(&a, &b))),
            &field_elements_multiplication(
                &r,
                &subtract_field_elements(
                    &field_elements_multiplication(&x_sqr, &add_field_elements!(&wc, &delta)),
                    &proof.t_x)
            )
        ));

        // -proof.e_blinding - r * proof.t_x_blinding
        arg1.push(negate_field_element(&add_field_elements!(&proof.e_blinding,
                                                                    &field_elements_multiplication(&r, &proof.t_x_blinding))));

        let mut arg2 = vec![
            proof.A_I1,
            proof.A_O1,
            proof.S1,
            proof.A_I2,
            proof.A_O2,
            proof.S2];

        arg2.extend(&self.V);
        arg2.extend(&T_points);
        arg2.extend(&[*self.g, *self.h]);

        let mut res = multi_scalar_multiplication(&arg1,&arg2).unwrap();
        if !res.is_infinity() {
            return Err(R1CSError::VerificationError);
        }
        /*let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(x) // A_I1
                .chain(iter::once(x_sqr)) // A_O1
                .chain(iter::once(x_cube)) // S1
                .chain(iter::once(u * x)) // A_I2
                .chain(iter::once(u * x_sqr)) // A_O2
                .chain(iter::once(u * x_cube)) // S2
                .chain(wV.iter().map(|wVi| wVi * r_x_sqr)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (x_sqr * (wc + delta) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g_scalars) // G
                .chain(h_scalars) // H
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()), // ipp_proof.R_vec
            iter::once(proof.A_I1.decompress())
                .chain(iter::once(proof.A_O1.decompress()))
                .chain(iter::once(proof.S1.decompress()))
                .chain(iter::once(proof.A_I2.decompress()))
                .chain(iter::once(proof.A_O2.decompress()))
                .chain(iter::once(proof.S2.decompress()))
                .chain(self.V.iter().map(|V_i| V_i.decompress()))
                .chain(T_points.iter().map(|T_i| T_i.decompress()))
                .chain(iter::once(Some(self.pc_gens.B)))
                .chain(iter::once(Some(self.pc_gens.B_blinding)))
                .chain(gens.G(padded_n).map(|&G_i| Some(G_i)))
                .chain(gens.H(padded_n).map(|&H_i| Some(H_i)))
                .chain(proof.ipp_proof.L_vec.iter().map(|L_i| L_i.decompress()))
                .chain(proof.ipp_proof.R_vec.iter().map(|R_i| R_i.decompress())),
        )
            .ok_or_else(|| R1CSError::VerificationError)?;*/


        Ok(())
    }
}
