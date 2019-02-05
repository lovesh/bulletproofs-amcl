use merlin::Transcript;
use crate::r1cs::transcript::TranscriptProtocol;

use crate::errors::R1CSError;
use crate::inner_product::InnerProductArgumentProof;
use crate::r1cs::linear_combination::LinearCombination;
use crate::types::BigNum;
use crate::types::GroupG1;
use crate::constants::CurveOrder;
use crate::r1cs::constraint_system::ConstraintSystem;
use crate::r1cs::linear_combination::Variable;
use crate::r1cs::constraint_system::RandomizedConstraintSystem;
use crate::utils::field_elements_multiplication;
use crate::utils::commit_to_field_element;


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
    transcript: &'a mut Transcript,
    G: &'b [GroupG1],
    H: &'b [GroupG1],
    g: &'b GroupG1,
    h: &'b GroupG1,
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
                        let m = field_elements_multiplication(&exp_z, &coeff);
                        wL[*i] = add_field_elements!(&wL[*i], &m);
                    }
                    Variable::MultiplierRight(i) => {
                        // wR[*i] += exp_z * coeff;
                        let m = field_elements_multiplication(&exp_z, &coeff);
                        wR[*i] = add_field_elements!(&wR[*i], &m);
                    }
                    Variable::MultiplierOutput(i) => {
                        // wO[*i] += exp_z * coeff;
                        let m = field_elements_multiplication(&exp_z, &coeff);
                        wO[*i] = add_field_elements!(&wO[*i], &m);
                    }
                    Variable::Committed(i) => {
                        // wV[*i] -= exp_z * coeff;
                        let m = field_elements_multiplication(&exp_z, &coeff);
                        wV[*i] = add_field_elements!(&wV[*i], &m);
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
            .map(|(var, coeff)| {
                coeff
                    * match var {
                    Variable::MultiplierLeft(i) => self.a_L[*i],
                    Variable::MultiplierRight(i) => self.a_R[*i],
                    Variable::MultiplierOutput(i) => self.a_O[*i],
                    Variable::Committed(i) => self.v[*i],
                    Variable::One() => field_element_one!(),
                }
            })
            .sum()
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

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

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

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        Ok((l_var, r_var, o_var))
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