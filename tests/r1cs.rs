extern crate bulletproofs_amcl as bulletproofs;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::errors::R1CSError;


#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::types::GroupG1;
    use bulletproofs::utils::hash_on_GroupG1;
    use bulletproofs::utils::random_field_element;
    use bulletproofs::types::BigNum;
    use bulletproofs::r1cs::LinearCombination;

    #[test]
    fn test_factor_r1cs() {
        // Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`
        let G: Vec<GroupG1> = vec!["g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8"].iter().map(|s| hash_on_GroupG1(s.as_bytes())).collect();
        let H: Vec<GroupG1> = vec!["h1", "h2", "h3", "h4", "h5", "h6", "h7", "h8"].iter().map(|s| hash_on_GroupG1(s.as_bytes())).collect();
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        let p = BigNum::new_int(17);
        let q = BigNum::new_int(19);
        let r = BigNum::new_int(323);  // 17*19

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&G, &H, &g, &h, &mut prover_transcript);

            let (com_p, var_p) = prover.commit(p, random_field_element(None));
            let (com_q, var_q) = prover.commit(q, random_field_element(None));

            /*let (a, b, o) = prover.allocate(|| {
                Ok((p, q, r))
            }).unwrap();
            prover.constrain(var_p - a);
            prover.constrain(var_q - b);*/

            let (_, _, o) =  prover.multiply(var_p.into(), var_q.into());
            let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
            prover.constrain(o -  lc);

            let proof = prover.prove().unwrap();

            (proof, (com_p, com_q))
        };

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&G, &H, &g, &h, &mut verifier_transcript);
        let var_p = verifier.commit(commitments.0);
        let var_q = verifier.commit(commitments.1);

        /*let (a, b, o) = verifier.allocate(|| {
            Err(R1CSError::MissingAssignment)
        }).unwrap();
        verifier.constrain(var_p - a);
        verifier.constrain(var_q - b);*/

        let (_, _, o) =  verifier.multiply(var_p.into(), var_q.into());
        let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
        verifier.constrain(o -  lc);

        assert!(verifier.verify(&proof).is_ok());
    }
}