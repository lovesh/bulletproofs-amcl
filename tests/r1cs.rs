/*
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
    use bulletproofs::utils::get_generators;

    #[test]
    fn test_2_factors_r1cs() {
        // Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`
        let G = get_generators("g", 8);
        let H = get_generators("h", 8);
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        let factors = vec![
            (BigNum::new_int(17), BigNum::new_int(19), BigNum::new_int(323)),
            (BigNum::new_int(7), BigNum::new_int(5), BigNum::new_int(35))
        ];

        let (proof, commitments) = {
            let mut comms = vec![];
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&G, &H, &g, &h, &mut prover_transcript);

            for (p, q, r) in &factors {
                let (com_p, var_p) = prover.commit(*p, random_field_element(None));
                let (com_q, var_q) = prover.commit(*q, random_field_element(None));
                let (_, _, o) =  prover.multiply(var_p.into(), var_q.into());
                let lc: LinearCombination = vec![(Variable::One(), *r)].iter().collect();
                prover.constrain(o -  lc);
                comms.push(com_p);
                comms.push(com_q);
            }

            let proof = prover.prove().unwrap();

            (proof, comms)
        };

        println!("Proving done");

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&G, &H, &g, &h, &mut verifier_transcript);
        let mut i = 0;
        while i < factors.len() {
            let var_p = verifier.commit(commitments[2*i]);
            let var_q = verifier.commit(commitments[2*i+1]);
            let (_, _, o) =  verifier.multiply(var_p.into(), var_q.into());
            let lc: LinearCombination = vec![(Variable::One(), factors[i].2)].iter().collect();
            verifier.constrain(o -  lc);

            i += 1;
        }

        assert!(verifier.verify(&proof).is_ok());
    }

    #[test]
    fn test_factor_r1cs() {
        // Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`
        let G = get_generators("g", 8);
        let H = get_generators("h", 8);
        let g = hash_on_GroupG1("g".as_bytes());
        let h = hash_on_GroupG1("h".as_bytes());

        let factors = vec![
            (BigNum::new_int(2), BigNum::new_int(4), BigNum::new_int(6), BigNum::new_int(48)),
            (BigNum::new_int(7), BigNum::new_int(5), BigNum::new_int(3), BigNum::new_int(105))
        ];

        let (proof, commitments) = {
            let mut comms = vec![];
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&G, &H, &g, &h, &mut prover_transcript);

            for (p, q, r, s) in &factors {
                let (com_p, var_p) = prover.commit(*p, random_field_element(None));
                let (com_q, var_q) = prover.commit(*q, random_field_element(None));
                let (com_r, var_r) = prover.commit(*r, random_field_element(None));
                let (_, _, o1) =  prover.multiply(var_p.into(), var_q.into());
                let (_, _, o2) =  prover.multiply(o1.into(), var_r.into());
                let mut lc: LinearCombination = vec![(Variable::One(), *s)].iter().collect();
                prover.constrain(o2 -  lc);
                comms.push(com_p);
                comms.push(com_q);
                comms.push(com_r);
            }

            let proof = prover.prove().unwrap();

            (proof, comms)
        };

        println!("Proving done");

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&G, &H, &g, &h, &mut verifier_transcript);
        let mut i = 0;
        while i < factors.len() {
            let var_p = verifier.commit(commitments[3*i]);
            let var_q = verifier.commit(commitments[3*i+1]);
            let var_r = verifier.commit(commitments[3*i+2]);
            let (_, _, o1) =  verifier.multiply(var_p.into(), var_q.into());
            let (_, _, o2) =  verifier.multiply(o1.into(), var_r.into());
            let lc: LinearCombination = vec![(Variable::One(), factors[i].3)].iter().collect();
            verifier.constrain(o2 -  lc);

            i += 1;
        }

        assert!(verifier.verify(&proof).is_ok());
    }
}*/
