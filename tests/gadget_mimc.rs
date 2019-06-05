extern crate merlin;
extern crate rand;
extern crate flame;
extern crate cpuprofiler;

use bulletproofs_amcl as bulletproofs;
use bulletproofs::utils::field_elem::FieldElement;
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::errors::R1CSError;

use bulletproofs::r1cs::linear_combination::AllocatedQuantity;
use merlin::Transcript;

mod utils;
use utils::mimc::{MIMC_ROUNDS, mimc, mimc_gadget, enforce_mimc_2_inputs};


#[cfg(test)]
mod tests {
    use super::*;
    // For benchmarking
    use std::time::{Duration, Instant};
    //use rand_chacha::ChaChaRng;
    use bulletproofs::utils::get_generators;
    use bulletproofs::utils::group_elem::{G1, GroupElementVector};
    use bulletproofs::utils::field_elem::FieldElement;
    use std::fs::File;
    use cpuprofiler::PROFILER;

    #[test]
    fn test_mimc() {

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| FieldElement::random(None)).collect::<Vec<_>>();
        //let constants = (0..MIMC_ROUNDS).map(|i| FieldElement::one()).collect::<Vec<_>>();

        let G: GroupElementVector = get_generators("G", 128).into();
        let H: GroupElementVector = get_generators("H", 128).into();
        let g =  G1::from_msg_hash("g".as_bytes());
        let h =  G1::from_msg_hash("h".as_bytes());

        const SAMPLES: u32 = 1;
        let mut total_proving = Duration::new(0, 0);
        let mut total_verifying = Duration::new(0, 0);

        for _ in 0..SAMPLES {
            // Generate a random preimage and compute the image
            let xl = FieldElement::random(None);
            let xr = FieldElement::random(None);
            let image = mimc(&xl, &xr, &constants);

            let (proof, commitments) = {
                let mut prover_transcript = Transcript::new(b"MiMC");
                let mut prover = Prover::new(&g, &h, &mut prover_transcript);


                let (com_l, var_l) = prover.commit(xl, FieldElement::random(None));
                let (com_r, var_r) = prover.commit(xr, FieldElement::random(None));

                let left_alloc_scalar = AllocatedQuantity {
                    variable: var_l,
                    assignment: Some(xl),
                };

                let right_alloc_scalar = AllocatedQuantity {
                    variable: var_r,
                    assignment: Some(xr),
                };

                //flame::start("proving");
                PROFILER.lock().unwrap().start("./proving.profile").unwrap();
                let start = Instant::now();
                assert!(mimc_gadget(&mut prover,
                                    left_alloc_scalar,
                                    right_alloc_scalar,
                                    MIMC_ROUNDS,
                                    &constants,
                                    &image).is_ok());

                //println!("For MiMC rounds {}, no of constraints is {}", &MIMC_ROUNDS, &prover.num_constraints());
                let proof = prover.prove(&G, &H).unwrap();
                total_proving += start.elapsed();
                //flame::end("proving");
                PROFILER.lock().unwrap().stop().unwrap();

                (proof, (com_l, com_r))
            };

            let mut verifier_transcript = Transcript::new(b"MiMC");
            let mut verifier = Verifier::new(&mut verifier_transcript);
            let var_l = verifier.commit(commitments.0);
            let var_r = verifier.commit(commitments.1);

            let mut left_alloc_scalar = AllocatedQuantity {
                variable: var_l,
                assignment: None,
            };

            let mut right_alloc_scalar = AllocatedQuantity {
                variable: var_r,
                assignment: None,
            };

            //flame::start("verifying");
            PROFILER.lock().unwrap().start("./verifying.profile").unwrap();
            let start = Instant::now();
            assert!(mimc_gadget(&mut verifier,
                                left_alloc_scalar,
                                right_alloc_scalar,
                                MIMC_ROUNDS,
                                &constants,
                                &image).is_ok());

            assert!(verifier.verify(&proof, &g, &h, &G, &H).is_ok());
            total_verifying += start.elapsed();
            //flame::end("verifying");
            PROFILER.lock().unwrap().stop().unwrap();
        }

        println!("Total proving time for {} samples: {:?} seconds", SAMPLES, total_proving);
        println!("Total verifying time for {} samples: {:?} seconds", SAMPLES, total_verifying);
        flame::dump_html(&mut File::create("flame-graph.html").unwrap()).unwrap();
    }

}
