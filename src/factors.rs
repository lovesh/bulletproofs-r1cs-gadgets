extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;
use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};

pub fn factors<CS: ConstraintSystem>(
    cs: &mut CS,
    p: AllocatedScalar,
    q: AllocatedScalar,
    r: &Scalar,
) -> Result<(), R1CSError> {
    let (_, _, o) =  cs.multiply(p.variable.into(), q.variable.into());
    constrain_lc_with_scalar::<CS>(cs, o.into(), r);
    Ok(())
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use rand::{RngCore, CryptoRng};
    use super::*;
    use curve25519_dalek::ristretto::CompressedRistretto;


    fn prover_prep<R: RngCore + CryptoRng>(prover: &mut Prover, values: Vec<Scalar>, rng: &mut R) -> (Vec<CompressedRistretto>, Vec<AllocatedScalar>) {
        let mut commitments = vec![];
        let mut allocations = vec![];
        for v in values {
            let (com, var) = prover.commit(v.clone(), Scalar::random(rng));
            commitments.push(com);
            allocations.push(AllocatedScalar {
                variable: var,
                assignment: Some(v)
            });
        }
        (commitments, allocations)
    }

    //fn create_proof_and_verify(prover: &mut Prover, verifier: &mut Verifier)

    #[test]
    fn test_factor_r1cs() {
        // Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`

        // TODO: Prove that neither `p` or `q` is 1, this can be done range proof gadget or using the `not_equals_gadget`
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let (p, q, r) = (17u64, 19u64, 323u64);
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut rng = rand::thread_rng();

            let (p, q, r) = (Scalar::from(p), Scalar::from(q), Scalar::from(r));

            let (com_p, var_p) = prover.commit(p.clone(), Scalar::random(&mut rng));
            let (com_q, var_q) = prover.commit(q.clone(), Scalar::random(&mut rng));

            assert!(factors(
                &mut prover,
                AllocatedScalar {
                    variable: var_p,
                    assignment: Some(p),
                },
                AllocatedScalar {
                    variable: var_q,
                    assignment: Some(q),
                },
                &r
            ).is_ok());

            let proof = prover.prove(&bp_gens).unwrap();

            (proof, (com_p, com_q))
        };

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_p = verifier.commit(commitments.0);
        let var_q = verifier.commit(commitments.1);

        assert!(factors(
            &mut verifier,
            AllocatedScalar {
                variable: var_p,
                assignment: None,
            },
            AllocatedScalar {
                variable: var_q,
                assignment: None,
            },
            &Scalar::from(r)
        ).is_ok());
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}