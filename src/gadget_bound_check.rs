extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;

use crate::r1cs_utils::{AllocatedQuantity, positive_no_gadget, constrain_lc_with_scalar};


pub fn bound_check_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    a: AllocatedQuantity,
    b: AllocatedQuantity,
    max: u64,
    min: u64,
    n: usize
) -> Result<(), R1CSError> {

    // a + b = max - min
    // Constrain a + b to be same as max - min.
    constrain_lc_with_scalar::<CS>(cs, a.variable + b.variable, &Scalar::from(max - min));

    // Constrain a in [0, 2^n)
    assert!(positive_no_gadget(cs, a, n).is_ok());
    // Constrain b in [0, 2^n)
    assert!(positive_no_gadget(cs, b, n).is_ok());

    Ok(())
}


#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn test_bound_check_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng = OsRng::new().unwrap();
        let min = 10;
        let max = 100;

        let v = rng.gen_range(min, max);
        println!("v is {}", &v);
        assert!(bound_check_helper(v, min, max).is_ok());
    }

    fn bound_check_helper(v: u64, min: u64, max: u64) -> Result<(), R1CSError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // TODO: Use correct bit size of the field
        let n = 32;

        let (proof, commitments) = {
            let a = v - min;
            let b = max - v;

            let mut comms = vec![];

            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"BoundsTest");
            let mut rng = rand::thread_rng();
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let (com_v, var_v) = prover.commit(v.into(), Scalar::random(&mut rng));
            let quantity_v = AllocatedQuantity {
                variable: var_v,
                assignment: Some(v),
            };
            comms.push(com_v);

            let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
            let quantity_a = AllocatedQuantity {
                variable: var_a,
                assignment: Some(a),
            };
            comms.push(com_a);

            let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
            let quantity_b = AllocatedQuantity {
                variable: var_b,
                assignment: Some(b),
            };
            comms.push(com_b);

            assert!(bound_check_gadget(&mut prover, quantity_v, quantity_a, quantity_b, max, min, n).is_ok());

            let proof = prover.prove(&bp_gens)?;

            (proof, comms)
        };

        let mut verifier_transcript = Transcript::new(b"BoundsTest");
        let mut verifier = Verifier::new(&mut verifier_transcript);

        let var_v = verifier.commit(commitments[0]);
        let quantity_v = AllocatedQuantity {
            variable: var_v,
            assignment: None,
        };

        let var_a = verifier.commit(commitments[1]);
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: None,
        };

        let var_b = verifier.commit(commitments[2]);
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: None,
        };

        assert!(bound_check_gadget(&mut verifier, quantity_v, quantity_a, quantity_b, max, min, n).is_ok());

        Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
    }
}