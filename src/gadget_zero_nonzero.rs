extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;

use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};

/// if x == 0 then y = 0 else y = 1
/// if x != 0 then inv = x^-1 else inv = 0
/// x*(1-y) = 0
/// x*inv = y
/// The idea is described in the Pinocchio paper and i first saw it in https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/isnonzero.cpp

/// Enforces that x is 0.
pub fn is_zero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedScalar
) -> Result<(), R1CSError> {
    let y: u32 = 0;
    let inv: u32 = 0;

    let x_lc: LinearCombination = vec![(x.variable, Scalar::one())].iter().collect();
    let one_minus_y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(1-y))].iter().collect();
    let y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(y))].iter().collect();
    let inv_lc: LinearCombination = vec![(Variable::One(), Scalar::from(inv))].iter().collect();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * inv = y
    let (_, _, o2) = cs.multiply(x_lc, inv_lc);
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}

/// Enforces that x is 0. Takes x and the inverse of x.
pub fn is_nonzero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedScalar,
    x_inv: AllocatedScalar,
) -> Result<(), R1CSError> {
    let x_lc = LinearCombination::from(x.variable);
    let y_lc = LinearCombination::from(Scalar::one());
    let one_minus_y_lc = LinearCombination::from(Variable::One()) - y_lc.clone();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * x_inv = y
    let inv_lc: LinearCombination = vec![(x_inv.variable, Scalar::one())].iter().collect();
    let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn test_is_zero_non_zero() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // To prove/verify value == 0, set y = 0 and inv = 0
        // To prove/verify value != 0, set y = 1 and inv = value^-1

        let mut rng = rand::thread_rng();

        {
            let inv = 0;
            let y = 0;

            let (proof, commitment) = {
                let value = Scalar::zero();
                let mut prover_transcript = Transcript::new(b"ZeroTest");
                let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

                let (com_val, var_val) = prover.commit(value.clone(), Scalar::random(&mut rng));
                let alloc_scal = AllocatedScalar {
                    variable: var_val,
                    assignment: Some(value),
                };
                assert!(is_zero_gadget(&mut prover, alloc_scal).is_ok());

                let proof = prover.prove(&bp_gens).unwrap();

                (proof, com_val)
            };

            let mut verifier_transcript = Transcript::new(b"ZeroTest");
            let mut verifier = Verifier::new(&mut verifier_transcript);
            let var_val = verifier.commit(commitment);
            let alloc_scal = AllocatedScalar {
                variable: var_val,
                assignment: None,
            };

            assert!(is_zero_gadget(&mut verifier, alloc_scal).is_ok());

            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        }

        {
            let (proof, commitments) = {

                let value = Scalar::random(&mut rng);
                let inv = value.invert();
                let mut prover_transcript = Transcript::new(b"NonZeroTest");
                let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

                let (com_val, var_val) = prover.commit(value.clone(), Scalar::random(&mut rng));
                let alloc_scal = AllocatedScalar {
                    variable: var_val,
                    assignment: Some(value),
                };

                let (com_val_inv, var_val_inv) = prover.commit(inv.clone(), Scalar::random(&mut rng));
                let alloc_scal_inv = AllocatedScalar {
                    variable: var_val_inv,
                    assignment: Some(inv),
                };
                assert!(is_nonzero_gadget(&mut prover, alloc_scal, alloc_scal_inv).is_ok());

                let proof = prover.prove(&bp_gens).unwrap();

                (proof, (com_val, com_val_inv))
            };

            let mut verifier_transcript = Transcript::new(b"NonZeroTest");
            let mut verifier = Verifier::new(&mut verifier_transcript);
            let var_val = verifier.commit(commitments.0);
            let alloc_scal = AllocatedScalar {
                variable: var_val,
                assignment: None,
            };

            let var_val_inv = verifier.commit(commitments.1);
            let alloc_scal_inv = AllocatedScalar {
                variable: var_val_inv,
                assignment: None,
            };

            assert!(is_nonzero_gadget(&mut verifier, alloc_scal, alloc_scal_inv).is_ok());

            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        }
    }
}