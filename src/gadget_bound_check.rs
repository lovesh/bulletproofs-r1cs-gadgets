extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;
use merlin::Transcript;
use rand::{RngCore, CryptoRng};

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

    // a = v - min
    // b = max - v
    // a + b = max - min

    cs.constrain(v.variable - LinearCombination::from(min) - a.variable);

    cs.constrain(LinearCombination::from(max) - v.variable - b.variable);

    // Constrain a + b to be same as max - min.
    constrain_lc_with_scalar::<CS>(cs, a.variable + b.variable, &Scalar::from(max - min));

    // Constrain a in [0, 2^n)
    assert!(positive_no_gadget(cs, a, n).is_ok());
    // Constrain b in [0, 2^n)
    assert!(positive_no_gadget(cs, b, n).is_ok());

    Ok(())
}

/// Accepts the num for which the bounds have to proved and optionally the randomness used in committing to that number.
/// This randomness argument is accepted so that this can be used as a sub-protocol where the protocol on upper layer will create the commitment.
pub fn gen_proof_of_bounded_num<R: RngCore + CryptoRng>(val: u64, randomness: Option<Scalar>, lower: u64, upper: u64,
                                max_bits_in_val: usize, mut rng: &mut R, transcript_label: &'static [u8],
                                pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let a = val - lower;
    let b = upper - val;

    let mut comms = vec![];

    // Prover makes a `ConstraintSystem` instance representing a range proof gadget
    let mut prover_transcript = Transcript::new(transcript_label);
    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

    let (com_v, var_v) = prover.commit(val.into(), randomness.unwrap_or_else(|| Scalar::random(&mut rng)));
    let quantity_v = AllocatedQuantity {
        variable: var_v,
        assignment: Some(val),
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

    assert!(bound_check_gadget(&mut prover, quantity_v, quantity_a, quantity_b, upper, lower, max_bits_in_val).is_ok());

    let proof = prover.prove(&bp_gens)?;

    Ok((proof, comms))
}

pub fn verify_proof_of_bounded_num(lower: u64, upper: u64, max_bits_in_val: usize,
                                proof: R1CSProof, commitments: Vec<CompressedRistretto>,
                                transcript_label: &'static [u8], pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(), R1CSError> {
    let mut verifier_transcript = Transcript::new(transcript_label);
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

    assert!(bound_check_gadget(&mut verifier, quantity_v, quantity_a, quantity_b, upper, lower, max_bits_in_val).is_ok());

    verifier.verify(&proof, &pc_gens, &bp_gens)
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn test_bound_check_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let min = 10;
        let max = 100;

        let v = rng.gen_range(min, max);
        println!("v is {}", &v);
        let randomness = Some(Scalar::random(&mut rng));

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // TODO: Use correct bit size of the field
        let n = 32;

        let label = b"BoundsTest";
        let (proof, commitments) = gen_proof_of_bounded_num(v, randomness, min, max, n, &mut rng, label, &pc_gens, &bp_gens).unwrap();

        verify_proof_of_bounded_num(min, max, n, proof, commitments, label, &pc_gens, &bp_gens).unwrap();
    }
}