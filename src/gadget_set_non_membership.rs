extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;
use merlin::Transcript;
use rand::{RngCore, CryptoRng};

use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};
use crate::gadget_zero_nonzero::is_nonzero_gadget;


pub fn set_non_membership_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedScalar,
    diff_vars: Vec<AllocatedScalar>,
    diff_inv_vars: Vec<AllocatedScalar>,
    set: &[u64]
) -> Result<(), R1CSError> {
    let set_length = set.len();

    for i in 0..set_length {
        // Since `diff_vars[i]` is `set[i] - v`, `diff_vars[i]` + `v` should be `set[i]`
        constrain_lc_with_scalar::<CS>(cs, diff_vars[i].variable + v.variable, &Scalar::from(set[i]));

        // Ensure `set[i] - v` is non-zero
        is_nonzero_gadget(cs, diff_vars[i], diff_inv_vars[i])?;
    }

    Ok(())
}

/// Prove that difference between each set element and value is non-zero, hence value does not equal any set element.
pub fn gen_proof_of_set_non_membership<R: RngCore + CryptoRng>(value: u64, randomness: Option<Scalar>, set: &[u64],
                                                             mut rng: &mut R, transcript_label: &'static [u8],
                                                             pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let set_length = set.len();
    let mut comms: Vec<CompressedRistretto> = vec![];
    let mut diff_vars: Vec<AllocatedScalar> = vec![];
    let mut diff_inv_vars: Vec<AllocatedScalar> = vec![];

    let mut prover_transcript = Transcript::new(transcript_label);
    let mut rng = rand::thread_rng();

    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
    let value= Scalar::from(value);
    let (com_value, var_value) = prover.commit(value.clone(), randomness.unwrap_or_else(|| Scalar::random(&mut rng)));
    let alloc_scal = AllocatedScalar {
        variable: var_value,
        assignment: Some(value),
    };
    comms.push(com_value);

    for i in 0..set_length {
        let elem = Scalar::from(set[i]);
        let diff = elem - value;
        let diff_inv = diff.invert();

        // Take difference of set element and value, `set[i] - value`
        let (com_diff, var_diff) = prover.commit(diff.clone(), Scalar::random(&mut rng));
        let alloc_scal_diff = AllocatedScalar {
            variable: var_diff,
            assignment: Some(diff),
        };
        diff_vars.push(alloc_scal_diff);
        comms.push(com_diff);

        // Inverse needed to prove that difference `set[i] - value` is non-zero
        let (com_diff_inv, var_diff_inv) = prover.commit(diff_inv.clone(), Scalar::random(&mut rng));
        let alloc_scal_diff_inv = AllocatedScalar {
            variable: var_diff_inv,
            assignment: Some(diff_inv),
        };
        diff_inv_vars.push(alloc_scal_diff_inv);
        comms.push(com_diff_inv);
    }

    assert!(set_non_membership_gadget(&mut prover, alloc_scal, diff_vars, diff_inv_vars, &set).is_ok());

//            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());

    let proof = prover.prove(&bp_gens)?;

    Ok((proof, comms))
}

pub fn verify_proof_of_set_non_membership(set: &[u64],
                                        proof: R1CSProof, commitments: Vec<CompressedRistretto>,
                                        transcript_label: &'static [u8], pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(), R1CSError> {
    let set_length = set.len();
    let mut verifier_transcript = Transcript::new(transcript_label);
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let mut diff_vars: Vec<AllocatedScalar> = vec![];
    let mut diff_inv_vars: Vec<AllocatedScalar> = vec![];

    let var_val = verifier.commit(commitments[0]);
    let alloc_scal = AllocatedScalar {
        variable: var_val,
        assignment: None,
    };

    for i in 1..set_length+1 {
        let var_diff = verifier.commit(commitments[2*i-1]);
        let alloc_scal_diff = AllocatedScalar {
            variable: var_diff,
            assignment: None,
        };
        diff_vars.push(alloc_scal_diff);

        let var_diff_inv = verifier.commit(commitments[2*i]);
        let alloc_scal_diff_inv = AllocatedScalar {
            variable: var_diff_inv,
            assignment: None,
        };
        diff_inv_vars.push(alloc_scal_diff_inv);
    }

    assert!(set_non_membership_gadget(&mut verifier, alloc_scal, diff_vars, diff_inv_vars, &set).is_ok());

    verifier.verify(&proof, &pc_gens, &bp_gens)
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn set_non_membership_check_gadget() {
        let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
        let value = 10u64;
        let mut rng = rand::thread_rng();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let label= b"SetNonMemebershipTest";
        let randomness = Some(Scalar::random(&mut rng));
        let (proof, commitments) = gen_proof_of_set_non_membership(value, randomness, &set, &mut rng, label, &pc_gens, &bp_gens).unwrap();
        verify_proof_of_set_non_membership(&set, proof, commitments, label, &pc_gens, &bp_gens).unwrap();
    }
}