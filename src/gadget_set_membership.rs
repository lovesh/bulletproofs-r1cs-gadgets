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

use crate::r1cs_utils::{AllocatedQuantity, constrain_lc_with_scalar};

// Ensure `v` is a bit, hence 0 or 1
pub fn bit_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity
) -> Result<(), R1CSError> {
    // TODO: Possible to save reallocation of `v` in `bit`?
    let (a, b, o) = cs.allocate_multiplier(v.assignment.map(|bit| {
        ((1 - bit).into(), bit.into())
    }))?;

    // Might not be necessary if above TODO is addressed
    // Variable b is same as v so b + (-v) = 0
    let neg_v: LinearCombination = vec![(v.variable, -Scalar::one())].iter().collect();
    cs.constrain(b + neg_v);

    // Enforce a * b = 0, so one of (a,b) is zero
    cs.constrain(o.into());

    // Might not be necessary if above TODO is addressed
    // Enforce that a = 1 - b, so they both are 1 or 0.
    cs.constrain(a + (b - 1u64));

    Ok(())
}

// Ensure sum of items of `vector` is `sum`
pub fn vector_sum_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vector: &[AllocatedQuantity],
    sum: u64
) -> Result<(), R1CSError> {
    let mut constraints: Vec<(Variable, Scalar)> = vec![(Variable::One(), -Scalar::from(sum))];
    for i in vector {
        constraints.push((i.variable, Scalar::one()));
    }

    cs.constrain(constraints.iter().collect());

    Ok(())
}

// TODO: Find better name for function
// Ensure items[i] * vector[i] = vector[i] * value
pub fn vector_product_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    items: &[u64],
    vector: &[AllocatedQuantity],
    value: &AllocatedQuantity
) -> Result<(), R1CSError> {
    let mut constraints = vec![(value.variable, -Scalar::one())];

    for i in 0..items.len() {

        // TODO: Possible to save reallocation of elements of `vector` in `bit`? If circuit variables for vector are passed, then yes.
        let (bit_var, item_var, o1) = cs.allocate_multiplier(vector[i].assignment.map( |bit| {
            (bit.into(), items[i].into())
        }))?;
        constrain_lc_with_scalar::<CS>(cs, item_var.into(), &items[i].into());

        let (_, _, o2) = cs.multiply(bit_var.into(), value.variable.into());

        cs.constrain(o1 - o2);

        constraints.push((o1, Scalar::one()));

    }

    // Constrain the sum of output variables to be equal to the value of committed variable
    cs.constrain(constraints.iter().collect());

    Ok(())
}


/// Allocate a bitmap for the `set` with 1 as the index of `value`, 0 otherwise. Then commit to values of bitmap
/// and prove that each element is either 0 or 1, sum of elements of this bitmap is 1 (as there is only 1 element)
/// and the relation set[i] * bitmap[i] = bitmap[i] * value.
/// Taken from https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/one_of_n.hpp
pub fn gen_proof_of_set_membership<R: RngCore + CryptoRng>(value: u64, randomness: Option<Scalar>, set: &[u64],
                                                        mut rng: &mut R, transcript_label: &'static [u8],
                                                        pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let set_length = set.len();
    // Set all indices to 0 except the one where `value` is
    let bit_map: Vec<u64> = set.iter().map( | elem | {
        if *elem == value { 1 } else { 0 }
    }).collect();

    let mut comms = vec![];

    let mut prover_transcript = Transcript::new(transcript_label);
    let mut rng = rand::thread_rng();

    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

    let mut bit_vars = vec![];
    for b in bit_map {
        let (com, var) = prover.commit(b.into(), Scalar::random(&mut rng));
        let quantity = AllocatedQuantity {
            variable: var,
            assignment: Some(b),
        };
        assert!(bit_gadget(&mut prover, quantity).is_ok());
        comms.push(com);
        bit_vars.push(quantity);
    }

    // The bit vector sum should be 1
    assert!(vector_sum_gadget(&mut prover, &bit_vars, 1).is_ok());

    let (com_value, var_value) = prover.commit(value.into(), randomness.unwrap_or_else(|| Scalar::random(&mut rng)));
    let quantity_value = AllocatedQuantity {
        variable: var_value,
        assignment: Some(value),
    };
    assert!(vector_product_gadget(&mut prover, &set, &bit_vars, &quantity_value).is_ok());
    comms.push(com_value);

//            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
    let proof = prover.prove(&bp_gens)?;

    Ok((proof, comms))
}

pub fn verify_proof_of_set_membership(set: &[u64],
                                   proof: R1CSProof, commitments: Vec<CompressedRistretto>,
                                   transcript_label: &'static [u8], pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(), R1CSError> {
    let set_length = set.len();

    let mut verifier_transcript = Transcript::new(transcript_label);
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let mut bit_vars = vec![];

    for i in 0..set_length {
        let var = verifier.commit(commitments[i]);
        let quantity = AllocatedQuantity {
            variable: var,
            assignment: None,
        };
        assert!(bit_gadget(&mut verifier, quantity).is_ok());
        bit_vars.push(quantity);
    }

    assert!(vector_sum_gadget(&mut verifier, &bit_vars, 1).is_ok());

    let var_val = verifier.commit(commitments[set_length]);
    let quantity_value = AllocatedQuantity {
        variable: var_val,
        assignment: None,
    };

    assert!(vector_product_gadget(&mut verifier, &set, &bit_vars, &quantity_value).is_ok());

//        println!("Verifier commitments {:?}", &commitments);

    verifier.verify(&proof, &pc_gens, &bp_gens)
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn set_membership_check_gadget() {
        let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
        let value = 3u64;
        let mut rng = rand::thread_rng();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let label= b"SetMemebershipTest";
        let randomness = Some(Scalar::random(&mut rng));
        let (proof, commitments) = gen_proof_of_set_membership(value, randomness, &set, &mut rng, label, &pc_gens, &bp_gens).unwrap();
        verify_proof_of_set_membership(&set, proof, commitments, label, &pc_gens, &bp_gens).unwrap();
    }
}

