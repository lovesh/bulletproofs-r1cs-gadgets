extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;
use std::cmp;

use crate::r1cs_utils::{AllocatedQuantity, positive_no_gadget, constrain_lc_with_scalar};

/*struct PositiveNoGadget {}

impl PositiveNoGadget {
    fn constrain<CS: ConstraintSystem>(
        cs: &mut CS,
        v: AllocatedQuantity,
        n: usize,
    ) -> Result<(), R1CSError> {
        let mut constraint = vec![(v.variable, -Scalar::one())];
        let mut exp_2 = Scalar::one();
        for i in 0..n {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate(|| {
                let q: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
                //println!("q is {}", &q);
                let bit: u64 = (q >> i) & 1;
                Ok(((1 - bit).into(), bit.into(), Scalar::zero()))
            })?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - 1u64));

            constraint.push((b, exp_2)  );
            exp_2 = exp_2 + exp_2;
        }

        // Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
        cs.constrain(constraint.iter().collect());

        Ok(())
    }

    pub fn prover_commit<CS: ConstraintSystem>(
        mut prover: &mut Prover,
        value: u64,
        max_bit_size: usize,
    ) -> Result<
        (
            CompressedRistretto,
            Variable
        ),
        R1CSError,
    > {
        let mut rng = rand::thread_rng();

        let (com, var) = prover.commit(value.into(), Scalar::random(&mut rng));

        let quantity = AllocatedQuantity {
            variable: var,
            assignment: Some(value),
        };

        Self::constrain(&mut prover, quantity, max_bit_size).unwrap();

        Ok((com, var))
    }
}*/

// v and c should be equal
/*pub fn equality_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    c: u64,
) -> Result<(), R1CSError> {
    let (a, b, o) = cs.allocate(|| {
        let x: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
        Ok(((x-c).into(), Scalar::one(), Scalar::zero()))
    })?;

    // a should be (v-c) => a - (v-c) = 0 => a + (c-v) = 0
    let c_minus_v: LinearCombination = [(Variable::One(), Scalar::from(c)), (v.variable, -Scalar::one())].iter().collect();
    cs.constrain(a + c_minus_v);

    // Circuit variable a should be 0
    cs.constrain(a.into());

    // Circuit variable b should be 1
    cs.constrain(b - Scalar::one());

    // Circuit variable o should be 0
    cs.constrain(o.into());

    Ok(())
}*/

fn count_bits(number: u64) -> usize {
    let used_bits = 64 - number.leading_zeros();
    return used_bits as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn test_range_proof_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng: OsRng = OsRng::default();
        let min = 10;
        let max = 100;

        let v = rng.gen_range(min, max);
        println!("v is {}", &v);
        assert!(range_proof_helper(v, min, max).is_ok());
    }

    fn range_proof_helper(v: u64, min: u64, max: u64) -> Result<(), R1CSError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let n = count_bits(max);
        println!("bit_size is {}", &n);

        let a = v - min;
        let b = max - v;
        println!("a, b are {} {}", &a, &b);

        // Prover's scope
        let (proof, commitments) = {
            let mut comms = vec![];

            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"BoundsTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            // Constrain a in [0, 2^n)
            let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
            let quantity_a = AllocatedQuantity {
                variable: var_a,
                assignment: Some(a),
            };
            assert!(positive_no_gadget(&mut prover, quantity_a, n).is_ok());
            comms.push(com_a);

            // Constrain b in [0, 2^n)
            let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
            let quantity_b = AllocatedQuantity {
                variable: var_b,
                assignment: Some(b),
            };
            assert!(positive_no_gadget(&mut prover, quantity_b, n).is_ok());
            comms.push(com_b);

            // Constrain a+b to be same as max-min. This ensures same v is used in both commitments (`com_a` and `com_b`)
            constrain_lc_with_scalar(&mut prover, var_a + var_b, &(max-min).into());

//            println!("For {} in ({}, {}), no of constraints is {}", v, min, max, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove(&bp_gens)?;

            (proof, comms)
        };

        println!("Proving done");

        // Verifier makes a `ConstraintSystem` instance representing a merge gadget
        let mut verifier_transcript = Transcript::new(b"BoundsTest");
        let mut verifier = Verifier::new(&mut verifier_transcript);

        let var_a = verifier.commit(commitments[0]);
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: None,
        };
        assert!(positive_no_gadget(&mut verifier, quantity_a, n).is_ok());

        let var_b = verifier.commit(commitments[1]);
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: None,
        };
        assert!(positive_no_gadget(&mut verifier, quantity_b, n).is_ok());

//        println!("Verifier commitments {:?}", &commitments);

        constrain_lc_with_scalar(&mut verifier, var_a + var_b, &(max-min).into());

        // Verifier verifies proof
        Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
    }
}