extern crate rand;
extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;

use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};
use crate::gadget_zero_nonzero::is_nonzero_gadget;


pub struct SharkMiMCParams {
    pub num_branches: usize,
    pub middle_rounds: usize,
    pub total_rounds: usize,
        //    pub round_constants: Vec<Scalar>,
    pub round_keys: Vec<Scalar>,
    // TODO: Add matrix_1
    pub matrix_2: Vec<Vec<Scalar>>
}

impl SharkMiMCParams {
    fn new(num_branches: usize, middle_rounds: usize) -> SharkMiMCParams {
        let total_rounds = 6 + middle_rounds;
//        let round_constants = Self::gen_round_constants(num_branches, total_rounds);
        let round_keys = Self::gen_round_keys(num_branches, total_rounds);
        let matrix_2 = Self::gen_matrix_2(num_branches);
        SharkMiMCParams {
            num_branches,
            middle_rounds,
            total_rounds,
//            round_constants,
            round_keys,
            matrix_2
        }
    }

    /*fn gen_round_constants(num_branches: usize, total_rounds: usize) -> Vec<Scalar> {
        let cap = total_rounds * num_branches;
        let mut consts: Vec<Scalar> = Vec::with_capacity(cap);
        for i in 0..cap {
            consts[i] = Scalar::one();
        }
        consts
    }*/

    fn gen_round_keys(num_branches: usize, total_rounds: usize) -> Vec<Scalar> {
        let cap = (total_rounds + 1) * num_branches;
        vec![Scalar::one(); cap]
    }

    fn gen_matrix_2(num_branches: usize) -> Vec<Vec<Scalar>> {
        vec![vec![Scalar::one(); num_branches]; num_branches]
    }
}

fn SharkMiMC(
    input: &[Scalar],
    params: &SharkMiMCParams,
    apply_sbox: &Fn(&Scalar) -> Scalar
) -> Vec<Scalar>
{
    let num_branches = params.num_branches;
    assert_eq!(input.len(), num_branches);

    let mut value_branch = input.to_owned();
    let mut value_branch_temp = vec![Scalar::zero(); num_branches];

    let mut round_keys_offset = 0;

    // 3 full Sbox rounds
    for _ in 0..3 {
        // Sbox layer
        for i in 0..num_branches {
            value_branch[i] += params.round_keys[round_keys_offset];
            value_branch[i] = apply_sbox(&value_branch[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..num_branches {
            for i in 0..num_branches {
                value_branch_temp[i] += value_branch[j] * params.matrix_2[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = Scalar::zero();
        }
    }

    // middle partial Sbox rounds
    for _ in 3..(3+params.middle_rounds) {
        for i in 0..num_branches {
            value_branch[i] += &params.round_keys[round_keys_offset];
            round_keys_offset += 1;
        }

        // partial Sbox layer
        value_branch[0] = apply_sbox(&value_branch[0]);

        // linear layer
        for j in 0..num_branches {
            for i in 0..num_branches {
                value_branch_temp[i] += value_branch[j] * params.matrix_2[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = Scalar::zero();
        }
    }

    // last full Sbox rounds
    for _ in 3+params.middle_rounds..(3+params.middle_rounds+2) {
        // Sbox layer
        for i in 0..num_branches {
            value_branch[i] += params.round_keys[round_keys_offset];
            value_branch[i] = apply_sbox(&value_branch[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..num_branches {
            for i in 0..params.num_branches {
                value_branch_temp[i] += value_branch[j] * params.matrix_2[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = Scalar::zero();
        }
    }

    for i in 0..num_branches {
        value_branch[i] += params.round_keys[round_keys_offset];
        value_branch[i] = apply_sbox(&value_branch[i]);
        round_keys_offset += 1;

        value_branch[i] += params.round_keys[round_keys_offset];
        round_keys_offset += 1;
    }

    value_branch
}

fn apply_cube_sbox(elem: &Scalar) -> Scalar
{
    (elem * elem) * elem
}

fn apply_inverse_sbox(elem: &Scalar) -> Scalar
{
    elem.invert()
}

pub enum SboxType {
    Cube,
    Inverse
}

fn synthesize_sbox<CS: ConstraintSystem>(
    cs: &mut CS,
    input_var: LinearCombination,
    round_key: Scalar,
    sbox_type: &SboxType
) -> Result<Variable, R1CSError> {
    match sbox_type {
        SboxType::Cube => synthesize_cube_sbox(cs, input_var, round_key),
        SboxType::Inverse => synthesize_inverse_sbox(cs, input_var, round_key),
        _ => Err(R1CSError::GadgetError {description: String::from("inverse not implemented")})
    }
}

// Allocate variables in circuit and enforce constraints when Sbox as cube
fn synthesize_cube_sbox<CS: ConstraintSystem>(
    cs: &mut CS,
    input_var: LinearCombination,
    round_key: Scalar
) -> Result<Variable, R1CSError> {
    let inp_plus_const: LinearCombination = input_var + round_key;
    let (i, _, sqr) = cs.multiply(inp_plus_const.clone(), inp_plus_const);
    let (_, _, cube) = cs.multiply(sqr.into(), i.into());
    Ok(cube)
}

// Allocate variables in circuit and enforce constraints when Sbox as inverse
fn synthesize_inverse_sbox<CS: ConstraintSystem>(
    cs: &mut CS,
    input_var: LinearCombination,
    round_key: Scalar
) -> Result<Variable, R1CSError> {
    let inp_plus_const: LinearCombination = input_var + round_key;

    let val_l = cs.evaluate_lc(&inp_plus_const);
    let val_r = val_l.map(|l| {
        l.invert()
    });

    let (var_l, _) = cs.allocate_single(val_l)?;
    let (var_r, var_o) = cs.allocate_single(val_r)?;

    // Ensure `inp_plus_const` is not zero
    is_nonzero_gadget(
        cs,
        AllocatedScalar {
            variable: var_l,
            assignment: val_l
        },
        AllocatedScalar {
            variable: var_r,
            assignment: val_r
        }
    )?;

    // Constrain product of ``inp_plus_const` and its inverse to be 1.
    constrain_lc_with_scalar::<CS>(cs, var_o.unwrap().into(), &Scalar::one());

    Ok(var_r)
}

fn apply_linear_layer(
    num_branches: usize,
    sbox_outs: Vec<LinearCombination>,
    next_inputs: &mut Vec<LinearCombination>,
    matrix_2: &Vec<Vec<Scalar>>,
) {
    for j in 0..num_branches {
        for i in 0..num_branches {
            next_inputs[i] = next_inputs[i].clone() + sbox_outs[j].clone() * matrix_2[i][j];
        }
    }
}

pub fn sharkmimc_gadget<'a, CS: ConstraintSystem>(
    cs: &mut CS,
    input: Vec<AllocatedScalar>,
    params: &'a SharkMiMCParams,
    sbox_type: &SboxType,
    output: &[Scalar]
) -> Result<(), R1CSError> {
    let num_branches = params.num_branches;
    assert_eq!(input.len(), num_branches);
    assert_eq!(output.len(), num_branches);

    let mut input_vars: Vec<LinearCombination> = input.iter().map(|i|i.variable.into()).collect();

    let mut round_keys_offset = 0;

    // ------------ First 3 rounds begin --------------------

    for k in 0..3 {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        // Substitution (S-box) layer
        for i in 0..num_branches {
            let round_key = params.round_keys[round_keys_offset];
            sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();

            round_keys_offset += 1;
        }

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        apply_linear_layer(num_branches, sbox_outputs, &mut next_input_vars, &params.matrix_2);

        for i in 0..num_branches {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // ------------ First 3 rounds end --------------------

    // ------------ Middle rounds begin --------------------

    for k in 3..(3+params.middle_rounds) {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        // Substitution (S-box) layer
        for i in 0..num_branches {
            let round_key = params.round_keys[round_keys_offset];

            if i == 0 {
                sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();
            } else {
                sbox_outputs[i] = input_vars[i].clone() + LinearCombination::from(round_key);
            }

            round_keys_offset += 1;
        }

        // Linear layer

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        apply_linear_layer(num_branches, sbox_outputs, &mut next_input_vars, &params.matrix_2);

        for i in 0..num_branches {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // ------------ Middle rounds end --------------------

    // ------------ Last 2+1 rounds begin --------------------

    // 2 rounds
    for k in 3+params.middle_rounds..(3+params.middle_rounds+2) {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        // Substitution (S-box) layer
        for i in 0..num_branches {
            let round_key = params.round_keys[round_keys_offset];
            sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();

            round_keys_offset += 1;
        }

        // Linear layer

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

        apply_linear_layer(num_branches, sbox_outputs, &mut next_input_vars, &params.matrix_2);

        for i in 0..num_branches {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // Last round
    let mut output_vars: Vec<LinearCombination> = vec![LinearCombination::default(); num_branches];

    // Substitution (S-box) layer
    for i in 0..num_branches {
        let round_key = params.round_keys[round_keys_offset];

        let sbox_out: LinearCombination = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();

        round_keys_offset += 1;

        let new_round_key = params.round_keys[round_keys_offset];

        output_vars[i] = sbox_out + new_round_key;

        round_keys_offset += 1;
    }

    // ------------ Last 2+1 rounds end --------------------

    for i in 0..num_branches {
        constrain_lc_with_scalar::<CS>(cs, output_vars[i].to_owned(), &output[i]);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    // For benchmarking
    use std::time::{Duration, Instant};
    use rand::SeedableRng;
    use super::rand::rngs::StdRng;

    #[test]
    fn test_sharkmimc_cube_sbox() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
        let num_branches = 4;
        let middle_rounds = 6;
        let s_params = SharkMiMCParams::new(num_branches, middle_rounds);
        let total_rounds = s_params.total_rounds;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let input = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32), Scalar::from(4u32)];
        let expected_output = SharkMiMC(&input, &s_params, &apply_cube_sbox);

        println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"SharkMiMC");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for i in 0..num_branches {
                let (com, var) = prover.commit(input[i].clone(), Scalar::random(&mut test_rng));
                comms.push(com);
                allocs.push(AllocatedScalar {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(sharkmimc_gadget(&mut prover,
                                allocs,
                                     &s_params,
                                &SboxType::Cube,
                                &expected_output).is_ok());

            let proof = prover.prove(&bp_gens).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(b"SharkMiMC");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for i in 0..num_branches {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }
        assert!(sharkmimc_gadget(&mut verifier,
                                 allocs,
                                 &s_params,
                                 &SboxType::Cube,
                                 &expected_output).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_sharkmimc_inverse_sbox() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
        let num_branches = 4;
        let middle_rounds = 6;
        let s_params = SharkMiMCParams::new(num_branches, middle_rounds);
        let total_rounds = s_params.total_rounds;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let input = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32), Scalar::from(4u32)];
        let expected_output = SharkMiMC(&input, &s_params, &apply_inverse_sbox);

        println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"SharkMiMC");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for i in 0..num_branches {
                let (com, var) = prover.commit(input[i].clone(), Scalar::random(&mut test_rng));
                comms.push(com);
                allocs.push(AllocatedScalar {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(sharkmimc_gadget(&mut prover,
                                     allocs,
                                     &s_params,
                                     &SboxType::Inverse,
                                     &expected_output).is_ok());

            let proof = prover.prove(&bp_gens).unwrap();
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(b"SharkMiMC");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for i in 0..num_branches {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }
        assert!(sharkmimc_gadget(&mut verifier,
                                 allocs,
                                 &s_params,
                                 &SboxType::Inverse,
                                 &expected_output).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}