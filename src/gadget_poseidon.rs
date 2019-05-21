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


pub struct PoseidonParams {
    pub width: usize,
    // Number of full SBox rounds in beginning
    pub full_rounds_beginning: usize,
    // Number of full SBox rounds in end
    pub full_rounds_end: usize,
    // Number of partial SBox rounds in beginning
    pub partial_rounds: usize,
    pub round_keys: Vec<Scalar>,
    pub MDS_matrix: Vec<Vec<Scalar>>
}

impl PoseidonParams {
    fn new(width: usize, full_rounds_beginning: usize, full_rounds_end: usize, partial_rounds: usize) -> PoseidonParams {
        let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;
//        let round_constants = Self::gen_round_constants(width, total_rounds);
        let round_keys = Self::gen_round_keys(width, total_rounds);
        let matrix_2 = Self::gen_MDS_matrix(width);
        PoseidonParams {
            width,
            full_rounds_beginning,
            full_rounds_end,
            partial_rounds,
            round_keys,
            MDS_matrix: matrix_2
        }
    }

    // TODO: Generate correct round keys
    fn gen_round_keys(width: usize, total_rounds: usize) -> Vec<Scalar> {
        let cap = (total_rounds + 1) * width;
        vec![Scalar::one(); cap]
    }

    // TODO: Generate correct MDS matrix
    fn gen_MDS_matrix(width: usize) -> Vec<Vec<Scalar>> {
        vec![vec![Scalar::one(); width]; width]
    }
}

fn PoseidonPermutation(
    input: &[Scalar],
    params: &PoseidonParams,
    apply_sbox: &Fn(&Scalar) -> Scalar
) -> Vec<Scalar>
{
    let width = params.width;
    assert_eq!(input.len(), width);

    let full_rounds_beginning = params.full_rounds_beginning;
    let partial_rounds = params.partial_rounds;
    let full_rounds_end = params.full_rounds_end;

    let mut current_state = input.to_owned();
    let mut current_state_temp = vec![Scalar::zero(); width];

    let mut round_keys_offset = 0;

    // full Sbox rounds
    for _ in 0..full_rounds_beginning {
        // Sbox layer
        for i in 0..width {
            current_state[i] += params.round_keys[round_keys_offset];
            current_state[i] = apply_sbox(&current_state[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..width {
            for i in 0..width {
                current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = Scalar::zero();
        }
    }

    // middle partial Sbox rounds
    for _ in full_rounds_beginning..(full_rounds_beginning+partial_rounds) {
        for i in 0..width {
            current_state[i] += &params.round_keys[round_keys_offset];
            round_keys_offset += 1;
        }

        // partial Sbox layer, apply Sbox to only 1 element of the state.
        // Here the last one is chosen but the choice is arbitrary.
        current_state[width-1] = apply_sbox(&current_state[width-1]);

        // linear layer
        for j in 0..width {
            for i in 0..width {
                current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = Scalar::zero();
        }
    }

    // last full Sbox rounds
    for _ in full_rounds_beginning+partial_rounds..(full_rounds_beginning+partial_rounds+full_rounds_end) {
        // Sbox layer
        for i in 0..width {
            current_state[i] += params.round_keys[round_keys_offset];
            current_state[i] = apply_sbox(&current_state[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..width {
            for i in 0..width {
                current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
            }
        }

        // Output of this round becomes input to next round
        for i in 0..width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = Scalar::zero();
        }
    }

    current_state
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
    width: usize,
    sbox_outs: Vec<LinearCombination>,
    next_inputs: &mut Vec<LinearCombination>,
    matrix_2: &Vec<Vec<Scalar>>,
) {
    for j in 0..width {
        for i in 0..width {
            next_inputs[i] = next_inputs[i].clone() + sbox_outs[j].clone() * matrix_2[i][j];
        }
    }
}

pub fn PoseidonPermutation_gadget<'a, CS: ConstraintSystem>(
    cs: &mut CS,
    input: Vec<AllocatedScalar>,
    params: &'a PoseidonParams,
    sbox_type: &SboxType,
    output: &[Scalar]
) -> Result<(), R1CSError> {
    let width = params.width;
    assert_eq!(input.len(), width);
    assert_eq!(output.len(), width);

    let mut input_vars: Vec<LinearCombination> = input.iter().map(|i|i.variable.into()).collect();

    let mut round_keys_offset = 0;

    let full_rounds_beginning = params.full_rounds_beginning;
    let partial_rounds = params.partial_rounds;
    let full_rounds_end = params.full_rounds_end;

    // ------------ First rounds with full SBox begin --------------------

    for k in 0..full_rounds_beginning {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        // Substitution (S-box) layer
        for i in 0..width {
            let round_key = params.round_keys[round_keys_offset];
            sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();

            round_keys_offset += 1;
        }

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        apply_linear_layer(width, sbox_outputs, &mut next_input_vars, &params.MDS_matrix);

        for i in 0..width {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // ------------ First rounds with full SBox begin --------------------

    // ------------ Middle rounds with partial SBox begin --------------------

    for k in full_rounds_beginning..(full_rounds_beginning+partial_rounds) {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        // Substitution (S-box) layer
        for i in 0..width {
            let round_key = params.round_keys[round_keys_offset];

            // apply Sbox to only 1 element of the state.
            // Here the last one is chosen but the choice is arbitrary.
            if i == width-1 {
                sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();
            } else {
                sbox_outputs[i] = input_vars[i].clone() + LinearCombination::from(round_key);
            }

            round_keys_offset += 1;
        }

        // Linear layer

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        apply_linear_layer(width, sbox_outputs, &mut next_input_vars, &params.MDS_matrix);

        for i in 0..width {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // ------------ Middle rounds with partial SBox end --------------------

    // ------------ Last rounds with full SBox begin --------------------

    for k in full_rounds_beginning+partial_rounds..(full_rounds_beginning+partial_rounds+full_rounds_end) {
        let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        // Substitution (S-box) layer
        for i in 0..width {
            let round_key = params.round_keys[round_keys_offset];
            sbox_outputs[i] = synthesize_sbox(cs, input_vars[i].clone(), round_key.clone(), sbox_type)?.into();

            round_keys_offset += 1;
        }

        // Linear layer

        let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

        apply_linear_layer(width, sbox_outputs, &mut next_input_vars, &params.MDS_matrix);

        for i in 0..width {
            input_vars[i] = next_input_vars[i].to_owned();
        }
    }

    // ------------ Last rounds with full SBox end --------------------

    for i in 0..width {
        constrain_lc_with_scalar::<CS>(cs, input_vars[i].to_owned(), &output[i]);
    }

    Ok(())
}


// TODO: Construct 2:1 (2 inputs, 1 output) hash and corresponding constraints from the permutation by passing the first input as zero, 2 of the next 4 as non-zero and rest zero. Choose one of the outputs.

pub fn hash_2_Poseidon(xl: Scalar, xr: Scalar, params: &PoseidonParams, apply_sbox: &Fn(&Scalar) -> Scalar) -> Scalar {
    let input = vec![
        Scalar::zero(),
        xl,
        xr,
        Scalar::zero(),
        Scalar::zero(),
        Scalar::zero()
    ];

    // Never take the first input
    PoseidonPermutation(&input, params, apply_sbox)[1]
}


#[cfg(test)]
mod tests {
    use super::*;
    // For benchmarking
    use std::time::{Duration, Instant};
    use rand::SeedableRng;
    use super::rand::rngs::StdRng;

    #[test]
    fn test_poseidon_cube_sbox() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 6;
        let s_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let total_rounds = full_b + full_e + partial_rounds;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let input = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32), Scalar::from(4u32), Scalar::from(5u32), Scalar::from(6u32)];
        let expected_output = PoseidonPermutation(&input, &s_params, &apply_cube_sbox);

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

            for i in 0..width {
                let (com, var) = prover.commit(input[i].clone(), Scalar::random(&mut test_rng));
                comms.push(com);
                allocs.push(AllocatedScalar {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(PoseidonPermutation_gadget(&mut prover,
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
        for i in 0..width {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }
        assert!(PoseidonPermutation_gadget(&mut verifier,
                                           allocs,
                                           &s_params,
                                           &SboxType::Cube,
                                           &expected_output).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_poseidon_inverse_sbox() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 6;
        let s_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let total_rounds = full_b + full_e + partial_rounds;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let input = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32), Scalar::from(4u32), Scalar::from(5u32), Scalar::from(6u32)];
        let expected_output = PoseidonPermutation(&input, &s_params, &apply_inverse_sbox);

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

            for i in 0..width {
                let (com, var) = prover.commit(input[i].clone(), Scalar::random(&mut test_rng));
                comms.push(com);
                allocs.push(AllocatedScalar {
                    variable: var,
                    assignment: Some(input[i]),
                });
            }

            assert!(PoseidonPermutation_gadget(&mut prover,
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
        for i in 0..width {
            let v = verifier.commit(commitments[i]);
            allocs.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }
        assert!(PoseidonPermutation_gadget(&mut verifier,
                                           allocs,
                                           &s_params,
                                           &SboxType::Inverse,
                                           &expected_output).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}