extern crate rand;
extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;

use std::collections::HashMap;
use rand::SeedableRng;
use rand::rngs::OsRng;
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

use crate::scalar_utils::{ScalarBytes, get_base_4_repr};
use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};
use crate::gadget_poseidon::{PoseidonParams, Poseidon_hash_4, Poseidon_hash_4_constraints, Poseidon_hash_4_gadget, SboxType,
                             allocate_statics_for_prover, allocate_statics_for_verifier};

type DBVal = [Scalar; 4];
type ProofNode = [Scalar; 3];

/// Depth of the tree. Has to be a multiple of 4.
// TODO: Remove this restriction.
pub const TreeDepth: usize = 128;

/// Number of bytes to represent leaf index
pub const LeafIndexBytes: usize = TreeDepth / 4;

// TODO: ABSTRACT HASH FUNCTION BETTER
/// Sparse merkle tree with width 4, .i.e each node has 4 children.
pub struct VanillaSparseMerkleTree_4<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<Scalar>,
    db: HashMap<ScalarBytes, DBVal>,
    hash_params: &'a PoseidonParams,
    pub root: Scalar
}

impl<'a> VanillaSparseMerkleTree_4<'a> {
    pub fn new(hash_params: &'a PoseidonParams) -> VanillaSparseMerkleTree_4<'a> {
        if (TreeDepth % 4) != 0 {
            panic!("Tree depth should be a multiple of 4");
        }
        let depth = TreeDepth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<Scalar> = vec![];
        empty_tree_hashes.push(Scalar::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i-1];
            let input: [Scalar; 4] = [prev.clone(); 4];
            // Hash all 4 children at once
            let new = Poseidon_hash_4(input.clone(), hash_params, &SboxType::Inverse);
            let key = new.to_bytes();

            db.insert(key, input);
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree_4 {
            depth,
            empty_tree_hashes,
            db,
            hash_params,
            root
        }
    }

    pub fn update(&mut self, idx: Scalar, val: Scalar) -> Scalar {

        // Find path to insert the new key
        let mut sidenodes_wrap = Some(Vec::<ProofNode>::new());
        self.get(idx, &mut sidenodes_wrap);
        let mut sidenodes = sidenodes_wrap.unwrap();

        // Convert leaf index to base 4
        let mut cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        cur_idx.reverse();
        let mut cur_val = val.clone();

        // Iterate over the base 4 digits
        for d in cur_idx {
            let mut side_elem = sidenodes.pop().unwrap().to_vec();
            // Insert the value at the position determined by the base 4 digit
            side_elem.insert(d as usize, cur_val);

            let mut input: DBVal = [Scalar::zero(); 4];
            input.copy_from_slice(side_elem.as_slice());
            let h = Poseidon_hash_4(input.clone(), self.hash_params, &SboxType::Inverse);
            self.update_db_with_key_val(h, input);
            cur_val = h;
        }

        self.root = cur_val;

        cur_val
    }

    /// Get a value from tree, if `proof` is not None, populate `proof` with the merkle proof
    pub fn get(&self, idx: Scalar, proof: &mut Option<Vec<ProofNode>>) -> Scalar {
        let cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<ProofNode>::new();

        for d in cur_idx {
            let k = cur_node.to_bytes();
            let children = self.db.get(&k).unwrap();
            cur_node = children[d as usize];
            if need_proof {
                let mut proof_node: ProofNode = [Scalar::zero(); 3];
                let mut j = 0;
                for (i, c) in children.to_vec().iter().enumerate() {
                    if i != (d as usize) {
                        proof_node[j] = c.clone();
                        j += 1;
                    }
                }
                proof_vec.push(proof_node);
            }
        }

        match proof {
            Some(v) => {
                v.extend_from_slice(&proof_vec);
            }
            None => ()
        }

        cur_node
    }

    /// Verify a merkle proof, if `root` is None, use the current root else use given root
    pub fn verify_proof(&self, idx: Scalar, val: Scalar, proof: &[ProofNode], root: Option<&Scalar>) -> bool {
        let mut cur_idx = get_base_4_repr(&idx, LeafIndexBytes).to_vec();
        cur_idx.reverse();
        let mut cur_val = val.clone();

        for (i, d) in cur_idx.iter().enumerate() {
            let mut p = proof[self.depth-1-i].clone().to_vec();
            p.insert(*d as usize, cur_val);
            let mut input: DBVal = [Scalar::zero(); 4];
            input.copy_from_slice(p.as_slice());
            let h = Poseidon_hash_4(input.clone(), self.hash_params, &SboxType::Inverse);
            cur_val = h;
        }

        // Check if root is equal to cur_val
        match root {
            Some(r) => {
                cur_val == *r
            }
            None => {
                cur_val == self.root
            }
        }
    }

    fn update_db_with_key_val(&mut self, key: Scalar, val: DBVal) {
        self.db.insert(key.to_bytes(), val);
    }
}

/*
    Hash all 4 children including the node on the path to leaf.
    But the prover cannot disclose at what index the node is in the children.
    So he expresses each child arithmetically. An example below for a single level of the tree.

    Proof elements = [N1, N2, N3]
    Hidden Node (node in path to leaf) = N

    Proof elements with placeholder (_p0, _p1, _p2, _p3) where hidden node can go
    [_p0, N1, _p1, N2, _p2, N3, _p3]

    p = position of hidden node, p =(b1, b0) where b0 and b1 are bits at index 0 and 1
    c0, c1, c2, c3 are children of one level of one subtree

    [c0, c1, c2, c3]

    Different arrangements of node for values of p
    p=0 => [N, N1, N2, N3]
    p=1 => [N1, N, N2, N3]
    p=2 => [N1, N2, N, N3]
    p=3 => [N1, N2, N3, N]

    Arithmetic relations for c0, c1, c2 and c3

    c0 = (1-b0)*(1-b1)*N + b0*N1 + (1-b0)*b1*N1

    c1 = (1-b0)*(1-b1)*N1 + (1-b1)*b0*N + (1-b0)*b1*N2 + b0*b1*N2

    c2 = (1-b1)*N2 + (1-b0)*b1*N + b0*b1*N3

    c3 = (1-b1)*N3 + (1-b0)*b1*N3 + b1*b0*N
*/
pub fn vanilla_merkle_merkle_tree_4_verif_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    root: &Scalar,
    leaf_val: AllocatedScalar,
    leaf_index: AllocatedScalar,
    proof_nodes: Vec<AllocatedScalar>,
    statics: Vec<AllocatedScalar>,
    poseidon_params: &PoseidonParams
) -> Result<(), R1CSError> {

    let mut prev_hash = LinearCombination::from(leaf_val.variable);
    let mut proof_nodes = proof_nodes.clone();

    let statics: Vec<LinearCombination> = statics.iter().map(|s| s.variable.into()).collect();

    // Initialize  constraint_leaf_index with -leaf_index.
    let mut constraint_leaf_index = vec![(leaf_index.variable, -Scalar::one())];
    let mut exp_4 = Scalar::one();
    let two = Scalar::from(2u64);
    let four = Scalar::from(4u64);

    // Each leaf index can take upto LeafIndexBytes bytes so for each byte
    for i in 0..LeafIndexBytes {
        // Decompose each byte into 4 parts of 2 bits each. For each 2 bits
        for j in 0..4 {
            // Check that both 2 bits are actually bits, .i.e. they both are 0 and 1
            let (b0, b0_1, o) = cs.allocate_multiplier(leaf_index.assignment.map(|l| {
                let bit = (l[i] >> 2*j) & 1;
                (bit.into(), (1-bit).into())
            }))?;
            cs.constrain(o.into());
            cs.constrain(b0 + (b0_1 - 1u64));

            let (b1, b1_1, o) = cs.allocate_multiplier(leaf_index.assignment.map(|l| {
                let bit = (l[i] >> (2*j + 1)) & 1;
                (bit.into(), (1-bit).into())
            }))?;
            cs.constrain(o.into());
            cs.constrain(b1 + (b1_1 - 1u64));

            // The 2 bits should represent the base 4 digit for the node in path to leaf
            // Add (2*b1 + b0)*4 to constraint_leaf_index.
            // (2*b1 + b0)*4 = 2*4*b1 + 4*b0
            constraint_leaf_index.push((b1, two * exp_4));
            constraint_leaf_index.push((b0, exp_4));

            let N3: LinearCombination = proof_nodes.pop().unwrap().variable.into();
            let N2: LinearCombination = proof_nodes.pop().unwrap().variable.into();
            let N1: LinearCombination = proof_nodes.pop().unwrap().variable.into();

            // Notation: b0_1 = 1 - b0 and b1_1 = 1 - b1 and prev_hash = N

            // Pre-compute various products of both bits
            // (1 - b0)*(1 - b1)
            let (_, _, b0_1_b1_1) = cs.multiply(b0_1.into(), b1_1.into());
            // (1 - b0)*b1
            let (_, _, b0_1_b1) = cs.multiply(b0_1.into(), b1.into());
            // b0*(1 - b1)
            let (_, _, b0_b1_1) = cs.multiply(b0.into(), b1_1.into());
            // b0*b1
            let (_, _, b0_b1) = cs.multiply(b0.into(), b1.into());

            // (1-b0)*(1-b1)*N
            let (_, _, c0_1) = cs.multiply(b0_1_b1_1.into(), prev_hash.clone());
            // b0*N1
            let (_, _, c0_2) = cs.multiply(b0.into(), N1.clone());
            // (1-b0)*b1*N1
            let (_, _, c0_3) = cs.multiply(b0_1_b1.into(), N1.clone());
            // c0 = (1-b0)*(1-b1)*N + b0*N1 + (1-b0)*b1*N1
            let c0 = c0_1 + c0_2 + c0_3;

            // (1-b0)*(1-b1)*N1
            let (_, _, c1_1) = cs.multiply(b0_1_b1_1.into(), N1.clone());
            // (1-b1)*b0*N
            let (_, _, c1_2) = cs.multiply(b0_b1_1.into(), prev_hash.clone());
            // (1-b0)*b1*N2
            let (_, _, c1_3) = cs.multiply(b0_1_b1.into(), N2.clone());
            // b0*b1*N2
            let (_, _, c1_4) = cs.multiply(b0_b1.into(), N2.clone());
            // c1 = (1-b0)*(1-b1)*N1 + (1-b1)*b0*N + (1-b0)*b1*N2 + b0*b1*N2
            let c1 = c1_1 + c1_2 + c1_3 + c1_4;

            // (1-b1)*N2
            let (_, _, c2_1) = cs.multiply(b1_1.into(), N2.clone());
            // (1-b0)*b1*N
            let (_, _, c2_2) = cs.multiply(b0_1_b1.into(), prev_hash.clone());
            // b0*b1*N3
            let (_, _, c2_3) = cs.multiply(b0_b1.into(), N3.clone());
            // c2 = (1-b1)*N2 + (1-b0)*b1*N + b0*b1*N3
            let c2 = c2_1 + c2_2 + c2_3;

            // (1-b1)*N3
            let (_, _, c3_1) = cs.multiply(b1_1.into(), N3.clone());
            // (1-b0)*b1*N3
            let (_, _, c3_2) = cs.multiply(b0_1_b1.into(), N3.clone());
            // b1*b0*N
            let (_, _, c3_3) = cs.multiply(b0_b1.into(), prev_hash.clone());
            // c3 = (1-b1)*N3 + (1-b0)*b1*N3 + b1*b0*N
            let c3 = c3_1 + c3_2 + c3_3;

            let input: [LinearCombination; 4] = [c0, c1, c2, c3];
            prev_hash = Poseidon_hash_4_constraints::<CS>(cs, input, statics.clone(), poseidon_params, &SboxType::Inverse)?;

            exp_4 = exp_4 * four;
        }
    }

    cs.constrain(constraint_leaf_index.iter().collect());

    constrain_lc_with_scalar::<CS>(cs, prev_hash, root);

    Ok(())
}


#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use curve25519_dalek::constants::BASEPOINT_ORDER;
    use rand::SeedableRng;
    use super::rand::rngs::StdRng;
    // For benchmarking
    use std::time::{Duration, Instant};

    #[test]
    fn test_vanilla_sparse_merkle_tree_4() {
        let mut test_rng: OsRng = OsRng::default();

        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 6;
        let p_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let mut tree = VanillaSparseMerkleTree_4::new(&p_params);

        for i in 1..6 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }


        for i in 1..6 {
            let s = Scalar::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<ProofNode>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(s, s, &proof_vec, None));
            assert!(tree.verify_proof(s, s, &proof_vec, Some(&tree.root)));
        }

        let kvs: Vec<(Scalar, Scalar)> = (0..10).map(|_| (Scalar::random(&mut test_rng), Scalar::random(&mut test_rng))).collect();
        for i in 0..kvs.len() {
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }

    #[test]
    fn test_VSMT_4_Verif() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);

        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 140;
        let total_rounds = full_b + partial_rounds + full_e;
        let p_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let mut tree = VanillaSparseMerkleTree_4::new(&p_params);

        for i in 1..=10 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        let mut merkle_proof_vec = Vec::<ProofNode>::new();
        let mut merkle_proof = Some(merkle_proof_vec);
        let k =  Scalar::from(7u32);
        assert_eq!(k, tree.get(k, &mut merkle_proof));
        merkle_proof_vec = merkle_proof.unwrap();
        assert!(tree.verify_proof(k, k, &merkle_proof_vec, None));
        assert!(tree.verify_proof(k, k, &merkle_proof_vec, Some(&tree.root)));

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(819200, 1);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"VSMT");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let (com_leaf, var_leaf) = prover.commit(k, Scalar::random(&mut test_rng));
            let leaf_alloc_scalar = AllocatedScalar {
                variable: var_leaf,
                assignment: Some(k),
            };

            let (com_leaf_idx, var_leaf_idx) = prover.commit(k, Scalar::random(&mut test_rng));
            let leaf_idx_alloc_scalar = AllocatedScalar {
                variable: var_leaf_idx,
                assignment: Some(k),
            };

            let mut proof_comms = vec![];
            let mut proof_alloc_scalars = vec![];
            for p in merkle_proof_vec.iter() {
                for i in p {
                    let (c, v) = prover.commit(*i, Scalar::random(&mut test_rng));
                    proof_comms.push(c);
                    proof_alloc_scalars.push(AllocatedScalar {
                        variable: v,
                        assignment: Some(*i),
                    });
                }
            }

            let num_statics = 2;
            let statics = allocate_statics_for_prover(&mut prover, num_statics);

            let start = Instant::now();
            assert!(vanilla_merkle_merkle_tree_4_verif_gadget(
                &mut prover,
                tree.depth,
                &tree.root,
                leaf_alloc_scalar,
                leaf_idx_alloc_scalar,
                proof_alloc_scalars,
                statics,
                                &p_params).is_ok());

            println!("For 4-ary tree of height {} (has 2^{} leaves) and Poseidon rounds {}, no of multipliers is {} and constraints is {}", tree.depth, tree.depth*2, total_rounds, &prover.num_multipliers(), &prover.num_constraints());

            let proof = prover.prove(&bp_gens).unwrap();
            let end = start.elapsed();

            println!("Proving time is {:?}", end);

            (proof, (com_leaf, com_leaf_idx, proof_comms))
        };

        let mut verifier_transcript = Transcript::new(b"VSMT");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_leaf = verifier.commit(commitments.0);
        let leaf_alloc_scalar = AllocatedScalar {
            variable: var_leaf,
            assignment: None,
        };

        let var_leaf_idx = verifier.commit(commitments.1);
        let leaf_idx_alloc_scalar = AllocatedScalar {
            variable: var_leaf_idx,
            assignment: None,
        };

        let mut proof_alloc_scalars = vec![];
        for c in commitments.2.iter() {
            let v = verifier.commit(*c);
            proof_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: None
            });
        }

        let num_statics = 2;
        let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

        let start = Instant::now();
        assert!(vanilla_merkle_merkle_tree_4_verif_gadget(
            &mut verifier,
            tree.depth,
            &tree.root,
            leaf_alloc_scalar,
            leaf_idx_alloc_scalar,
            proof_alloc_scalars,
            statics,
            &p_params).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        let end = start.elapsed();

        println!("Verification time is {:?}", end);
    }
}