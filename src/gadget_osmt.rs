/// This is incomplete

extern crate rand;
extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;

use std::collections::HashMap;
use rand::rngs::OsRng;
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

use crate::scalar_utils::{ScalarBytes, ScalarBits, get_bits, scalar_to_u64_array};
use crate::r1cs_utils::AllocatedScalar;
//use crate::gadget_mimc::{mimc, MIMC_ROUNDS};
use crate::gadget_poseidon::{PoseidonParams, Poseidon_hash_2, Poseidon_hash_2_constraints, Poseidon_hash_2_gadget, SboxType,
                             allocate_statics_for_prover, allocate_statics_for_verifier};
use curve25519_dalek::constants::BASEPOINT_ORDER;

// DBVal.0 is not None when DBVal is a single key value, i.e. DBVal.1 is a key and DBVal.2 is a value.
// Otherwise, one of the them is root of a subtree.
type DBVal = (Option<bool>, Scalar, Scalar);
/// Depth of the tree. Has to be a power of 2.
// TODO: Remove this restriction.
pub const TreeDepth: usize = 128;

/// Optimization ideas taken from https://ethresear.ch/t/optimizing-sparse-merkle-trees/3751
pub struct OptmzSparseMerkleTree<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<Scalar>,
    db: HashMap<ScalarBytes, DBVal>,
    //hash_constants: &'a [Scalar],
    hash_params: &'a PoseidonParams,
    pub root: Scalar
}

impl<'a> OptmzSparseMerkleTree<'a> {
    pub fn new(hash_params: &'a PoseidonParams, depth: usize) -> OptmzSparseMerkleTree<'a> {
        let depth = depth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<Scalar> = vec![];
        empty_tree_hashes.push(Scalar::zero());
        for _ in 0..depth {
            let prev = empty_tree_hashes[0];
            //let new = mimc(&prev, &prev, hash_constants);
            let new = Poseidon_hash_2(prev.clone(), prev.clone(), hash_params, &SboxType::Inverse);
            empty_tree_hashes.insert(0, new);
        }

        let root = empty_tree_hashes[0].clone();

        OptmzSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_params,
            root
        }
    }

    pub fn update(&mut self, idx: Scalar, val: Scalar) -> Scalar {
        let old_root = &self.root.clone();
        let new_root = self._update(&ScalarBits::from_scalar(&idx, self.depth), val, old_root, 0);
        self.root = new_root.clone();
        new_root
    }

    pub fn get(&self, idx: Scalar, proof: &mut Option<Vec<DBVal>>) -> Scalar {
        let mut cur_idx = ScalarBits::from_scalar(&idx, self.depth);
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<DBVal>::new();

        for i in 0..self.depth {
            if cur_node == self.empty_tree_hashes[i] {
                cur_node = Scalar::zero();
                break
            }

            let v = self.get_from_db(&cur_node);
            if need_proof { proof_vec.push(v.clone()); }

            if v.0.is_some() {
                let scl = cur_idx.to_scalar();
                if scl == v.1 {
                    cur_node =  v.2;
                    break
                } else {
                    cur_node =  Scalar::zero();
                    break
                }
            }

            if cur_idx.is_msb_set() {
                cur_node = v.2;
            } else {
                cur_node = v.1;
            }

            cur_idx.shl();
        }

        match proof {
            Some(v) => {
                v.extend_from_slice(&proof_vec);
            }
            None => ()
        }

        cur_node
    }

    pub fn verify_proof(&self, idx: Scalar, val: Scalar, proof: &[DBVal], root: &Scalar) -> bool {
        if *root == self.empty_tree_hashes[0] {
            return proof.len() == 0
        }

        let mut prev_hash: Scalar = root.clone();

        let mut path = ScalarBits::from_scalar(&idx, self.depth);

        for i in 0..proof.len() {
            let proof_node = proof[i];
            if proof_node.0.is_some() {
                if proof_node.1 == path.to_scalar() {
                    return proof_node.2 == val
                } else {
                    return val == Scalar::zero()
                }
            } else {
                //let expected_hash = mimc(&proof_node.1, &proof_node.2, self.hash_constants);
                let expected_hash = Poseidon_hash_2(proof_node.1.clone(), proof_node.2.clone(), self.hash_params, &SboxType::Inverse);
                if expected_hash != prev_hash {
                    return false
                }

                if path.is_msb_set() {
                    prev_hash = proof_node.2.clone()
                } else {
                    prev_hash = proof_node.1.clone()
                }
            }

            path.shl();
        }

        if proof.len() == self.depth {
            prev_hash == val
        } else {
            val == Scalar::zero()
        }
    }

    fn _update(&mut self, path: &ScalarBits, val: Scalar, root: &Scalar, depth: usize) -> Scalar {
        if depth == self.depth {
            return val
        }

        if *root == self.empty_tree_hashes[depth] {
            let new_root = self.get_subtree_with_one_val(path, &val, depth);
            self.update_db(&new_root,
                           (Some(true), path.to_scalar(), val));
            new_root
        } else {
            let child = self.get_from_db(&root).clone();
            if child.0.is_some() {
                self.update_one_val_subtree(path, val.clone(),
                                            &ScalarBits::from_scalar(&child.1, self.depth), child.2.clone(), depth)
            } else {
                let mut new_path = path.clone();
                new_path.shl();
                if path.is_msb_set() {
                    let new_right = self._update(&new_path, val, &child.2, depth+1);
                    //let root = mimc(&child.1, &new_right, self.hash_constants);
                    let root = Poseidon_hash_2(child.1.clone(), new_right.clone(), self.hash_params, &SboxType::Inverse);
                    self.update_db(&root, (None, child.1.clone(), new_right));
                    root
                } else {
                    let new_left = self._update(&new_path, val, &child.1, depth+1);
                    //let root = mimc(&new_left, &child.2, self.hash_constants);
                    let root = Poseidon_hash_2(new_left.clone(), child.2.clone(), self.hash_params, &SboxType::Inverse);
                    self.update_db(&root, (None, new_left, child.2.clone()));
                    root
                }
            }
        }
    }

    fn update_one_val_subtree(&mut self, path_for_new_key: &ScalarBits,
                              val_for_new_key: Scalar, path_for_old_key: &ScalarBits,
                              val_for_old_key: Scalar, depth: usize) -> Scalar {
        if depth == self.depth {
            panic!("Error in update_one_val_subtree")
        }

        let (left, right) = {
            let mut next_new_path = path_for_new_key.clone();
            next_new_path.shl();
            let mut next_old_path = path_for_old_key.clone();
            next_old_path.shl();
            if path_for_new_key.is_msb_set() {
                if path_for_old_key.is_msb_set() {
                    (self.empty_tree_hashes[depth+1].clone(),
                     self.update_one_val_subtree(&next_new_path, val_for_new_key,
                                                 &next_old_path, val_for_old_key, depth+1))
                } else {
                    let left_subtree_hash = self.get_subtree_with_one_val(&next_old_path, &val_for_old_key, depth+1);
                    let right_subtree_hash = self.get_subtree_with_one_val(&next_new_path, &val_for_new_key, depth+1);
                    self.update_db(&left_subtree_hash, (Some(true), next_old_path.to_scalar(), val_for_old_key));
                    self.update_db(&right_subtree_hash, (Some(true), next_new_path.to_scalar(), val_for_new_key));
                    (left_subtree_hash, right_subtree_hash)
                }
            } else {
                if path_for_old_key.is_msb_set() {
                    let left_subtree_hash = self.get_subtree_with_one_val(&next_new_path, &val_for_new_key, depth+1);
                    let right_subtree_hash = self.get_subtree_with_one_val(&next_old_path, &val_for_old_key, depth+1);
                    self.update_db(&left_subtree_hash, (Some(true), next_new_path.to_scalar(), val_for_new_key));
                    self.update_db(&right_subtree_hash, (Some(true), next_old_path.to_scalar(), val_for_old_key));
                    (left_subtree_hash, right_subtree_hash)
                } else {
                    (self.update_one_val_subtree(&next_new_path, val_for_new_key,
                                                 &next_old_path, val_for_old_key, depth+1),
                     self.empty_tree_hashes[depth+1].clone())
                }
            }
        };

        //let root = mimc(&left, &right, self.hash_constants);
        let root = Poseidon_hash_2(left.clone(), right.clone(), self.hash_params, &SboxType::Inverse);
        self.update_db(&root, (None, left, right));
        root
    }

    fn get_subtree_with_one_val(&self, path: &ScalarBits, val: &Scalar, depth: usize) -> Scalar {
        if depth == self.depth {
            return val.clone()
        }

        let (l, r) = {
            let mut new_path = path.clone();
            new_path.shl();
            if path.is_msb_set() {
                (self.empty_tree_hashes[depth+1].clone(),
                 self.get_subtree_with_one_val(&new_path, val, depth+1))
            } else {
                (self.get_subtree_with_one_val(&new_path, val, depth+1),
                 self.empty_tree_hashes[depth+1].clone())
            }
        };
        Poseidon_hash_2(l.clone(), r.clone(), self.hash_params, &SboxType::Inverse)
    }

    fn update_db(&mut self, key: &Scalar, val: DBVal) {
        let k = key.to_bytes();

        self.db.insert(k, val);
    }

    fn get_from_db(&self, key: &Scalar) -> &DBVal {
        // TODO: Raise an error when root is not present in db
        let k = key.to_bytes();
        let val = self.db.get(&k).unwrap();
        val
    }
}

pub fn optimized_sparse_merkle_merkle_tree_verif_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    root: &Scalar,
    leaf_val: AllocatedScalar,
    leaf_index_bits: Vec<AllocatedScalar>,
    proof_nodes: Vec<AllocatedScalar>,
    statics: Vec<AllocatedScalar>,
    poseidon_params: &PoseidonParams
) -> Result<(), R1CSError> {
    // Does it make sense since the size of proof_nodes might allow the verifier to guess where the leaf is in the tree.
    unimplemented!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand::SeedableRng;
    use super::rand::rngs::StdRng;
    use std::collections::HashSet;

    #[test]
    fn test_optmz_sparse_merkle_tree() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);

        // Generate the MiMC round constants
        //let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();
        let width = 6;
        let (full_b, full_e) = (4, 4);
        let partial_rounds = 2;
        let p_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
        let mut tree = OptmzSparseMerkleTree::new(&p_params, TreeDepth);

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<DBVal>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            println!("Proof length={}", proof_vec.len());
            assert!(tree.verify_proof(s, s, &proof_vec, &tree.root));
        }

        //let kvs: Vec<(Scalar, Scalar)> = (0..10).map(|_| (Scalar::random(&mut test_rng), Scalar::random(&mut test_rng))).collect();
        //let kvs: Vec<(Scalar, Scalar)> = vec![(Scalar::from(7227u32), Scalar::from(7227u32)), (Scalar::from(7700u32), Scalar::from(7700u32))];
        let mut kvs: Vec<(Scalar, Scalar)> = vec![];
        //let mut keys: HashSet<[u8; TreeDepth]> = HashSet::new();
        while kvs.len() != 100 {
            let _k = Scalar::random(&mut test_rng);
            let bits = ScalarBits::from_scalar(&_k, TreeDepth);
            /*let mut bit_array = [0u8; TreeDepth];
            let bits_slice = &bits.bit_array[..bit_array.len()];
            bit_array.copy_from_slice(bits_slice);
            if keys.contains(&bit_array) {
                continue
            }*/
            let key = bits.to_scalar();
            let v = Scalar::random(&mut test_rng);
            kvs.push((key, v));
        }
        println!("Running on {} random keys", &kvs.len());
        for i in 0..kvs.len() {
            //println!("Setting {:?}={:?}", scalar_to_u64_array(&kvs[i].0), scalar_to_u64_array(&kvs[i].1));
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            let mut proof_vec = Vec::<DBVal>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut proof));
            proof_vec = proof.unwrap();
            println!("Proof length={}", proof_vec.len());
            assert!(tree.verify_proof(kvs[i].0, kvs[i].1, &proof_vec, &tree.root));
        }

    }
}