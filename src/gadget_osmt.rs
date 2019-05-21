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

use crate::scalar_utils::{ScalarBytes, TreeDepth, ScalarBits, get_bits, scalar_to_u64_array};
use crate::r1cs_utils::AllocatedScalar;
use crate::gadget_mimc::{mimc, MIMC_ROUNDS};
use curve25519_dalek::constants::BASEPOINT_ORDER;


type DBVal = (Option<bool>, Scalar, Scalar);

pub struct OptmzSparseMerkleTree<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<Scalar>,
    db: HashMap<ScalarBytes, DBVal>,
    hash_constants: &'a [Scalar],
    pub root: Scalar
}

impl<'a> OptmzSparseMerkleTree<'a> {
    pub fn new(hash_constants: &'a [Scalar]) -> OptmzSparseMerkleTree<'a> {
        let depth = TreeDepth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<Scalar> = vec![];
        empty_tree_hashes.push(Scalar::zero());
        for _ in 0..depth {
            let prev = empty_tree_hashes[0];
            let new = mimc(&prev, &prev, hash_constants);
            empty_tree_hashes.insert(0, new);
        }

        let root = empty_tree_hashes[0].clone();

        OptmzSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_constants,
            root
        }
    }

    pub fn update(&mut self, idx: Scalar, val: Scalar) -> Scalar {
        let old_root = &self.root.clone();
        let new_root = self._update(&ScalarBits::from_scalar(&idx), val, old_root, 0);
        self.root = new_root.clone();
        new_root
    }

    pub fn get(&self, idx: Scalar, proof: &mut Option<Vec<DBVal>>) -> Scalar {
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<DBVal>::new();

        for i in 0..self.depth {
            if cur_node == self.empty_tree_hashes[i] {
                //println!("Root:Num bits of child node idx={}", cur_idx.num_bits());
                cur_node = Scalar::zero();
                break
            }

            let v = self.get_from_db(&cur_node);
            if need_proof { proof_vec.push(v.clone()); }

            let debug_cur_idx_scalar = cur_idx.to_scalar();
            let debug_cur_idx = scalar_to_u64_array(&debug_cur_idx_scalar);
            println!("Loop: {} cur_idx {:?}", i, debug_cur_idx);
//            println!("Loop: cur_idx reduced {:?}", &reduce_field_repr_to_elem::<E>(cur_idx));
            let debug_cur_node = scalar_to_u64_array(&cur_node);
            println!("Loop: db key {:?}", debug_cur_node);
            let debug_v1 = scalar_to_u64_array(&v.1);
            let debug_v2 = scalar_to_u64_array(&v.2);
            println!("Loop: db val ({:?}, {:?}, {:?})", &v.0, debug_v1, debug_v2);
            if v.0.is_some() {
                //if are_equal::<E>(&Scalar::from_repr(cur_idx).unwrap(), &v.1) {
                /*println!("1Child:Num bits of child node idx={}", cur_idx.num_bits());
                println!("1Child:cur_idx={:?}", &cur_idx);
                println!("1Child:cur_idx reduced={:?}", &reduce_field_repr_to_elem::<E>(cur_idx));*/
                let scl = cur_idx.to_scalar();
                println!("1Child:cur_idx={:?}", scalar_to_u64_array(&scl));
                /*println!("1Child:cur_idx={:?}", &scl.reduce());*/
                if scl == v.1 {
                    cur_node =  v.2;
                    break
                } else {
                    println!("1Child:found 0 for key val {:?}={:?}", scalar_to_u64_array(&v.1), scalar_to_u64_array(&v.2));
                    cur_node =  Scalar::zero();
                    break
                }
            }

            let new_x = ScalarBits::from_scalar(&debug_cur_idx_scalar);
            if cur_idx.is_msb_set() {
                cur_node = v.2;
            } else {
                cur_node = v.1;
            }

            cur_idx.shl();
            /*if !cur_idx.to_non_reduced_scalar().is_canonical() {
                cur_idx = ScalarBits::from_scalar(&cur_idx.to_scalar());
            }*/
            //cur_idx = ScalarBits::from_scalar(&cur_idx.to_scalar());
            //cur_idx = reduce_field_repr::<E>(cur_idx);
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

        let mut path = ScalarBits::from_scalar(&idx);

        for i in 0..proof.len() {
            let proof_node = proof[i];
            if proof_node.0.is_some() {
                //let rhs = Scalar::from_repr(path).unwrap();
                if proof_node.1 == path.to_scalar() {
                    return proof_node.2 == val
                } else {
                    return val == Scalar::zero()
                }
            } else {
                let expected_hash = mimc(&proof_node.1, &proof_node.2, self.hash_constants);
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
        println!("Called _update with key-val {:?}={:?}", scalar_to_u64_array(&path.to_scalar()), scalar_to_u64_array(&val));
        if depth == self.depth {
            return val
        }

        if *root == self.empty_tree_hashes[depth] {
            println!("Calling get_subtree_with_one_val with depth {} key-val {:?}={:?}", depth, scalar_to_u64_array(&path.to_scalar()), scalar_to_u64_array(&val));
            let new_root = self.get_subtree_with_one_val(path, &val, depth);
            self.update_db(&new_root,
                           //(Some(true), Scalar::from_repr(path).unwrap(), val));
                           (Some(true), path.to_scalar(), val));
                           //(Some(true), path.to_non_reduced_scalar(), val));
            return new_root
        }

        //println!("_update with depth {}", &depth);
        let child = self.get_from_db(&root).clone();
        if child.0.is_some() {
            //let x = ScalarBits::from_scalar(&child.1);
            return self.update_one_val_subtree(path, val.clone(),
                                               &ScalarBits::from_scalar(&child.1), child.2.clone(), depth)
                                               //&ScalarBits::from_scalar_dont_reduce(&child.1), child.2.clone(), depth)
        } else {
            let mut new_path = path.clone();
            new_path.shl();
            if path.is_msb_set() {
                let new_right = self._update(&new_path, val, &child.2, depth+1);
                let root = mimc(&child.1, &new_right, self.hash_constants);
                self.update_db(&root, (None, child.1.clone(), new_right));
                return root
            } else {
                let new_left = self._update(&new_path, val, &child.1, depth+1);
                let root = mimc(&new_left, &child.2, self.hash_constants);
                self.update_db(&root, (None, new_left, child.2.clone()));
                return root
            }
        }
    }

    fn update_one_val_subtree(&mut self, path_for_new_key: &ScalarBits,
                              val_for_new_key: Scalar, path_for_old_key: &ScalarBits,
                              val_for_old_key: Scalar, depth: usize) -> Scalar {
        let new_path_scalar = path_for_new_key.to_scalar();
        let old_path_scalar = path_for_old_key.to_scalar();
        let debug_path_for_new_key = scalar_to_u64_array(&new_path_scalar);
        let debug_path_for_old_key = scalar_to_u64_array(&old_path_scalar);
        println!("Called update_one_val_subtree with new key-val {:?}={:?}", debug_path_for_new_key, scalar_to_u64_array(&val_for_new_key));
        println!("Called update_one_val_subtree with old key-val {:?}={:?}", debug_path_for_old_key, scalar_to_u64_array(&val_for_old_key));
        if depth == self.depth {
            panic!("Error in update_one_val_subtree")
        }

        let (left, right) = {
            let mut next_new_path = path_for_new_key.clone();
            next_new_path.shl();
            let mut next_old_path = path_for_old_key.clone();
            next_old_path.shl();
            let debug_next_old_path = scalar_to_u64_array(&next_old_path.to_scalar());
            let debug_next_new_path = scalar_to_u64_array(&next_new_path.to_scalar());
            if path_for_new_key.is_msb_set() {
                if path_for_old_key.is_msb_set() {
                    (self.empty_tree_hashes[depth+1].clone(),
                     self.update_one_val_subtree(&next_new_path, val_for_new_key,
                                                 &next_old_path, val_for_old_key, depth+1))
                } else {
                    println!("Calling get_subtree_with_one_val with depth {} key-val {:?}={:?}", depth+1, debug_next_old_path, scalar_to_u64_array(&val_for_old_key));
                    let left_subtree_hash = self.get_subtree_with_one_val(&next_old_path, &val_for_old_key, depth+1);
                    println!("Calling get_subtree_with_one_val with depth {} key-val {:?}={:?}", depth+1, debug_next_new_path, scalar_to_u64_array(&val_for_new_key));
                    let right_subtree_hash = self.get_subtree_with_one_val(&next_new_path, &val_for_new_key, depth+1);
                    self.update_db(&left_subtree_hash, (Some(true), next_old_path.to_scalar(), val_for_old_key));
                    //self.update_db(&left_subtree_hash, (Some(true), next_old_path.to_non_reduced_scalar(), val_for_old_key));
                    self.update_db(&right_subtree_hash, (Some(true), next_new_path.to_scalar(), val_for_new_key));
                    //self.update_db(&right_subtree_hash, (Some(true), next_new_path.to_non_reduced_scalar(), val_for_new_key));
                    (left_subtree_hash, right_subtree_hash)
                }
            } else {
                if path_for_old_key.is_msb_set() {
                    println!("Calling get_subtree_with_one_val with depth {} key-val {:?}={:?}", depth+1, debug_next_new_path, scalar_to_u64_array(&val_for_new_key));
                    let left_subtree_hash = self.get_subtree_with_one_val(&next_new_path, &val_for_new_key, depth+1);
                    println!("Calling get_subtree_with_one_val with depth {} key-val {:?}={:?}", depth+1, debug_next_old_path, scalar_to_u64_array(&val_for_old_key));
                    let right_subtree_hash = self.get_subtree_with_one_val(&next_old_path, &val_for_old_key, depth+1);
                    self.update_db(&left_subtree_hash, (Some(true), next_new_path.to_scalar(), val_for_new_key));
                    //self.update_db(&left_subtree_hash, (Some(true), next_new_path.to_non_reduced_scalar(), val_for_new_key));
                    self.update_db(&right_subtree_hash, (Some(true), next_old_path.to_scalar(), val_for_old_key));
                    //self.update_db(&right_subtree_hash, (Some(true), next_old_path.to_non_reduced_scalar(), val_for_old_key));
                    (left_subtree_hash, right_subtree_hash)
                } else {
                    (self.update_one_val_subtree(&next_new_path, val_for_new_key,
                                                 &next_old_path, val_for_old_key, depth+1),
                     self.empty_tree_hashes[depth+1].clone())
                }
            }
        };

        let root = mimc(&left, &right, self.hash_constants);
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
        mimc(&l, &r, self.hash_constants)
    }

    fn update_db(&mut self, key: &Scalar, val: DBVal) {
        let k = key.to_bytes();
        //println!("Adding to db={:?}", key);
        //println!("Adding to db val={:?}", &val);
        println!("Adding to db key-val {:?}=({:?}, {:?}, {:?})", scalar_to_u64_array(key), &val.0, scalar_to_u64_array(&val.1), scalar_to_u64_array(&val.2));
        /*if self.db.get(&k).is_some() {
            println!("Root already present: {:?}", &k);
        }*/
        self.db.insert(k, val);
    }

    fn get_from_db(&self, key: &Scalar) -> &DBVal {
        // TODO: Raise an error when root is not present in db
        /*if !self.empty_tree_hashes.contains(key) {
            println!("{:?} not in empty hashes", key);
        } else {
            println!("empty hashes = {:?}", &self.empty_tree_hashes);
        }*/
        let k = key.to_bytes();
        let val = self.db.get(&k).unwrap();
        println!("Getting from db {:?}=({:?}, {:?}, {:?})", scalar_to_u64_array(key), &val.0, scalar_to_u64_array(&val.1), scalar_to_u64_array(&val.2));
        val
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand::SeedableRng;
    use super::rand::rngs::StdRng;

    #[test]
    fn test_optmz_sparse_merkle_tree() {
        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);

        // Generate the MiMC round constants
        //let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();
        let constants = (0..MIMC_ROUNDS).map(|i| Scalar::one()).collect::<Vec<_>>();
        let mut tree = OptmzSparseMerkleTree::new(&constants);

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
            assert!(tree.verify_proof(s, s, &proof_vec, &tree.root));
        }

        //let kvs: Vec<(Scalar, Scalar)> = (0..10).map(|_| (Scalar::random(&mut test_rng), Scalar::random(&mut test_rng))).collect();
        let kvs: Vec<(Scalar, Scalar)> = vec![(Scalar::from(7227u32), Scalar::from(7227u32)), (Scalar::from(7700u32), Scalar::from(7700u32))];
        for i in 0..kvs.len() {
            println!("Setting {:?}={:?}", scalar_to_u64_array(&kvs[i].0), scalar_to_u64_array(&kvs[i].1));
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            println!("Getting key {:?}", scalar_to_u64_array(&kvs[i].0));
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }

    }
}