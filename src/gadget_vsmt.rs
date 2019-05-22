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

use crate::scalar_utils::{ScalarBytes, TreeDepth, ScalarBits, get_bits};
use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};
use crate::gadget_mimc::{mimc, MIMC_ROUNDS, mimc_hash_2, mimc_gadget};


type DBVal = (Scalar, Scalar);

pub struct VanillaSparseMerkleTree<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<Scalar>,
    db: HashMap<ScalarBytes, DBVal>,
    hash_constants: &'a [Scalar],
    pub root: Scalar
}

impl<'a> VanillaSparseMerkleTree<'a> {
    pub fn new(hash_constants: &'a [Scalar]) -> VanillaSparseMerkleTree<'a> {
        let depth = TreeDepth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<Scalar> = vec![];
        empty_tree_hashes.push(Scalar::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i-1];
            let new = mimc(&prev, &prev, hash_constants);
            let key = new.to_bytes();

            db.insert(key, (prev, prev));
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_constants,
            root
        }
    }

    pub fn update(&mut self, idx: Scalar, val: Scalar) -> Scalar {

        // Find path to insert the new key
        let mut sidenodes_wrap = Some(Vec::<Scalar>::new());
        self.get(idx, &mut sidenodes_wrap);
        let mut sidenodes: Vec<Scalar> = sidenodes_wrap.unwrap();

        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            let side_elem = sidenodes.pop().unwrap();
            let new_val = {
                if cur_idx.is_lsb_set() {
                    // LSB is set, so put new value on right
                    let h =  mimc(&side_elem, &cur_val, self.hash_constants);
                    self.update_db_with_key_val(h, (side_elem, cur_val));
                    h
                } else {
                    // LSB is unset, so put new value on left
                    let h =  mimc(&cur_val, &side_elem, self.hash_constants);
                    self.update_db_with_key_val(h, (cur_val, side_elem));
                    h
                }
            };
            //println!("Root at level {} is {:?}", i, &cur_val);
            cur_idx.shr();
            cur_val = new_val;
        }

        self.root = cur_val;

        cur_val
    }

    /// Get a value from tree, if `proof` is not None, populate `proof` with the merkle proof
    pub fn get(&self, idx: Scalar, proof: &mut Option<Vec<Scalar>>) -> Scalar {
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<Scalar>::new();

        for i in 0..self.depth {
            let k = cur_node.to_bytes();
            let v = self.db.get(&k).unwrap();
            if cur_idx.is_msb_set() {
                // MSB is set, traverse to right subtree
                cur_node = v.1;
                if need_proof { proof_vec.push(v.0); }
            } else {
                // MSB is unset, traverse to left subtree
                cur_node = v.0;
                if need_proof { proof_vec.push(v.1); }
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

    /// Verify a merkle proof, if `root` is None, use the current root else use given root
    pub fn verify_proof(&self, idx: Scalar, val: Scalar, proof: &[Scalar], root: Option<&Scalar>) -> bool {
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            cur_val = {
                if cur_idx.is_lsb_set() {
                    mimc(&proof[self.depth-1-i], &cur_val, self.hash_constants)
                } else {
                    mimc(&cur_val, &proof[self.depth-1-i], self.hash_constants)
                }
            };

            cur_idx.shr();
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


/// left = (1-leaf_side) * leaf + (leaf_side * proof_node)
/// right = leaf_side * leaf + ((1-leaf_side) * proof_node))
pub fn vanilla_merkle_merkle_tree_verif_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    root: &Scalar,
    leaf_val: AllocatedScalar,
    leaf_index_bits: Vec<AllocatedScalar>,
    proof_nodes: Vec<AllocatedScalar>,
    mimc_rounds: usize,
    mimc_constants: &[Scalar]
) -> Result<(), R1CSError> {

    let mut prev_hash = LinearCombination::default();

    for i in 0..depth {
        let leaf_val_lc = if i == 0 {
            LinearCombination::from(leaf_val.variable)
        } else {
            prev_hash.clone()
        };
        let one_minus_leaf_side: LinearCombination = Variable::One() - leaf_index_bits[i].variable;

        let (_, _, left_1) = cs.multiply(one_minus_leaf_side.clone(), leaf_val_lc.clone());
        let (_, _, left_2) = cs.multiply(leaf_index_bits[i].variable.into(), proof_nodes[i].variable.into());
        let left = left_1 + left_2;

        let (_, _, right_1) = cs.multiply(leaf_index_bits[i].variable.into(), leaf_val_lc);
        let (_, _, right_2) = cs.multiply(one_minus_leaf_side, proof_nodes[i].variable.into());
        let right = right_1 + right_2;

        prev_hash = mimc_hash_2::<CS>(cs, left, right, mimc_rounds, mimc_constants)?;
    }

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

    pub fn is_lsb_set(scalar: &Scalar) -> bool {
        (scalar.as_bytes()[0] & 1u8) == 1
    }

    // Check that bit 252 (0-indexing) is set or not
    pub fn is_msb_set(scalar: &Scalar) -> bool {
        // 252 >> 3 = 31
        // 252 & 7 = 4
        ((scalar.as_bytes()[31] >> 4) & 1u8) == 1
    }

    pub fn mul2(scalar: &Scalar) -> Scalar {
        scalar * Scalar::from(2u8)
    }

    pub fn div2(scalar: &Scalar) -> Scalar {
        let inv_2 = Scalar::from_canonical_bytes(
            [247, 233, 122, 46, 141, 49, 9, 44, 107, 206, 123, 81, 239, 124, 111, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]
        ).unwrap();
        scalar * inv_2
    }
    /*fn count_set_bits(bits: &[i8; 256]) -> u8 {
        let mut c = 0;
        for i in bits.iter() {
            if *i == 1i8 {
                c += 1;
            }
        }
        c
    }

    #[test]
    fn test_msb_lsb() {
        let two = Scalar::from(2u128);
        let _256 = Scalar::from(256u128);
        let _257 = Scalar::from(257u128);
        let _258 = Scalar::from(258u128);
        assert_eq!(is_lsb_set(&Scalar::zero()), false);
        assert_eq!(is_lsb_set(&Scalar::one()), true);
        assert_eq!(is_lsb_set(&two), false);
        assert_eq!(is_lsb_set(&_256), false);
        assert_eq!(is_lsb_set(&_257), true);
        assert_eq!(is_lsb_set(&_258), false);

        assert_eq!(is_msb_set(&Scalar::zero()), false);
        assert_eq!(is_msb_set(&Scalar::one()), false);
        assert_eq!(is_msb_set(&two), false);
        assert_eq!(is_msb_set(&_256), false);
        assert_eq!(is_msb_set(&_257), false);
        assert_eq!(is_msb_set(&_258), false);

        let l = BASEPOINT_ORDER;
        let l_minus_1 = l - Scalar::one();
        let t_252 = l - Scalar::from(27742317777372353535851937790883648493 as u128);
        let t_252_minus_1 = t_252 - Scalar::one();
        let t_252_plus_1 = t_252 + Scalar::one();
        assert_eq!(is_msb_set(&l), true);
        assert_eq!(is_msb_set(&l_minus_1), true);
        assert_eq!(is_msb_set(&t_252), true);
        assert_eq!(is_msb_set(&t_252_minus_1), false);
        assert_eq!(is_msb_set(&t_252_plus_1), true);
    }

    #[test]
    fn test_mul2_div2() {
        let x = Scalar::from(6 as u32);
        assert_eq!(Scalar::from(3 as u32), div2(&x));
        assert_eq!(Scalar::from(12 as u32), mul2(&x));
        let mut csprng: OsRng = OsRng::new().unwrap();

        for _ in 0..100 {
            let r: Scalar = Scalar::random(&mut csprng);
            let r2 = mul2(&r);
            assert_eq!(r, div2(&r2));
        }
    }*/

    #[test]
    fn test_vanilla_sparse_merkle_tree() {
        let mut test_rng: OsRng = OsRng::new().unwrap();;

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();
        let mut tree = VanillaSparseMerkleTree::new(&constants);

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<Scalar>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(s, s, &proof_vec, None));
            assert!(tree.verify_proof(s, s, &proof_vec, Some(&tree.root)));
        }

        let kvs: Vec<(Scalar, Scalar)> = (0..100).map(|_| (Scalar::random(&mut test_rng), Scalar::random(&mut test_rng))).collect();
        for i in 0..kvs.len() {
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }

    #[test]
    fn test_field_ops() {
        let one = Scalar::from(257u128);
        println!("one is {:?}", one);
        println!("one as bytes {:?}", one.as_bytes());
        //println!("one as bits {:?}", get_bits(&one).to_vec());

        let two = Scalar::from(2 as u32);
        let inv_2 = two.invert();
        println!("inv_2 is {:?}", inv_2);
        let x = Scalar::from(6 as u32);
        println!("x/2 {:?}", x*inv_2);


        let t = Scalar::from(256 as u32);
        let m = std::u128::MAX;
        let m1 = Scalar::from(m as u128) + Scalar::one();
        println!("m1 is {:?}", m1);
        let m2 = (m1 * t);
        println!("m2 is {:?}", m2);

        let mut r = Scalar::one();
        for i in 0..256 {
            r = r * two;
            /*println!("for i={} , r.is_canonical = {}", i, r.is_canonical());
            println!("For i={}, bit count={}", i, count_set_bits(&get_bits(&r)));
            println!("for i={} last byte={:?}", i, r.as_bytes()[31]);*/
        }

        let l = BASEPOINT_ORDER;
        println!("BASEPOINT_ORDER as bits {:?}", get_bits(&BASEPOINT_ORDER).to_vec());

        let y = Scalar::from(1u32);
        let mut b1 = vec![];
        let mut b2 = vec![];

        let mut z1 = y.clone();
        println!("z1 as bits {:?}", get_bits(&z1).to_vec());
        for i in 0..253 {
            if is_msb_set(&z1) {
                b1.push(1)
            } else {
                b1.push(0)
            }
            z1 = mul2(&z1);
        }

        let mut z2 = y.clone();
        println!("z2 as bits {:?}", get_bits(&z2).to_vec());
        for i in 0..253 {
            if is_lsb_set(&z2) {
                b2.insert(0, 1)
            } else {
                b2.insert(0, 0)
            }
            z2 = div2(&z2);
        }

        println!("b1 is {:?}", b1);
        println!("b2 is {:?}", b2);

        assert_eq!(b1, b2);
    }

    #[test]
    fn test_VSMT_Verif() {
        let mut test_rng: OsRng = OsRng::new().unwrap();;

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();
        let mut tree = VanillaSparseMerkleTree::new(&constants);

        for i in 1..=10 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        let mut proof_vec = Vec::<Scalar>::new();
        let mut proof = Some(proof_vec);
        let k =  Scalar::from(7u32);
        assert_eq!(k, tree.get(k, &mut proof));
        proof_vec = proof.unwrap();
        assert!(tree.verify_proof(k, k, &proof_vec, None));
        assert!(tree.verify_proof(k, k, &proof_vec, Some(&tree.root)));

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(8192, 1);

        let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"VSMT");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let (com_leaf, var_leaf) = prover.commit(k, Scalar::random(&mut test_rng));
            let mut leaf_alloc_scalar = AllocatedScalar {
                variable: var_leaf,
                assignment: Some(k),
            };

            let mut leaf_index_comms = vec![];
            let mut leaf_index_vars = vec![];
            let mut leaf_index_alloc_scalars = vec![];
            for b in get_bits(&k).iter().take(tree.depth) {
                let val: Scalar = Scalar::from(*b as u8);
                let (c, v) = prover.commit(val.clone(), Scalar::random(&mut test_rng));
                leaf_index_comms.push(c);
                leaf_index_vars.push(v);
                leaf_index_alloc_scalars.push(AllocatedScalar {
                    variable: v,
                    assignment: Some(val),
                });
            }

            let mut proof_comms = vec![];
            let mut proof_vars = vec![];
            let mut proof_alloc_scalars = vec![];
            for p in proof_vec.iter().rev() {
                let (c, v) = prover.commit(*p, Scalar::random(&mut test_rng));
                proof_comms.push(c);
                proof_vars.push(v);
                proof_alloc_scalars.push(AllocatedScalar {
                    variable: v,
                    assignment: Some(*p),
                });
            }

            let start = Instant::now();
            assert!(vanilla_merkle_merkle_tree_verif_gadget(
                &mut prover,
                tree.depth,
                &tree.root,
                leaf_alloc_scalar,
                leaf_index_alloc_scalars,
                proof_alloc_scalars,
                                MIMC_ROUNDS,
                                &constants).is_ok());

//            println!("For tree height {} and MiMC rounds {}, no of constraints is {}", tree.depth, &MIMC_ROUNDS, &prover.num_constraints());

            let proof = prover.prove(&bp_gens).unwrap();
            let end = start.elapsed();

            println!("Proving time is {:?} seconds", end);

            (proof, (com_leaf, leaf_index_comms, proof_comms))
        };

        let mut verifier_transcript = Transcript::new(b"VSMT");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_leaf = verifier.commit(commitments.0);
        let mut leaf_alloc_scalar = AllocatedScalar {
            variable: var_leaf,
            assignment: None,
        };

        let mut leaf_index_alloc_scalars = vec![];
        for l in commitments.1 {
            let v = verifier.commit(l);
            leaf_index_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }

        let mut proof_alloc_scalars = vec![];
        for p in commitments.2 {
            let v = verifier.commit(p);
            proof_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }

        let start = Instant::now();
        assert!(vanilla_merkle_merkle_tree_verif_gadget(
            &mut verifier,
            tree.depth,
            &tree.root,
            leaf_alloc_scalar,
            leaf_index_alloc_scalars,
            proof_alloc_scalars,
            MIMC_ROUNDS,
            &constants).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        let end = start.elapsed();

        println!("Verification time is {:?} seconds", end);
    }
}