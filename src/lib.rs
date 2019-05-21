extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

pub mod scalar_utils;
pub mod r1cs_utils;
pub mod factors;
pub mod gadget_not_equals;
pub mod gadget_bound_check;
pub mod gadget_range_proof;
pub mod gadget_set_membership;
pub mod gadget_set_membership_1;
pub mod gadget_set_non_membership;
pub mod gadget_zero_nonzero;
pub mod gadget_mimc;
pub mod gadget_vsmt;
pub mod gadget_osmt;    /// This is incomplete
pub mod gadget_poseidon;