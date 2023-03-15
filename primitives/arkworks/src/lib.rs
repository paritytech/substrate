#![cfg_attr(not(feature = "std"), no_std)]
use codec::{Decode, Encode};

pub mod bls12_377;
pub mod bls12_381;
pub mod bw6_761;
pub mod ed_on_bls12_377;
pub mod ed_on_bls12_381;
mod utils;

/// Error computing an elliptic curve pairing
#[derive(Encode, Decode)]
pub enum PairingError {
	InternalPanic,
	FinalExpInverse,
	MillerLoopCofactor,
}
