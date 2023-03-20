#![cfg_attr(not(feature = "std"), no_std)]

pub mod bls12_377;
pub mod bls12_381;
pub mod bw6_761;
pub mod ed_on_bls12_377;
pub mod ed_on_bls12_381;
mod utils;

/// Error computing an elliptic curve pairing
#[derive(Encode, Decode, Debug)]
pub enum PairingError {
	#[codec(index = 1)]
	InternalPanic,
	#[codec(index = 2)]
	FinalExpInverse,
	#[codec(index = 3)]
	MillerLoopCofactor,
}
