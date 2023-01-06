#![cfg_attr(not(feature = "std"), no_std)]
pub mod bls12;
pub mod bw6;
pub use ark_ec::{
	models, models::short_weierstrass, pairing, scalar_mul, twisted_edwards, AffineRepr,
	CurveConfig, CurveGroup, Group,
};
