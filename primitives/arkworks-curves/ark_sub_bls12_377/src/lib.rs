#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the BLS12_377 curve generated in [\[BCGMMW20, “Zexe”\]](https://eprint.iacr.org/2018/962).
//! The name denotes that it is a Barreto--Lynn--Scott curve of embedding degree
//! 12, defined over a 377-bit (prime) field. The main feature of this curve is
//! that both the scalar field and the base field are highly 2-adic.
//! (This is in contrast to the BLS12_381 curve for which only the scalar field
//! is highly 2-adic.)
//!
//!
//! Curve information:
//! * Base field: q = 258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177
//! * Scalar field: r =
//!   8444461749428370424248824938781546531375899335154063827935233455917409239041
//! * valuation(q - 1, 2) = 46
//! * valuation(r - 1, 2) = 47
//! * G1 curve equation: y^2 = x^3 + 1
//! * G2 curve equation: y^2 = x^3 + B, where
//!    * B = Fq2(0, 155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906)

#[cfg(feature = "curve")]
mod curves;

mod fields;

#[cfg(feature = "r1cs")]
pub mod constraints;

#[cfg(feature = "curve")]
pub use curves::*;

pub use fields::*;
