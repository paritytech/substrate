#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    // warnings,
    // unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the BW6_761 curve generated in [\[EG20\]](https://eprint.iacr.org/2020/351).
//! The name denotes that it is a curve generated using the Brezing--Weng
//! method, and that its embedding degree is 6.
//! The main feature of this curve is that the scalar field equals the base
//! field of the BLS12_377 curve.
//!
//! Curve information:
//! * Base field: q = 6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299
//! * Scalar field: r = 258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177
//! * valuation(q - 1, 2) = 1
//! * valuation(r - 1, 2) = 46
//!
//! G1 curve equation: y^2 = x^3 + ax + b, where
//! * a = 0,
//! * b = -1,
//!
//! G2 curve equation: y^2 = x^3 + Ax + B
//! * A = 0
//! * B = 4

mod curves;

pub use ark_bw6_761::{fq, fq3, fq6, fr, Fq, Fq3Config, Fq6Config, Fr};
pub use curves::*;
