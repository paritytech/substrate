use ark_ec::{
    bls12,
    bls12::{Bls12, Bls12Config, TwistType},
};

use crate::*;

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub struct Config;

impl Bls12Config for Config {
    const X: &'static [u64] = &[0x8508c00000000001];
    /// `x` is positive.
    const X_IS_NEGATIVE: bool = false;
    const TWIST_TYPE: TwistType = TwistType::D;
    type Fp = Fq;
    type Fp2Config = Fq2Config;
    type Fp6Config = Fq6Config;
    type Fp12Config = Fq12Config;
    type G1Config = g1::Config;
    type G2Config = g2::Config;
}

pub type Bls12_377 = Bls12<Config>;

pub type G1Affine = bls12::G1Affine<Config>;
pub type G1Projective = bls12::G1Projective<Config>;
pub type G2Affine = bls12::G2Affine<Config>;
pub type G2Projective = bls12::G2Projective<Config>;

pub use g1::{G1TEAffine, G1TEProjective};
