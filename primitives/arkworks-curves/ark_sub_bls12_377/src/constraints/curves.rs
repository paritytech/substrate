use ark_ec::{bls12::Bls12Config, CurveConfig};
use ark_r1cs_std::{
    fields::fp::FpVar,
    groups::{bls12, curves::twisted_edwards::AffineVar as TEAffineVar},
};

use crate::Config;

/// An element of G1 in the BLS12-377 bilinear group.
pub type G1Var = bls12::G1Var<Config>;
/// An element of G2 in the BLS12-377 bilinear group.
pub type G2Var = bls12::G2Var<Config>;

/// An element of G1 (in TE Affine form) in the BLS12-377 bilinear group.
pub type G1TEAffineVar = TEAffineVar<
    <Config as Bls12Config>::G1Config,
    FpVar<<<Config as Bls12Config>::G1Config as CurveConfig>::BaseField>,
>;

/// Represents the cached precomputation that can be performed on a G1 element
/// which enables speeding up pairing computation.
pub type G1PreparedVar = bls12::G1PreparedVar<Config>;
/// Represents the cached precomputation that can be performed on a G2 element
/// which enables speeding up pairing computation.
pub type G2PreparedVar = bls12::G2PreparedVar<Config>;

#[test]
fn test() {
    use ark_ec::models::bls12::Bls12Config;
    ark_curve_constraint_tests::curves::sw_test::<<Config as Bls12Config>::G1Config, G1Var>()
        .unwrap();
    ark_curve_constraint_tests::curves::te_test::<
        <Config as Bls12Config>::G1Config,
        G1TEAffineVar,
    >()
    .unwrap();
    ark_curve_constraint_tests::curves::sw_test::<<Config as Bls12Config>::G2Config, G2Var>()
        .unwrap();
}
