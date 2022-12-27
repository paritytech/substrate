use crate::{Bls12_377, G1Projective, G2Projective};
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bls12_377>; msm);
test_pairing!(pairing; crate::Bls12_377);
