use ark_algebra_test_templates::*;

test_group!(g1; sp_ark_bls12_377::curves::g1::G1Projective; sw);
test_group!(g2; sp_ark_bls12_377::curves::g2::G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<sp_ark_bls12_377::curves::Bls12_377>; msm);
test_pairing!(pairing; sp_ark_bls12_377::curves::Bls12_377);
