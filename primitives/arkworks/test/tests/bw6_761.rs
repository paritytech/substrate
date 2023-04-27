use ark_algebra_test_templates::*;

test_group!(g1; sp_ark_bw6_761::g1::G1Projective; sw);
test_group!(g2; sp_ark_bw6_761::g2::G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<sp_ark_bw6_761::curves::BW6_761>; msm);
test_pairing!(pairing; sp_ark_bw6_761::curves::BW6_761);
