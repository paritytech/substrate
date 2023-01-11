use ark_algebra_test_templates::*;
use ark_std::vec::Vec;
use sp_ark_bw6_761::HostFunctions;

#[derive(PartialEq, Eq)]
pub struct Host;

impl HostFunctions for Host {
	fn bw6_761_multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::crypto::bw6_761_multi_miller_loop(a, b)
	}
	fn bw6_761_final_exponentiation(f12: &[u8]) -> Vec<u8> {
		sp_io::crypto::bw6_761_final_exponentiation(f12)
	}
	fn bw6_761_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::crypto::bw6_761_mul_projective_g2(base, scalar)
	}
	fn bw6_761_mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::crypto::bw6_761_mul_affine_g2(base, scalar)
	}
	fn bw6_761_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::crypto::bw6_761_mul_projective_g1(base, scalar)
	}
	fn bw6_761_mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::crypto::bw6_761_mul_affine_g1(base, scalar)
	}
	fn bw6_761_msm_g1(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::crypto::bw6_761_msm_g1(bases, bigints)
	}
	fn bw6_761_msm_g2(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::crypto::bw6_761_msm_g2(bases, bigints)
	}
}

test_group!(g1; sp_ark_bw6_761::g1::G1Projective<super::Host>; sw);
test_group!(g2; sp_ark_bw6_761::g2::G2Projective<super::Host>; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<sp_ark_bw6_761::BW6_761<super::Host>>; msm);
test_pairing!(pairing; sp_ark_bw6_761::BW6_761<super::Host>);
