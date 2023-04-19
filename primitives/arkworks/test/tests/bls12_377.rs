use ark_algebra_test_templates::*;
use ark_std::vec::Vec;
use sp_ark_bls12_377::HostFunctions;

pub struct Host {}

impl HostFunctions for Host {
	fn bls12_377_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_multi_miller_loop(a, b)
	}
	fn bls12_377_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_final_exponentiation(f12)
	}
	fn bls12_377_msm_g1(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_msm_g1(bases, bigints)
	}
	fn bls12_377_msm_g2(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_msm_g2(bases, bigints)
	}
}

test_group!(g1; sp_ark_bls12_377::G1Projective<super::Host>; sw);
test_group!(g2; sp_ark_bls12_377::G2Projective<super::Host>; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<sp_ark_bls12_377::Bls12_377<super::Host>>; msm);
test_pairing!(pairing; sp_ark_bls12_377::Bls12_377<super::Host>);
