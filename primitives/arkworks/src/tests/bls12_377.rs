use ark_algebra_test_templates::*;
use sp_ark_bls12_377::{
	Bls12_377 as Bls12_377Host, G1Projective as G1ProjectiveHost, G2Projective as G2ProjectiveHost,
	HostFunctions,
};

#[derive(PartialEq, Eq)]
struct Host;

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
	fn bls12_377_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_mul_projective_g1(base, scalar)
	}
	fn bls12_377_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bls12_377_mul_projective_g2(base, scalar)
	}
}

type Bls12_377 = Bls12_377Host<Host>;
type G1Projective = G1ProjectiveHost<Host>;
type G2Projective = G2ProjectiveHost<Host>;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bls12_377>; msm);
test_pairing!(pairing; super::Bls12_377);
