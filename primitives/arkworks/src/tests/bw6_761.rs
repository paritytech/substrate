use ark_algebra_test_templates::*;
use sp_ark_bw6_761::{
	G1Projective as G1ProjectiveHost, G2Projective as G2ProjectiveHost, HostFunctions,
	BW6_761 as BW6_761Host,
};

#[derive(PartialEq, Eq)]
struct Host;

impl HostFunctions for Host {
	fn bw6_761_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_multi_miller_loop(a, b)
	}
	fn bw6_761_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_final_exponentiation(f12)
	}
	fn bw6_761_msm_g1(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_msm_g1(bases, bigints)
	}
	fn bw6_761_msm_g2(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_msm_g2(bases, bigints)
	}
	fn bw6_761_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_mul_projective_g1(base, scalar)
	}
	fn bw6_761_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::bw6_761_mul_projective_g2(base, scalar)
	}
}

type BW6_761 = BW6_761Host<Host>;
type G1Projective = G1ProjectiveHost<Host>;
type G2Projective = G2ProjectiveHost<Host>;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<BW6_761>; msm);
test_pairing!(pairing; super::BW6_761);
