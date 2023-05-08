use ark_algebra_test_templates::*;
use sp_ark_ed_on_bls12_377::{EdwardsProjective as EdwardsProjectiveHost, HostFunctions};

struct Host {}

impl HostFunctions for Host {
	fn ed_on_bls12_377_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_377_msm(bases, scalars)
	}
	fn ed_on_bls12_377_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_377_mul_projective(base, scalar)
	}
}

type EdwardsProjective = EdwardsProjectiveHost<Host>;
test_group!(te; EdwardsProjective; te);
