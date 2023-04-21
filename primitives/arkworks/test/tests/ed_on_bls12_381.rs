use ark_algebra_test_templates::*;
use ark_std::vec::Vec;
use sp_ark_ed_on_bls12_381::HostFunctions;

pub struct Host {}

impl HostFunctions for Host {
	fn ed_on_bls12_381_te_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_te_msm(bases, scalars)
	}
	fn ed_on_bls12_381_sw_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_sw_msm(bases, scalars)
	}
	fn ed_on_bls12_381_te_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_te_mul_projective(base, scalar)
	}
	fn ed_on_bls12_381_sw_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_sw_mul_projective(base, scalar)
	}
}

test_group!(sw; sp_ark_ed_on_bls12_381::SWProjective<super::Host>; sw);
test_group!(te; sp_ark_ed_on_bls12_381::EdwardsProjective<super::Host>; te);
