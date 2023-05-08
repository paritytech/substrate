use ark_algebra_test_templates::*;
use sp_ark_ed_on_bls12_381_bandersnatch::{
	EdwardsProjective as EdwardsProjectiveHost, HostFunctions, SWProjective as SWProjectiveHost,
};

pub struct Host {}

impl HostFunctions for Host {
	fn ed_on_bls12_381_bandersnatch_te_msm(
		bases: Vec<u8>,
		scalars: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_bandersnatch_te_msm(bases, scalars)
	}
	fn ed_on_bls12_381_bandersnatch_sw_msm(
		bases: Vec<u8>,
		scalars: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_bandersnatch_sw_msm(bases, scalars)
	}
	fn ed_on_bls12_381_bandersnatch_te_mul_projective(
		base: Vec<u8>,
		scalar: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_bandersnatch_te_mul_projective(base, scalar)
	}
	fn ed_on_bls12_381_bandersnatch_sw_mul_projective(
		base: Vec<u8>,
		scalar: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_381_bandersnatch_sw_mul_projective(base, scalar)
	}
}

type EdwardsProjective = EdwardsProjectiveHost<Host>;
type SWProjective = SWProjectiveHost<Host>;

test_group!(sw; SWProjective; sw);
test_group!(te; EdwardsProjective; te);
