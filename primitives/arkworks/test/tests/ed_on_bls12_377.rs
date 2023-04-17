use ark_algebra_test_templates::*;
use ark_std::vec::Vec;
use sp_ark_ed_on_bls12_377::HostFunctions;

pub struct Host {}

impl HostFunctions for Host {
	fn ed_on_bls12_377_msm(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Result<Vec<u8>, ()> {
		sp_io::elliptic_curves::ed_on_bls12_377_msm(bases, scalars)
	}
}

test_group!(te; sp_ark_ed_on_bls12_377::EdwardsProjective<super::Host>; te);
