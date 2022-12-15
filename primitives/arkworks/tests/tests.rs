use ark_algebra_test_templates::{msm::test_var_base_msm, test_pairing, test_group};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_sub_bls12_381::{
	Bls12_381 as Bls12_381_Host, Fr as BlsFr, G1Affine as G1Affine_Host,
	G1Projective as G1Projective_Host, G2Affine as G2Affine_Host,
	G2Projective as G2Projective_Host, HostFunctions,
};
use sp_arkworks::bls12_381;
use sp_std::vec;

pub struct Host {}

impl HostFunctions for Host {
	fn bls12_381_multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Vec<u8> {
		bls12_381::multi_miller_loop(a, b)
	}
	fn bls12_381_final_exponentiation(f12: &[u8]) -> Vec<u8> {
		bls12_381::final_exponentiation(f12)
	}
	fn bls12_381_bigint_msm_g1(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		bls12_381::msm_bigint_g1(bases, bigints)
	}
	fn bls12_381_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		bls12_381::mul_projective_g1(base, scalar)
	}
	fn bls12_381_mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		bls12_381::mul_affine_g1(base, scalar)
	}
	fn bls12_381_bigint_msm_g2(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		bls12_381::msm_bigint_g2(bases, bigints)
	}
	fn bls12_381_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		bls12_381::mul_projective_g2(base, scalar)
	}
	fn bls12_381_mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		bls12_381::mul_affine_g2(base, scalar)
	}
}

type Bls12_381 = Bls12_381_Host<Host>;
type G1Affine = G1Affine_Host<Host>;
type G2Affine = G2Affine_Host<Host>;
type G1Projective = G1Projective_Host<Host>;
type G2Projective = G2Projective_Host<Host>;

test_pairing!(pairing; crate::Bls12_381);
// test_group!(g1; crate::G1Projective; sw);

#[cfg(test)]
mod tests {
    use super::*;
	#[test]
	fn bls12_381_msm() {
		test_var_base_msm::<G1Projective>();
	}
}
