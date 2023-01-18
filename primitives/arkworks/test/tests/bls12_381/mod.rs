use ark_algebra_test_templates::*;
use ark_ff::{fields::Field, UniformRand, Zero};
use sp_ark_models::{AffineRepr, CurveGroup, Group};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{rand::Rng, test_rng, vec, vec::Vec, One};

use sp_ark_bls12_381::{
	Fq, Fq2, Fr, G1Affine as G1Affine_Host, G1Projective as G1Projective_Host,
	G2Affine as G2Affine_Host, G2Projective as G2Projective_Host, HostFunctions,
};

pub struct Host {}

impl HostFunctions for Host {
	fn bls12_381_multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_multi_miller_loop(a, b)
	}
	fn bls12_381_final_exponentiation(f12: Vec<u8>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_final_exponentiation(f12)
	}
	fn bls12_381_msm_g1(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_msm_g1(bases, bigints)
	}
	fn bls12_381_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_mul_projective_g1(base, scalar)
	}
	fn bls12_381_mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_mul_affine_g1(base, scalar)
	}
	fn bls12_381_msm_g2(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_msm_g2(bases, bigints)
	}
	fn bls12_381_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_mul_projective_g2(base, scalar)
	}
	fn bls12_381_mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
		sp_io::elliptic_curves::bls12_381_mul_affine_g2(base, scalar)
	}
}

type G1Projective = G1Projective_Host<Host>;
type G1Affine = G1Affine_Host<Host>;
type G2Projective = G2Projective_Host<Host>;
type G2Affine = G2Affine_Host<Host>;

test_group!(g1; sp_ark_bls12_381::G1Projective<super::Host>; sw);
test_group!(g2; sp_ark_bls12_381::G2Projective<super::Host>; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<sp_ark_bls12_381::Bls12_381<super::Host>>; msm);
test_pairing!(pairing; sp_ark_bls12_381::Bls12_381<super::Host>);

#[test]
fn test_g1_endomorphism_beta() {
	assert!(sp_ark_bls12_381::g1::BETA.pow(&[3u64]).is_one());
}

#[test]
fn test_g1_subgroup_membership_via_endomorphism() {
	let mut rng = test_rng();
	let generator = G1Projective::rand(&mut rng).into_affine();
	assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_g1_subgroup_non_membership_via_endomorphism() {
	let mut rng = test_rng();
	loop {
		let x = Fq::rand(&mut rng);
		let greatest = rng.gen();

		if let Some(p) = G1Affine::get_point_from_x_unchecked(x, greatest) {
			if !<sp_ark_models::short_weierstrass::Projective<sp_ark_bls12_381::g1::Config<Host>> as ark_std::Zero>::is_zero(&p.mul_bigint(Fr::characteristic())) {
                assert!(!p.is_in_correct_subgroup_assuming_on_curve());
                return;
            }
		}
	}
}

#[test]
fn test_g2_subgroup_membership_via_endomorphism() {
	let mut rng = test_rng();
	let generator = G2Projective::rand(&mut rng).into_affine();
	assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_g2_subgroup_non_membership_via_endomorphism() {
	let mut rng = test_rng();
	loop {
		let x = Fq2::rand(&mut rng);
		let greatest = rng.gen();

		if let Some(p) = G2Affine::get_point_from_x_unchecked(x, greatest) {
			if !<sp_ark_models::short_weierstrass::Projective<sp_ark_bls12_381::g2::Config::<Host>> as ark_std::Zero>::is_zero(&p.mul_bigint(Fr::characteristic())) {
                assert!(!p.is_in_correct_subgroup_assuming_on_curve());
                return;
            }
		}
	}
}

// Test vectors and macro adapted from https://github.com/zkcrypto/bls12_381/blob/e224ad4ea1babfc582ccd751c2bf128611d10936/src/tests/mod.rs
macro_rules! test_vectors {
	($projective:ident, $affine:ident, $compress:expr, $expected:ident) => {
		let mut e = $projective::zero();

		let mut v = vec![];
		{
			let mut expected = $expected;
			for _ in 0..1000 {
				let e_affine = $affine::from(e);
				let mut serialized = vec![0u8; e.serialized_size($compress)];
				e_affine.serialize_with_mode(serialized.as_mut_slice(), $compress).unwrap();
				v.extend_from_slice(&serialized[..]);

				let mut decoded = serialized;
				let len_of_encoding = decoded.len();
				(&mut decoded[..]).copy_from_slice(&expected[0..len_of_encoding]);
				expected = &expected[len_of_encoding..];
				let decoded =
					$affine::deserialize_with_mode(&decoded[..], $compress, Validate::Yes).unwrap();
				assert_eq!(e_affine, decoded);

				e += &$projective::generator();
			}
		}

		assert_eq!(&v[..], $expected);
	};
}

#[test]
fn g1_compressed_valid_test_vectors() {
	let bytes: &'static [u8] = include_bytes!("g1_compressed_valid_test_vectors.dat");
	test_vectors!(G1Projective, G1Affine, Compress::Yes, bytes);
}

#[test]
fn g1_uncompressed_valid_test_vectors() {
	let bytes: &'static [u8] = include_bytes!("g1_uncompressed_valid_test_vectors.dat");
	test_vectors!(G1Projective, G1Affine, Compress::No, bytes);
}

#[test]
fn g2_compressed_valid_test_vectors() {
	let bytes: &'static [u8] = include_bytes!("g2_compressed_valid_test_vectors.dat");
	test_vectors!(G2Projective, G2Affine, Compress::Yes, bytes);
}

#[test]
fn g2_uncompressed_valid_test_vectors() {
	let bytes: &'static [u8] = include_bytes!("g2_uncompressed_valid_test_vectors.dat");
	test_vectors!(G2Projective, G2Affine, Compress::No, bytes);
}
