#![cfg_attr(not(feature = "std"), no_std)]
use ark_algebra_test_templates::*;
use ark_ff::{fields::Field, One, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{rand::Rng, test_rng, vec, vec::Vec, UniformRand};
use sp_ark_models::{pairing::PairingOutput, AffineRepr, CurveGroup, Group};

use sp_ark_bls12_381::{
	curves::{
		g1::{G1Affine, G1Projective},
		g2::{G2Affine, G2Projective},
	},
	fq::Fq,
	fq2::Fq2,
	fr::Fr,
};

test_group!(g1; sp_ark_bls12_381::curves::g1::G1Projective; sw);
test_group!(g2; sp_ark_bls12_381::curves::g2::G2Projective; sw);
test_group!(pairing_output; PairingOutput<sp_ark_bls12_381::curves::Bls12_381>; msm);
test_pairing!(ark_pairing; sp_ark_bls12_381::curves::Bls12_381);

#[test]
fn test_g1_endomorphism_beta() {
	assert!(sp_ark_bls12_381::g1::BETA.pow([3u64]).is_one());
}

#[test]
fn test_g1_subgroup_membership_via_endomorphism() {
	let mut rng = test_rng();
	let generator = sp_ark_bls12_381::curves::g1::G1Projective::rand(&mut rng).into_affine();
	assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_g1_subgroup_non_membership_via_endomorphism() {
	let mut rng = test_rng();
	loop {
		let x = Fq::rand(&mut rng);
		let greatest = rng.gen();

		if let Some(p) =
			sp_ark_bls12_381::curves::g1::G1Affine::get_point_from_x_unchecked(x, greatest)
		{
			if !<sp_ark_bls12_381::curves::g1::G1Projective as ark_std::Zero>::is_zero(
				&p.mul_bigint(Fr::characteristic()),
			) {
				assert!(!p.is_in_correct_subgroup_assuming_on_curve());
				return
			}
		}
	}
}

#[test]
fn test_g2_subgroup_membership_via_endomorphism() {
	let mut rng = test_rng();
	let generator = sp_ark_bls12_381::curves::g2::G2Projective::rand(&mut rng).into_affine();
	assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_g2_subgroup_non_membership_via_endomorphism() {
	let mut rng = test_rng();
	loop {
		let x = Fq2::rand(&mut rng);
		let greatest = rng.gen();

		if let Some(p) =
			sp_ark_bls12_381::curves::g2::G2Affine::get_point_from_x_unchecked(x, greatest)
		{
			if !<sp_ark_bls12_381::curves::g2::G2Projective as Zero>::is_zero(
				&p.mul_bigint(Fr::characteristic()),
			) {
				assert!(!p.is_in_correct_subgroup_assuming_on_curve());
				return
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
