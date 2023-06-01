// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Support functions for bls12_381 to improve the performance of
//! multi_miller_loop, final_exponentiation, msm's and projective
//! multiplications by host function calls

use crate::utils::{
	final_exponentiation_generic, msm_sw_generic, mul_projective_generic, multi_miller_loop_generic,
};
use ark_bls12_381::{g1, g2, Bls12_381};
use sp_std::vec::Vec;

/// Compute a multi miller loop through arkworks
pub fn multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
	multi_miller_loop_generic::<Bls12_381>(a, b)
}

/// Compute a final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Result<Vec<u8>, ()> {
	final_exponentiation_generic::<Bls12_381>(target)
}

/// Compute a multi scalar multiplication for short_weierstrass through
/// arkworks on G1.
pub fn msm_g1(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
	msm_sw_generic::<g1::Config>(bases, scalars)
}

/// Compute a multi scalar multiplication for short_weierstrass through
/// arkworks on G2.
pub fn msm_g2(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
	msm_sw_generic::<g2::Config>(bases, scalars)
}

/// Compute a projective scalar multiplication for short_weierstrass
/// through arkworks on G1.
pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
	mul_projective_generic::<g1::Config>(base, scalar)
}

/// Compute a projective scalar multiplication for short_weierstrass
/// through arkworks on G2.
pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
	mul_projective_generic::<g2::Config>(base, scalar)
}

#[cfg(test)]
mod tests {
	use super::*;
	use ark_algebra_test_templates::*;
	use ark_ec::{AffineRepr, CurveGroup, Group};
	use ark_ff::{fields::Field, One, Zero};
	use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
	use ark_std::{rand::Rng, test_rng, vec, UniformRand};
	use sp_ark_bls12_381::{
		fq::Fq, fq2::Fq2, fr::Fr, Bls12_381 as Bls12_381Host, G1Affine as G1AffineHost,
		G1Projective as G1ProjectiveHost, G2Affine as G2AffineHost,
		G2Projective as G2ProjectiveHost, HostFunctions,
	};
	use sp_ark_models::pairing::PairingOutput;

	#[derive(PartialEq, Eq)]
	struct Host;

	impl HostFunctions for Host {
		fn bls12_381_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_multi_miller_loop(a, b)
		}
		fn bls12_381_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_final_exponentiation(f12)
		}
		fn bls12_381_msm_g1(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_msm_g1(bases, bigints)
		}
		fn bls12_381_msm_g2(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_msm_g2(bases, bigints)
		}
		fn bls12_381_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_mul_projective_g1(base, scalar)
		}
		fn bls12_381_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bls12_381_mul_projective_g2(base, scalar)
		}
	}

	type Bls12_381 = Bls12_381Host<Host>;
	type G1Projective = G1ProjectiveHost<Host>;
	type G2Projective = G2ProjectiveHost<Host>;
	type G1Affine = G1AffineHost<Host>;
	type G2Affine = G2AffineHost<Host>;

	test_group!(g1; G1Projective; sw);
	test_group!(g2; G2Projective; sw);
	test_group!(pairing_output; PairingOutput<Bls12_381>; msm);
	test_pairing!(ark_pairing; super::Bls12_381);

	#[test]
	fn test_g1_endomorphism_beta() {
		assert!(sp_ark_bls12_381::g1::BETA.pow([3u64]).is_one());
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
				if !<G1Projective as ark_std::Zero>::is_zero(&p.mul_bigint(Fr::characteristic())) {
					assert!(!p.is_in_correct_subgroup_assuming_on_curve());
					return
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
				if !<G2Projective as Zero>::is_zero(&p.mul_bigint(Fr::characteristic())) {
					assert!(!p.is_in_correct_subgroup_assuming_on_curve());
					return
				}
			}
		}
	}

	// Test vectors and macro adapted from https://github.com/zkcrypto/bls12_381/blob/e224ad4ea1babfc582ccd751c2bf128611d10936/src/test-data/mod.rs
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
						$affine::deserialize_with_mode(&decoded[..], $compress, Validate::Yes)
							.unwrap();
					assert_eq!(e_affine, decoded);

					e += &$projective::generator();
				}
			}

			assert_eq!(&v[..], $expected);
		};
	}

	#[test]
	fn g1_compressed_valid_test_vectors() {
		let bytes: &'static [u8] = include_bytes!("test-data/g1_compressed_valid_test_vectors.dat");
		test_vectors!(G1Projective, G1Affine, Compress::Yes, bytes);
	}

	#[test]
	fn g1_uncompressed_valid_test_vectors() {
		let bytes: &'static [u8] =
			include_bytes!("test-data/g1_uncompressed_valid_test_vectors.dat");
		test_vectors!(G1Projective, G1Affine, Compress::No, bytes);
	}

	#[test]
	fn g2_compressed_valid_test_vectors() {
		let bytes: &'static [u8] = include_bytes!("test-data/g2_compressed_valid_test_vectors.dat");
		test_vectors!(G2Projective, G2Affine, Compress::Yes, bytes);
	}

	#[test]
	fn g2_uncompressed_valid_test_vectors() {
		let bytes: &'static [u8] =
			include_bytes!("test-data/g2_uncompressed_valid_test_vectors.dat");
		test_vectors!(G2Projective, G2Affine, Compress::No, bytes);
	}
}
