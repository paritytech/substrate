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

//! Hashing Functions.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use ark_bw6_761::{Config, G1Affine, G1Projective, G2Affine, G2Projective, BW6_761};
use ark_ec::{
	models::CurveConfig,
	pairing::{MillerLoopOutput, Pairing},
	Group,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, Zero};
use sp_std::{vec, vec::Vec};

/// Compute multi pairing through arkworksrk_BW6_761::G2Projective
pub fn multi_pairing(vec_a: Vec<Vec<u8>>, vec_b: Vec<Vec<u8>>) -> Vec<u8> {
	let g1: Vec<_> = vec_a
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<BW6_761 as Pairing>::G1Prepared::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let g2: Vec<_> = vec_b
		.iter()
		.map(|b| {
			let cursor = Cursor::new(b);
			<BW6_761 as Pairing>::G2Affine::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let res = BW6_761::multi_pairing(g1, g2);
	// serialize the result
	let mut res_bytes = vec![0u8; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut res_bytes[..]);
	res.0.serialize_compressed(&mut cursor).unwrap();
	res_bytes.to_vec()
}

/// Compute multi miller loop through arkworks
pub fn multi_miller_loop(a_vec: Vec<Vec<u8>>, b_vec: Vec<Vec<u8>>) -> Vec<u8> {
	let g1: Vec<_> = a_vec
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<BW6_761 as Pairing>::G1Affine::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.map(<BW6_761 as Pairing>::G1Prepared::from)
			.unwrap()
		})
		.collect();
	let g2: Vec<_> = b_vec
		.iter()
		.map(|b| {
			let cursor = Cursor::new(b);
			<BW6_761 as Pairing>::G2Affine::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.map(<BW6_761 as Pairing>::G2Prepared::from)
			.unwrap()
		})
		.collect();
	let res = BW6_761::multi_miller_loop(g1, g2);
	// serialize the result
	let mut res_bytes = vec![0u8; res.0.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut res_bytes[..]);
	res.0.serialize_compressed(&mut cursor).unwrap();
	res_bytes.to_vec()
}

/// Compute final exponentiation through arkworks
pub fn final_exponentiation(target: &[u8]) -> Vec<u8> {
	let cursor = Cursor::new(target);
	let target = <BW6_761 as Pairing>::TargetField::deserialize_with_mode(
		cursor,
		Compress::Yes,
		Validate::No,
	)
	.unwrap();
	let res = BW6_761::final_exponentiation(MillerLoopOutput(target)).unwrap();
	// serialize the result
	let mut res_bytes = vec![0u8; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut res_bytes[..]);
	res.0.serialize_compressed(&mut cursor).unwrap();
	res_bytes.to_vec()
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let cursor = Cursor::new(base);
	let base = G2Projective::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

	let cursor = Cursor::new(scalar);
	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
	let mut res = ark_ec::bw6::G2Projective::<Config>::zero();
	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
		res.double_in_place();
		if b {
			res += base;
		}
	}
	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let cursor = Cursor::new(base);
	let base = G1Projective::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

	let cursor = Cursor::new(scalar);
	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
	let mut res = ark_ec::bw6::G1Projective::<Config>::zero();
	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
		res.double_in_place();
		if b {
			res += base;
		}
	}
	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let cursor = Cursor::new(base);
	let base = G1Affine::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

	let cursor = Cursor::new(scalar);
	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
	let mut res = ark_ec::bw6::G1Projective::<Config>::zero();
	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
		res.double_in_place();
		if b {
			res += base;
		}
	}
	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let cursor = Cursor::new(base);
	let base = G2Affine::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

	let cursor = Cursor::new(scalar);
	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
	let mut res = ark_ec::bw6::G2Projective::<Config>::zero();
	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
		res.double_in_place();
		if b {
			res += base;
		}
	}
	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_bigint_g1(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<BW6_761 as Pairing>::G1Affine::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<ark_bw6_761::g1::Config as CurveConfig>::ScalarField::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let result =
		<<BW6_761 as Pairing>::G1 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();
	let mut serialized = vec![0; result.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	result.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_bigint_g2(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<BW6_761 as Pairing>::G2Affine::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			<ark_bw6_761::g2::Config as CurveConfig>::ScalarField::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	let result =
		<<BW6_761 as Pairing>::G2 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();
	let mut serialized = vec![0; result.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	result.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}
