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

use ark_ed_on_bls12_381::{EdwardsAffine, EdwardsProjective, JubjubParameters};
use ark_ec::{
	models::CurveConfig,
	pairing::{MillerLoopOutput, Pairing},
	Group, VariableBaseMSM,
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, Zero};
use sp_std::{vec, vec::Vec};

// /// Compute a scalar multiplication on G2 through arkworks
// pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
// 	let cursor = Cursor::new(base);
// 	let base = G2Projective::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
	
// 	let cursor = Cursor::new(scalar);
// 	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
// 	let mut res = EdwardsProjective::mul_bigint(&self, other);
// 	let mut res = ark_ec::bls12::G2Projective::<Parameters>::zero();
// 	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
// 		res.double_in_place();
// 		if b {
// 			res += base;
// 		}
// 	}
// 	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
// 	let mut cursor = Cursor::new(&mut serialized[..]);
// 	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
// 	serialized
// }

// /// Compute a scalar multiplication on G2 through arkworks
// pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
// 	let cursor = Cursor::new(base);
// 	let base = G1Projective::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

// 	let cursor = Cursor::new(scalar);
// 	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
// 	let mut res = ark_ec::bls12::G1Projective::<Parameters>::zero();
// 	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
// 		res.double_in_place();
// 		if b {
// 			res += base;
// 		}
// 	}
// 	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
// 	let mut cursor = Cursor::new(&mut serialized[..]);
// 	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
// 	serialized
// }

// /// Compute a scalar multiplication on G2 through arkworks
// pub fn mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
// 	let cursor = Cursor::new(base);
// 	let base = G1Affine::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

// 	let cursor = Cursor::new(scalar);
// 	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
// 	let mut res = ark_ec::bls12::G1Projective::<Parameters>::zero();
// 	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
// 		res.double_in_place();
// 		if b {
// 			res += base;
// 		}
// 	}
// 	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
// 	let mut cursor = Cursor::new(&mut serialized[..]);
// 	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
// 	serialized
// }

// /// Compute a scalar multiplication on G2 through arkworks
// pub fn mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
// 	let cursor = Cursor::new(base);
// 	let base = G2Affine::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();

// 	let cursor = Cursor::new(scalar);
// 	let scalar = Vec::<u64>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
// 	let mut res = ark_ec::bls12::G2Projective::<Parameters>::zero();
// 	for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
// 		res.double_in_place();
// 		if b {
// 			res += base;
// 		}
// 	}
// 	let mut serialized = vec![0; res.serialized_size(Compress::Yes)];
// 	let mut cursor = Cursor::new(&mut serialized[..]);
// 	res.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
// 	serialized
// }

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| {
			let cursor = Cursor::new(a);
			ark_ec::twisted_edwards::Affine::<JubjubParameters>::deserialize_with_mode(
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
			<JubjubParameters as CurveConfig>::ScalarField::deserialize_with_mode(
				cursor,
				Compress::Yes,
				Validate::No,
			)
			.unwrap()
		})
		.collect();
	
	let result = <EdwardsProjective as VariableBaseMSM>::msm(&bases, &scalars);
	let mut serialized = vec![0; result.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized[..]);
	result.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
	serialized
}

// /// Compute a multi scalar multiplication on G! through arkworks
// pub fn msm_bigint_g2(bases: Vec<Vec<u8>>, bigints: Vec<Vec<u8>>) -> Vec<u8> {
// 	let bases: Vec<_> = bases
// 		.iter()
// 		.map(|a| {
// 			let cursor = Cursor::new(a);
// 			<Bls12_381 as Pairing>::G2Affine::deserialize_with_mode(
// 				cursor,
// 				Compress::Yes,
// 				Validate::No,
// 			)
// 			.unwrap()
// 		})
// 		.collect();
// 	let bigints: Vec<_> = bigints
// 		.iter()
// 		.map(|a| {
// 			let cursor = Cursor::new(a);
// 			<<ark_bls12_381::g2::Parameters as CurveConfig>::ScalarField as PrimeField>::BigInt::deserialize_with_mode(
// 				cursor,
// 				Compress::Yes,
// 				Validate::No,
// 			)
// 			.unwrap()
// 		})
// 		.collect();
// 	let result =
// 		<<Bls12_381 as Pairing>::G2 as ark_ec::VariableBaseMSM>::msm_bigint(&bases, &bigints);
// 	let mut serialized = vec![0; result.serialized_size(Compress::Yes)];
// 	let mut cursor = Cursor::new(&mut serialized[..]);
// 	result.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
// 	serialized
// }
