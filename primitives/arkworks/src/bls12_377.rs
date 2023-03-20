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

use crate::{utils::{deserialize_argument, serialize_result}, PairingError};
use ark_bls12_377::{g1, g2, Bls12_377, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{
	models::CurveConfig,
	pairing::{MillerLoopOutput, Pairing},
	short_weierstrass::SWCurveConfig,
};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
use ark_std::io::Cursor;
use sp_std::vec::Vec;

/// Compute multi miller loop through arkworks

pub fn multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Result<Vec<u8>, PairingError> {
	multi_miller_loop_generic::<Bls12_377>(a, b)
}

/// Compute final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Result<Vec<u8>, PairingError> {
	final_exponentiation_generic::<Bls12_377>(target)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g1(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_g1_generic::<Bls12_377>(bases, scalars)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g2(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_g2_generic::<Bls12_377>(bases, scalars)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<G2Projective>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <g2::Config as SWCurveConfig>::mul_projective(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<G1Projective>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <g1::Config as SWCurveConfig>::mul_projective(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<G1Affine>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <g1::Config as SWCurveConfig>::mul_affine(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<G2Affine>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <g2::Config as SWCurveConfig>::mul_affine(&base, &scalar);

	serialize_result(result)
}