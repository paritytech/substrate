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

use crate::utils::{deserialize_argument, serialize_result};
use ark_bw6_761::BW6_761;
use ark_ec::{
	models::CurveConfig,
	pairing::{MillerLoopOutput, Pairing},
};
use sp_std::vec::Vec;

/// Compute multi miller loop through arkworks
pub fn multi_miller_loop(a_vec: Vec<Vec<u8>>, b_vec: Vec<Vec<u8>>) -> Vec<u8> {
	let g1: Vec<_> = a_vec
		.iter()
		.map(|a| deserialize_argument::<<BW6_761 as Pairing>::G1Affine>(a))
		.collect();
	let g2: Vec<_> = b_vec
		.iter()
		.map(|b| deserialize_argument::<<BW6_761 as Pairing>::G2Affine>(b))
		.collect();

	let result = BW6_761::multi_miller_loop(g1, g2).0;

	serialize_result(result)
}

/// Compute final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Vec<u8> {
	let target = deserialize_argument::<<BW6_761 as Pairing>::TargetField>(&target);

	let result = BW6_761::final_exponentiation(MillerLoopOutput(target)).unwrap().0;

	serialize_result(result)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g1(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| deserialize_argument::<<BW6_761 as Pairing>::G1Affine>(a))
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| deserialize_argument::<<ark_bw6_761::g1::Config as CurveConfig>::ScalarField>(a))
		.collect();

	let result =
		<<BW6_761 as Pairing>::G1 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g2(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| deserialize_argument::<<BW6_761 as Pairing>::G2Affine>(a))
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| deserialize_argument::<<ark_bw6_761::g2::Config as CurveConfig>::ScalarField>(a))
		.collect();

	let result =
		<<BW6_761 as Pairing>::G2 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}
