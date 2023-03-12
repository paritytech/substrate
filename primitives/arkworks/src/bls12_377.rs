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

use crate::utils::{
	deserialize_argument, final_exponentiation_generic, msm_g1_generic, msm_g2_generic,
	multi_miller_loop_generic, serialize_result,
};
use ark_bls12_377::{g1, g2, Bls12_377};
use ark_ec::{
	models::CurveConfig,
	pairing::{MillerLoopOutput, Pairing},
};
use sp_std::vec::Vec;

/// Compute multi miller loop through arkworks

pub fn multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Vec<u8> {
	multi_miller_loop_generic::<Bls12_377>(a, b)
}

/// Compute final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Vec<u8> {
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
