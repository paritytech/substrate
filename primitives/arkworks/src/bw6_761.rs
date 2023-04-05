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
	final_exponentiation_generic, msm_sw_generic, mul_affine_generic, mul_projective_generic,
	multi_miller_loop_generic,
};
use ark_bw6_761::{g1, g2, BW6_761};
use sp_std::vec::Vec;

/// Compute multi miller loop through arkworks
pub fn multi_miller_loop(a: Vec<Vec<u8>>, b: Vec<Vec<u8>>) -> Result<Vec<u8>, ()> {
	multi_miller_loop_generic::<BW6_761>(a, b)
}

/// Compute final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Result<Vec<u8>, ()> {
	final_exponentiation_generic::<BW6_761>(target)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g1(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_sw_generic::<g1::Config>(bases, scalars)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm_g2(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_sw_generic::<g2::Config>(bases, scalars)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_projective_generic::<g1::Config>(base, scalar)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_projective_generic::<g2::Config>(base, scalar)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g1(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_affine_generic::<g1::Config>(base, scalar)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_g2(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_affine_generic::<g2::Config>(base, scalar)
}
