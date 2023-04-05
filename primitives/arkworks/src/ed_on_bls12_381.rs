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
	msm_sw_generic, msm_te_generic, mul_affine_generic, mul_affine_te_generic,
	mul_projective_generic, mul_projective_te_generic,
};
use ark_ed_on_bls12_381::JubjubConfig;
use sp_std::vec::Vec;

/// Compute a scalar multiplication on G2 through arkworks
pub fn sw_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_projective_generic::<JubjubConfig>(base, scalar)
}

/// Compute a scalar multiplication through arkworks
pub fn sw_mul_affine(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_affine_generic::<JubjubConfig>(base, scalar)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn te_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_projective_te_generic::<JubjubConfig>(base, scalar)
}

/// Compute a scalar multiplication through arkworks
pub fn te_mul_affine(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	mul_affine_te_generic::<JubjubConfig>(base, scalar)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn te_msm(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_te_generic::<JubjubConfig>(bases, scalars)
}

/// Compute a multi scalar multiplication on G! through arkworks
pub fn sw_msm(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	msm_sw_generic::<JubjubConfig>(bases, scalars)
}
