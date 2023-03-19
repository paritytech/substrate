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
use ark_ec::{models::CurveConfig, twisted_edwards, AffineRepr, Group, VariableBaseMSM};
use ark_ed_on_bls12_377::{EdwardsConfig, EdwardsProjective};
use ark_ff::Zero;
use ark_serialize::{CanonicalSerialize, Compress};
use sp_std::vec::Vec;

/// Compute a multi scalar multiplication on G! through arkworks
pub fn msm(bases: Vec<u8>, scalars: Vec<u8>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.chunks(twisted_edwards::Affine::<EdwardsConfig>::generator().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<twisted_edwards::Affine<EdwardsConfig>>(&a.to_vec()))
		.collect();
	let scalars: Vec<_> = scalars
		.chunks(<EdwardsConfig as CurveConfig>::ScalarField::zero().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<<EdwardsConfig as CurveConfig>::ScalarField>(&a.to_vec()))
		.collect();

	let result = <EdwardsProjective as VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}
