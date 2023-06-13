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

//! Support functions for ed_on_bls12_377 to improve the performance of
//! msm and projective multiplication by host function calls

use crate::utils::{msm_te_generic, mul_projective_te_generic};
use ark_ed_on_bls12_377::EdwardsConfig;
use sp_std::vec::Vec;

/// Compute a multi scalar mulitplication for twisted_edwards through
/// arkworks.
pub fn msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
	msm_te_generic::<EdwardsConfig>(bases, scalars)
}

/// Compute a projective scalar multiplication for twisted_edwards
/// through arkworks.
pub fn mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
	mul_projective_te_generic::<EdwardsConfig>(base, scalar)
}

#[cfg(test)]
mod tests {
	use super::*;
	use ark_algebra_test_templates::*;
	use sp_ark_ed_on_bls12_377::{EdwardsProjective as EdwardsProjectiveHost, HostFunctions};

	struct Host {}

	impl HostFunctions for Host {
		fn ed_on_bls12_377_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::ed_on_bls12_377_msm(bases, scalars)
		}
		fn ed_on_bls12_377_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::ed_on_bls12_377_mul_projective(base, scalar)
		}
	}

	type EdwardsProjective = EdwardsProjectiveHost<Host>;
	test_group!(te; EdwardsProjective; te);
}
