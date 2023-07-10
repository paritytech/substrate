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

//! Support functions for bw6_761 to improve the performance of
//! multi_miller_loop, final_exponentiation, msm's and projective
//! multiplications by host function calls.

use crate::utils::{
	final_exponentiation_generic, msm_sw_generic, mul_projective_generic, multi_miller_loop_generic,
};
use ark_bw6_761::{g1, g2, BW6_761};
use sp_std::vec::Vec;

/// Compute a multi miller loop through arkworks
pub fn multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
	multi_miller_loop_generic::<BW6_761>(a, b)
}

/// Compute a final exponentiation through arkworks
pub fn final_exponentiation(target: Vec<u8>) -> Result<Vec<u8>, ()> {
	final_exponentiation_generic::<BW6_761>(target)
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

/// Compute a projective scalar multiplication for short_weierstrass through
/// arkworks on G1.
pub fn mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
	mul_projective_generic::<g1::Config>(base, scalar)
}

/// Compute a projective scalar multiplication for short_weierstrass through
/// arkworks on G2.
pub fn mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
	mul_projective_generic::<g2::Config>(base, scalar)
}

#[cfg(test)]
mod tests {
	use super::*;
	use ark_algebra_test_templates::*;
	use sp_ark_bw6_761::{
		G1Projective as G1ProjectiveHost, G2Projective as G2ProjectiveHost, HostFunctions,
		BW6_761 as BW6_761Host,
	};

	#[derive(PartialEq, Eq)]
	struct Host;

	impl HostFunctions for Host {
		fn bw6_761_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_multi_miller_loop(a, b)
		}
		fn bw6_761_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_final_exponentiation(f12)
		}
		fn bw6_761_msm_g1(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_msm_g1(bases, bigints)
		}
		fn bw6_761_msm_g2(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_msm_g2(bases, bigints)
		}
		fn bw6_761_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_mul_projective_g1(base, scalar)
		}
		fn bw6_761_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
			crate::elliptic_curves::bw6_761_mul_projective_g2(base, scalar)
		}
	}

	type BW6_761 = BW6_761Host<Host>;
	type G1Projective = G1ProjectiveHost<Host>;
	type G2Projective = G2ProjectiveHost<Host>;

	test_group!(g1; G1Projective; sw);
	test_group!(g2; G2Projective; sw);
	test_group!(pairing_output; ark_ec::pairing::PairingOutput<BW6_761>; msm);
	test_pairing!(pairing; super::BW6_761);
}
