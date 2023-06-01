// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! The main elliptic curves trait, allowing Substrate to call into host functions
//! for operations on elliptic curves.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod bls12_377;
pub mod bls12_381;
pub mod bw6_761;
pub mod ed_on_bls12_377;
pub mod ed_on_bls12_381_bandersnatch;
mod utils;

use sp_runtime_interface::runtime_interface;

/// Interfaces for working with elliptic curves related types from within the runtime.
#[runtime_interface]
pub trait EllipticCurves {
	/// Compute a multi Miller loop on bls12_381
	fn bls12_381_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::multi_miller_loop(a, b)
	}

	/// Compute a final exponentiation on bls12_381
	fn bls12_381_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::final_exponentiation(f12)
	}

	/// Compute a projective multiplication on G1 for bls12_381
	fn bls12_381_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::mul_projective_g1(base, scalar)
	}

	/// Compute a projective multiplication on G2 for bls12_381
	fn bls12_381_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::mul_projective_g2(base, scalar)
	}

	/// Compute a msm on G1 for bls12_381
	fn bls12_381_msm_g1(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::msm_g1(bases, scalars)
	}

	/// Compute a msm on G2 for bls12_381
	fn bls12_381_msm_g2(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_381::msm_g2(bases, scalars)
	}

	/// Compute a multi Miller loop for bls12_377
	fn bls12_377_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::multi_miller_loop(a, b)
	}

	/// Compute a final exponentiation for bls12_377
	fn bls12_377_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::final_exponentiation(f12)
	}

	/// Compute a projective multiplication on G1 for bls12_377
	fn bls12_377_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::mul_projective_g1(base, scalar)
	}

	/// Compute a projective multiplication on G2 for bls12_377
	fn bls12_377_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::mul_projective_g2(base, scalar)
	}

	/// Compute a msm on G1 for bls12_377
	fn bls12_377_msm_g1(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::msm_g1(bases, scalars)
	}

	/// Compute a msm on G2 for bls12_377
	fn bls12_377_msm_g2(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		bls12_377::msm_g2(bases, scalars)
	}

	/// Compute a multi Miller loop on bw6_761
	fn bw6_761_multi_miller_loop(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::multi_miller_loop(a, b)
	}

	/// Compute a final exponentiation on bw6_761
	fn bw6_761_final_exponentiation(f12: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::final_exponentiation(f12)
	}

	/// Compute a projective multiplication on G1 for bw6_761
	fn bw6_761_mul_projective_g1(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::mul_projective_g1(base, scalar)
	}

	/// Compute a projective multiplication on G2 for bw6_761
	fn bw6_761_mul_projective_g2(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::mul_projective_g2(base, scalar)
	}

	/// Compute a msm on G1 for bw6_761
	fn bw6_761_msm_g1(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::msm_g1(bases, bigints)
	}

	/// Compute a msm on G2 for bw6_761
	fn bw6_761_msm_g2(bases: Vec<u8>, bigints: Vec<u8>) -> Result<Vec<u8>, ()> {
		bw6_761::msm_g2(bases, bigints)
	}

	/// Compute twisted edwards projective multiplication on ed_on_bls12_381_bandersnatch
	fn ed_on_bls12_381_bandersnatch_te_mul_projective(
		base: Vec<u8>,
		scalar: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		ed_on_bls12_381_bandersnatch::te_mul_projective(base, scalar)
	}

	/// Compute short weierstrass projective multiplication on ed_on_bls12_381_bandersnatch
	fn ed_on_bls12_381_bandersnatch_sw_mul_projective(
		base: Vec<u8>,
		scalar: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		ed_on_bls12_381_bandersnatch::sw_mul_projective(base, scalar)
	}

	/// Compute twisted edwards msm on ed_on_bls12_381_bandersnatch
	fn ed_on_bls12_381_bandersnatch_te_msm(
		bases: Vec<u8>,
		scalars: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		ed_on_bls12_381_bandersnatch::te_msm(bases, scalars)
	}

	/// Compute short weierstrass msm on ed_on_bls12_381_bandersnatch
	fn ed_on_bls12_381_bandersnatch_sw_msm(
		bases: Vec<u8>,
		scalars: Vec<u8>,
	) -> Result<Vec<u8>, ()> {
		ed_on_bls12_381_bandersnatch::sw_msm(bases, scalars)
	}

	/// Compute short weierstrass msm on ed_on_bls12_381_bandersnatch
	fn ed_on_bls12_381_sw_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		ed_on_bls12_381_bandersnatch::sw_msm(bases, scalars)
	}

	/// Compute projective multiplication on ed_on_bls12_377
	fn ed_on_bls12_377_mul_projective(base: Vec<u8>, scalar: Vec<u8>) -> Result<Vec<u8>, ()> {
		ed_on_bls12_377::mul_projective(base, scalar)
	}

	/// Compute msm on ed_on_bls12_377
	fn ed_on_bls12_377_msm(bases: Vec<u8>, scalars: Vec<u8>) -> Result<Vec<u8>, ()> {
		ed_on_bls12_377::msm(bases, scalars)
	}
}
