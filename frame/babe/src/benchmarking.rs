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

//! Benchmarks for the BABE Pallet.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::v1::benchmarks;

type Header = sp_runtime::generic::Header<u64, sp_runtime::traits::BlakeTwo256>;

benchmarks! {
	check_equivocation_proof {
		let x in 0 .. 1;

		// NOTE: generated with the test below `test_generate_equivocation_report_blob`.
		// the output is not deterministic since keys are generated randomly (and therefore
		// signature content changes). it should not affect the benchmark.
		// with the current benchmark setup it is not possible to generate this programatically
		// from the benchmark setup.
		const EQUIVOCATION_PROOF_BLOB: [u8; 416] = [
			222, 241, 46, 66, 243, 228, 135, 233, 177, 64, 149, 170, 141, 92, 193, 106, 51, 73, 31,
			27, 80, 218, 220, 248, 129, 29, 20, 128, 243, 250, 134, 39, 11, 0, 0, 0, 0, 0, 0, 0,
			158, 4, 7, 240, 67, 153, 134, 190, 251, 196, 229, 95, 136, 165, 234, 228, 255, 18, 2,
			187, 76, 125, 108, 50, 67, 33, 196, 108, 38, 115, 179, 86, 40, 36, 27, 5, 105, 58, 228,
			94, 198, 65, 212, 218, 213, 61, 170, 21, 51, 249, 182, 121, 101, 91, 204, 25, 31, 87,
			219, 208, 43, 119, 211, 185, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11,
			0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 188, 192, 217, 91, 138, 78, 217, 80, 8,
			29, 140, 55, 242, 210, 170, 184, 73, 98, 135, 212, 236, 209, 115, 52, 200, 79, 175,
			172, 242, 161, 199, 47, 236, 93, 101, 95, 43, 34, 141, 16, 247, 220, 33, 59, 31, 197,
			27, 7, 196, 62, 12, 238, 236, 124, 136, 191, 29, 36, 22, 238, 242, 202, 57, 139, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			0, 40, 23, 175, 153, 83, 6, 33, 65, 123, 51, 80, 223, 126, 186, 226, 225, 240, 105, 28,
			169, 9, 54, 11, 138, 46, 194, 201, 250, 48, 242, 125, 117, 116, 0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 6, 66, 65,
			66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 142, 12,
			124, 11, 167, 227, 103, 88, 78, 23, 228, 33, 96, 41, 207, 183, 227, 189, 114, 70, 254,
			30, 128, 243, 233, 83, 214, 45, 74, 182, 120, 119, 64, 243, 219, 119, 63, 240, 205,
			123, 231, 82, 205, 174, 143, 70, 2, 86, 182, 20, 16, 141, 145, 91, 116, 195, 58, 223,
			175, 145, 255, 7, 121, 133
		];

		let equivocation_proof1: sp_consensus_babe::EquivocationProof<Header> =
			Decode::decode(&mut &EQUIVOCATION_PROOF_BLOB[..]).unwrap();

		let equivocation_proof2 = equivocation_proof1.clone();
	}: {
		sp_consensus_babe::check_equivocation_proof::<Header>(equivocation_proof1);
	} verify {
		assert!(sp_consensus_babe::check_equivocation_proof::<Header>(equivocation_proof2));
	}

	impl_benchmark_test_suite!(
		Pallet,
		crate::mock::new_test_ext(3),
		crate::mock::Test,
	)
}
