// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use frame_benchmarking::benchmarks;

type Header = sp_runtime::generic::Header<u64, sp_runtime::traits::BlakeTwo256>;

benchmarks! {
	check_equivocation_proof {
		let x in 0 .. 1;

		// NOTE: generated with the test below `test_generate_equivocation_report_blob`.
		// the output is not deterministic since keys are generated randomly (and therefore
		// signature content changes). it should not affect the benchmark.
		// with the current benchmark setup it is not possible to generate this programatically
		// from the benchmark setup.
		const EQUIVOCATION_PROOF_BLOB: [u8; 416] = [222, 241, 46, 66, 243, 228, 135, 233, 177, 64, 149, 170, 141, 92, 193, 106, 51, 73, 31, 27, 80, 218, 220, 248, 129, 29, 20, 128, 243, 250, 134, 39, 11, 0, 0, 0, 0, 0, 0, 0, 151, 111, 34, 84, 204, 159, 149, 150, 145, 159, 46, 85, 194, 59, 38, 7, 140, 194, 18, 219, 47, 114, 10, 166, 185, 24, 43, 186, 79, 107, 161, 239, 40, 165, 150, 53, 188, 62, 210, 242, 74, 199, 221, 186, 140, 28, 5, 97, 12, 20, 12, 74, 78, 61, 109, 178, 62, 11, 34, 57, 111, 24, 197, 124, 121, 3, 23, 10, 46, 117, 151, 183, 183, 227, 216, 76, 5, 57, 29, 19, 154, 98, 177, 87, 231, 135, 134, 216, 192, 130, 242, 157, 207, 76, 17, 19, 20, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 252, 174, 112, 151, 169, 71, 87, 129, 149, 25, 92, 39, 178, 209, 7, 218, 249, 246, 105, 17, 224, 31, 227, 61, 198, 4, 43, 16, 239, 199, 149, 46, 2, 75, 56, 105, 90, 114, 19, 124, 167, 217, 11, 70, 15, 28, 139, 160, 204, 72, 177, 74, 84, 5, 18, 94, 139, 42, 76, 51, 197, 1, 222, 142, 151, 111, 34, 84, 204, 159, 149, 150, 145, 159, 46, 85, 194, 59, 38, 7, 140, 194, 18, 219, 47, 114, 10, 166, 185, 24, 43, 186, 79, 107, 161, 239, 40, 165, 150, 53, 188, 62, 210, 242, 74, 199, 221, 186, 140, 28, 5, 97, 12, 20, 12, 74, 78, 61, 109, 178, 62, 11, 34, 57, 111, 24, 197, 124, 121, 3, 23, 10, 46, 117, 151, 183, 183, 227, 216, 76, 5, 57, 29, 19, 154, 98, 177, 87, 231, 135, 134, 216, 192, 130, 242, 157, 207, 76, 17, 19, 20, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 38, 156, 193, 156, 7, 174, 253, 207, 53, 225, 56, 119, 11, 170, 181, 27, 149, 86, 122, 21, 214, 107, 61, 23, 31, 118, 93, 234, 190, 31, 65, 108, 175, 94, 21, 209, 196, 137, 166, 207, 160, 119, 141, 243, 52, 173, 102, 165, 23, 69, 177, 193, 93, 98, 71, 50, 209, 93, 46, 250, 233, 186, 249, 138];

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
