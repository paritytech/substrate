// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use super::*;
use frame_benchmarking::benchmarks;

type Header = sp_runtime::generic::Header<u64, sp_runtime::traits::BlakeTwo256>;

benchmarks! {
	_ {	}

	check_equivocation_proof {
		let x in 0 .. 1;

		// NOTE: generated with the test below `test_generate_equivocation_report_blob`.
		// the output is not deterministic since keys are generated randomly (and therefore
		// signature content changes). it should not affect the benchmark.
		// with the current benchmark setup it is not possible to generate this programatically
		// from the benchmark setup.
		const EQUIVOCATION_PROOF_BLOB: [u8; 608] = 
		[222, 241, 46, 66, 243, 228, 135, 233, 177, 64, 149, 170, 141, 92, 193, 106, 51, 73,
		31, 27, 80, 218, 220, 248, 129, 29, 20, 128, 243, 250, 134, 39, 11, 0, 0, 0, 0, 0, 0,
		0, 69, 226, 97, 131, 181, 167, 43, 160, 70, 55, 249, 6, 255, 28, 248, 88, 192, 145,
		32, 237, 161, 214, 90, 173, 188, 53, 155, 155, 150, 173, 28, 192, 40, 234, 4, 27, 230,
		11, 202, 160, 112, 152, 119, 2, 142, 71, 217, 150, 52, 124, 209, 251, 135, 222, 227, 141,
		106, 180, 31, 125, 219, 226, 198, 138, 198, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0,
		0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 60, 20, 93, 221, 43, 179, 180, 255,
		165, 121, 104, 246, 58, 101, 242, 253, 216, 44, 84, 90, 204, 185, 187, 17, 0, 182, 193,
		139, 143, 145, 77, 108, 64, 8, 8, 88, 19, 89, 152, 218, 69, 34, 11, 166, 61, 125, 112,
		232, 83, 253, 69, 226, 87, 237, 74, 73, 234, 66, 128, 107, 250, 123, 206, 128, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 86, 159, 100, 37, 240, 116, 137, 63, 99, 196, 141, 72, 36,
		97, 33, 107, 148, 178, 211, 135, 72, 178, 226, 250, 119, 207, 141, 93, 233, 194, 18, 108,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69,
		1, 1, 230, 247, 56, 224, 81, 164, 33, 178, 25, 206, 140, 109, 160, 171, 18, 177, 88, 194,
		124, 25, 209, 120, 23, 23, 190, 136, 140, 93, 241, 19, 59, 110, 24, 213, 106, 147, 115,
		127, 192, 60, 107, 175, 106, 127, 142, 67, 230, 106, 2, 251, 21, 230, 245, 78, 201, 87,
		30, 7, 229, 241, 246, 226, 183, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

		let equivocation_proof1: sp_consensus_babe::EquivocationProof<Header> =
			Decode::decode(&mut &EQUIVOCATION_PROOF_BLOB[..]).unwrap();

		let equivocation_proof2 = equivocation_proof1.clone();
	}: {
		sp_consensus_babe::check_equivocation_proof::<Header>(equivocation_proof1);
	} verify {
		assert!(sp_consensus_babe::check_equivocation_proof::<Header>(equivocation_proof2));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::*;
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext(3).execute_with(|| {
			assert_ok!(test_benchmark_check_equivocation_proof::<Test>());
		})
	}

	#[test]
	fn test_generate_equivocation_report_blob() {
		let (pairs, mut ext) = new_test_ext_with_pairs(3);

		let offending_authority_index = 0;
		let offending_authority_pair = &pairs[0];

		ext.execute_with(|| {
			start_era(1);

			let equivocation_proof = generate_equivocation_proof(
				offending_authority_index,
				offending_authority_pair,
				CurrentSlot::get() + 1,
			);

			println!("equivocation_proof: {:?}", equivocation_proof);
			println!(
				"equivocation_proof.encode(): {:?}",
				equivocation_proof.encode()
			);
		});
	}
}
