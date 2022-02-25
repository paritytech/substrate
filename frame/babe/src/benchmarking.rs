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
		const EQUIVOCATION_PROOF_BLOB: [u8; 608] = [
		222, 241, 46, 66, 243, 228, 135, 233, 177, 64, 149, 170, 141, 92, 193, 106, 51, 73, 31, 27, 80,
		218, 220, 248, 129, 29, 20, 128, 243, 250, 134, 39, 11, 0, 0, 0, 0, 0, 0, 0, 76, 44, 146, 70, 13,
		144, 172, 166, 131, 232, 192, 232, 11, 130, 187, 196, 243, 254, 92, 49, 2, 82, 238, 240, 212, 100,
		170, 156, 240, 4, 43, 126, 40, 12, 0, 204, 33, 63, 244, 44, 139, 179, 194, 115, 92, 133, 148, 6, 74,
		222, 223, 242, 5, 66, 108, 124, 211, 214, 122, 182, 77, 133, 235, 18, 142, 3, 23, 10, 46, 117, 151,
		183, 183, 227, 216, 76, 5, 57, 29, 19, 154, 98, 177, 87, 231, 135, 134, 216, 192, 130, 242, 157, 207,
		76, 17, 19, 20, 8, 6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69,
		1, 1, 164, 207, 115, 166, 87, 251, 195, 118, 57, 170, 0, 235, 172, 214, 191, 168, 119, 152, 142, 204,
		213, 60, 8, 0, 245, 12, 81, 175, 182, 51, 217, 91, 175, 47, 115, 140, 127, 143, 89, 236, 200, 158, 78,
		43, 89, 232, 209, 94, 223, 41, 110, 244, 0, 7, 105, 121, 231, 75, 65, 195, 91, 126, 47, 133, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 44, 146, 70, 13, 144,
		172, 166, 131, 232, 192, 232, 11, 130, 187, 196, 243, 254, 92, 49, 2, 82, 238, 240, 212, 100, 170, 156,
		240, 4, 43, 126, 40, 12, 0, 204, 33, 63, 244, 44, 139, 179, 194, 115, 92, 133, 148, 6, 74, 222, 223,
		242, 5, 66, 108, 124, 211, 214, 122, 182, 77, 133, 235, 18, 142, 3, 23, 10, 46, 117, 151, 183, 183, 227,
		216, 76, 5, 57, 29, 19, 154, 98, 177, 87, 231, 135, 134, 216, 192, 130, 242, 157, 207, 76, 17, 19, 20, 8,
		6, 66, 65, 66, 69, 52, 2, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 5, 66, 65, 66, 69, 1, 1, 186, 47, 118, 136,
		32, 133, 160, 159, 5, 188, 32, 115, 221, 1, 31, 94, 131, 26, 217, 7, 30, 182, 154, 212, 66, 110, 49, 97,
		98, 134, 209, 69, 203, 110, 58, 59, 253, 81, 219, 182, 193, 81, 7, 94, 27, 235, 13, 116, 176, 243, 57, 205,
		100, 190, 63, 234, 137, 97, 220, 28, 151, 171, 19, 139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0];

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

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::*;

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
				CurrentSlot::<Test>::get() + 1,
			);

			println!("equivocation_proof: {:?}", equivocation_proof);
			println!("equivocation_proof.encode(): {:?}", equivocation_proof.encode());
		});
	}
}
