// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the GRANDPA pallet.

use super::{Pallet as Grandpa, *};
use frame_benchmarking::benchmarks;
use frame_system::RawOrigin;
use sp_core::H256;

benchmarks! {
	check_equivocation_proof {
		let x in 0 .. 1;

		// NOTE: generated with the test below `test_generate_equivocation_report_blob`.
		// the output should be deterministic since the keys we use are static.
		// with the current benchmark setup it is not possible to generate this
		// programatically from the benchmark setup.
		const EQUIVOCATION_PROOF_BLOB: [u8; 257] = [
			1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 136, 220, 52, 23,
			213, 5, 142, 196, 180, 80, 62, 12, 18, 234, 26, 10, 137, 190, 32,
			15, 233, 137, 34, 66, 61, 67, 52, 1, 79, 166, 176, 238, 207, 48,
			195, 55, 171, 225, 252, 130, 161, 56, 151, 29, 193, 32, 25, 157,
			249, 39, 80, 193, 214, 96, 167, 147, 25, 130, 45, 42, 64, 208, 182,
			164, 10, 0, 0, 0, 0, 0, 0, 0, 234, 236, 231, 45, 70, 171, 135, 246,
			136, 153, 38, 167, 91, 134, 150, 242, 215, 83, 56, 238, 16, 119, 55,
			170, 32, 69, 255, 248, 164, 20, 57, 50, 122, 115, 135, 96, 80, 203,
			131, 232, 73, 23, 149, 86, 174, 59, 193, 92, 121, 76, 154, 211, 44,
			96, 10, 84, 159, 133, 211, 56, 103, 0, 59, 2, 96, 20, 69, 2, 32,
			179, 16, 184, 108, 76, 215, 64, 195, 78, 143, 73, 177, 139, 20, 144,
			98, 231, 41, 117, 255, 220, 115, 41, 59, 27, 75, 56, 10, 0, 0, 0, 0,
			0, 0, 0, 128, 179, 250, 48, 211, 76, 10, 70, 74, 230, 219, 139, 96,
			78, 88, 112, 33, 170, 44, 184, 59, 200, 155, 143, 128, 40, 222, 179,
			210, 190, 84, 16, 182, 21, 34, 94, 28, 193, 163, 226, 51, 251, 134,
			233, 187, 121, 63, 157, 240, 165, 203, 92, 16, 146, 120, 190, 229,
			251, 129, 29, 45, 32, 29, 6
		];

		let equivocation_proof1: sp_finality_grandpa::EquivocationProof<H256, u64> =
			Decode::decode(&mut &EQUIVOCATION_PROOF_BLOB[..]).unwrap();

		let equivocation_proof2 = equivocation_proof1.clone();
	}: {
		sp_finality_grandpa::check_equivocation_proof(equivocation_proof1);
	} verify {
		assert!(sp_finality_grandpa::check_equivocation_proof(equivocation_proof2));
	}

	note_stalled {
		let delay = 1000u32.into();
		let best_finalized_block_number = 1u32.into();

	}: _(RawOrigin::Root, delay, best_finalized_block_number)
	verify {
		assert!(Grandpa::<T>::stalled().is_some());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::*;

	frame_benchmarking::impl_benchmark_test_suite!(
		Pallet,
		crate::mock::new_test_ext(vec![(1, 1), (2, 1), (3, 1)]),
		crate::mock::Test,
	);

	#[test]
	fn test_generate_equivocation_report_blob() {
		let authorities = crate::tests::test_authorities();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index].0;
		let equivocation_keyring = extract_keyring(equivocation_key);

		new_test_ext_raw_authorities(authorities).execute_with(|| {
			start_era(1);

			// generate an equivocation proof, with two votes in the same round for
			// different block hashes signed by the same key
			let equivocation_proof = generate_equivocation_proof(
				1,
				(1, H256::random(), 10, &equivocation_keyring),
				(1, H256::random(), 10, &equivocation_keyring),
			);

			println!("equivocation_proof: {:?}", equivocation_proof);
			println!("equivocation_proof.encode(): {:?}", equivocation_proof.encode());
		});
	}
}
