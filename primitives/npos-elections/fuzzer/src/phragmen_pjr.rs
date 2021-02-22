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

//! Fuzzing which ensures that running unbalanced sequential phragmen always produces a result
//! which satisfies our PJR checker.
//!
//! # Running
//!
//! Run with `cargo hfuzz run phragmen_pjr`.
//!
//! # Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug phragmen_pjr hfuzz_workspace/phragmen_pjr/*.fuzz`.

use honggfuzz::fuzz;

mod common;
use common::{generate_random_npos_inputs, to_range};
use rand::{self, SeedableRng};
use sp_npos_elections::{
	assignment_ratio_to_staked, pjr_check, seq_phragmen, to_supports, to_without_backing,
	ElectionResult, ExtendedBalance, Supports,
};

type AccountId = u64;
type PerThing = sp_arithmetic::PerU16;

/// TODO: This value is currently _entirely arbitrary_.
const PJR_THRESHOLD: ExtendedBalance = 1_000_000_000_000;

fn main() {
	loop {
		fuzz!(|data: (usize, usize, u64)| {
			let (mut candidate_count, mut voter_count, seed) = data;
			let rng = rand::rngs::SmallRng::seed_from_u64(seed);
			candidate_count = to_range(candidate_count, 100, 1000);
			voter_count = to_range(voter_count, 100, 2000);

			let (rounds, candidates, voters) =
				generate_random_npos_inputs(candidate_count, voter_count, rng);

			// Run seq-phragmen
			let ElectionResult {
				winners,
				assignments,
			} = seq_phragmen::<AccountId, PerThing>(rounds, candidates.clone(), voters.clone(), None)
				.expect("seq_phragmen must succeed");

			// pjr_check only cares about the identity of the winner, not its balance
			let winners = to_without_backing(winners);

			// convert assignments into staked assignments
			let assignments = assignment_ratio_to_staked(assignments, |who| {
				let voter_idx = voters
					.binary_search_by_key(who, |(id, _weight, _assignments)| *id)
					.expect("voter must be present in voters list");
				voters[voter_idx].1
			});

			let supports: Supports<AccountId> = to_supports(&winners, &assignments)
				.expect("election result must be structurally valid");

			assert!(
				pjr_check(&supports, candidates, voters),
				"unbalanced sequential phragmen must satisfy PJR",
			);
		});
	}
}
