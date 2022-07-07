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

//! Common fuzzing utils.

// Each function will be used based on which fuzzer binary is being used.
#![allow(dead_code)]

use sp_npos_elections::{ElectionResult, VoteWeight, phragmms, seq_phragmen};
use sp_std::collections::btree_map::BTreeMap;
use sp_runtime::Perbill;
use rand::{self, Rng, RngCore};

/// converts x into the range [a, b] in a pseudo-fair way.
pub fn to_range(x: usize, a: usize, b: usize) -> usize {
	// does not work correctly if b < 2 * a
	assert!(b >= 2 * a);
	let collapsed = x % b;
	if collapsed >= a {
		collapsed
	} else {
		collapsed + a
	}
}

pub enum ElectionType {
	Phragmen(Option<(usize, u128)>),
	Phragmms(Option<(usize, u128)>)
}

pub type AccountId = u64;

pub fn generate_random_npos_result(
	voter_count: u64,
	target_count: u64,
	to_elect: usize,
	mut rng: impl RngCore,
	election_type: ElectionType,
) -> (
	ElectionResult<AccountId, Perbill>,
	Vec<AccountId>,
	Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	BTreeMap<AccountId, VoteWeight>,
) {
	let prefix = 100_000;
	// Note, it is important that stakes are always bigger than ed.
	let base_stake: u64 = 1_000_000_000_000;
	let ed: u64 = base_stake;

	let mut candidates = Vec::with_capacity(target_count as usize);
	let mut stake_of: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();

	(1..=target_count).for_each(|acc| {
		candidates.push(acc);
		let stake_var = rng.gen_range(ed, 100 * ed);
		stake_of.insert(acc, base_stake + stake_var);
	});

	let mut voters = Vec::with_capacity(voter_count as usize);
	(prefix ..= (prefix + voter_count)).for_each(|acc| {
		let edge_per_this_voter = rng.gen_range(1, candidates.len());
		// all possible targets
		let mut all_targets = candidates.clone();
		// we remove and pop into `targets` `edge_per_this_voter` times.
		let targets = (0..edge_per_this_voter).map(|_| {
			let upper = all_targets.len() - 1;
			let idx = rng.gen_range(0, upper);
			all_targets.remove(idx)
		})
		.collect::<Vec<AccountId>>();

		let stake_var = rng.gen_range(ed, 100 * ed) ;
		let stake = base_stake + stake_var;
		stake_of.insert(acc, stake);
		voters.push((acc, stake, targets));
	});

	(
		match election_type {
			ElectionType::Phragmen(conf) =>
				seq_phragmen::<AccountId, sp_runtime::Perbill>(
					to_elect,
					candidates.clone(),
					voters.clone(),
					conf,
				).unwrap(),
			ElectionType::Phragmms(conf) =>
				phragmms::<AccountId, sp_runtime::Perbill>(
					to_elect,
					candidates.clone(),
					voters.clone(),
					conf,
				).unwrap(),
		},
		candidates,
		voters,
		stake_of,
	)
}
