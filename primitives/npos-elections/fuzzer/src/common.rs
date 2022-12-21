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

//! Common fuzzing utils.

// Each function will be used based on which fuzzer binary is being used.
#![allow(dead_code)]

use rand::{self, seq::SliceRandom, Rng, RngCore};
use sp_npos_elections::{phragmms, seq_phragmen, BalancingConfig, ElectionResult, VoteWeight};
use sp_runtime::Perbill;
use std::collections::{BTreeMap, HashSet};

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
	Phragmen(Option<BalancingConfig>),
	Phragmms(Option<BalancingConfig>),
}

pub type AccountId = u64;

/// Generate a set of inputs suitable for fuzzing an election algorithm
///
/// Given parameters governing how many candidates and voters should exist, generates a voting
/// scenario suitable for fuzz-testing an election algorithm.
///
/// The returned candidate list is sorted. This sorting property should not affect the result of the
/// calculation.
///
/// The returned voters list is sorted. This enables binary searching for a particular voter by
/// account id. This sorting property should not affect the results of the calculation.
///
/// Each voter's selection of candidates to vote for is sorted.
///
/// Note that this does not generate balancing parameters.
pub fn generate_random_npos_inputs(
	candidate_count: usize,
	voter_count: usize,
	mut rng: impl Rng,
) -> (usize, Vec<AccountId>, Vec<(AccountId, VoteWeight, Vec<AccountId>)>) {
	// cache for fast generation of unique candidate and voter ids
	let mut used_ids = HashSet::with_capacity(candidate_count + voter_count);

	// always generate a sensible desired number of candidates: elections are uninteresting if we
	// desire 0 candidates, or a number of candidates >= the actual number of candidates present
	let rounds = rng.gen_range(1..candidate_count);

	// candidates are easy: just a completely random set of IDs
	let mut candidates: Vec<AccountId> = Vec::with_capacity(candidate_count);
	for _ in 0..candidate_count {
		let mut id = rng.gen();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = rng.gen();
		}
		candidates.push(id);
	}
	candidates.sort();
	candidates.dedup();
	assert_eq!(candidates.len(), candidate_count);

	let mut voters = Vec::with_capacity(voter_count);
	for _ in 0..voter_count {
		let mut id = rng.gen();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = rng.gen();
		}

		let vote_weight = rng.gen();

		// it's not interesting if a voter chooses 0 or all candidates, so rule those cases out.
		let n_candidates_chosen = rng.gen_range(1..candidates.len());

		let mut chosen_candidates = Vec::with_capacity(n_candidates_chosen);
		chosen_candidates.extend(candidates.choose_multiple(&mut rng, n_candidates_chosen));
		chosen_candidates.sort();
		voters.push((id, vote_weight, chosen_candidates));
	}

	voters.sort();
	voters.dedup_by_key(|(id, _weight, _chosen_candidates)| *id);
	assert_eq!(voters.len(), voter_count);

	(rounds, candidates, voters)
}

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
		let stake_var = rng.gen_range(ed..100 * ed);
		stake_of.insert(acc, base_stake + stake_var);
	});

	let mut voters = Vec::with_capacity(voter_count as usize);
	(prefix..=(prefix + voter_count)).for_each(|acc| {
		let edge_per_this_voter = rng.gen_range(1..candidates.len());
		// all possible targets
		let mut all_targets = candidates.clone();
		// we remove and pop into `targets` `edge_per_this_voter` times.
		let targets = (0..edge_per_this_voter)
			.map(|_| {
				let upper = all_targets.len() - 1;
				let idx = rng.gen_range(0..upper);
				all_targets.remove(idx)
			})
			.collect::<Vec<AccountId>>();

		let stake_var = rng.gen_range(ed..100 * ed);
		let stake = base_stake + stake_var;
		stake_of.insert(acc, stake);
		voters.push((acc, stake, targets));
	});

	(
		match election_type {
			ElectionType::Phragmen(conf) =>
				seq_phragmen(to_elect, candidates.clone(), voters.clone(), conf).unwrap(),
			ElectionType::Phragmms(conf) =>
				phragmms(to_elect, candidates.clone(), voters.clone(), conf).unwrap(),
		},
		candidates,
		voters,
		stake_of,
	)
}
