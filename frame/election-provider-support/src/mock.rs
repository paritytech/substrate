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

//! Mock file for solution-type.

#![cfg(test)]

use std::{
	collections::{HashMap, HashSet},
	hash::Hash,
};

use rand::{seq::SliceRandom, Rng};

pub type AccountId = u64;

/// The candidate mask allows easy disambiguation between voters and candidates: accounts
/// for which this bit is set are candidates, and without it, are voters.
pub const CANDIDATE_MASK: AccountId = 1 << ((std::mem::size_of::<AccountId>() * 8) - 1);

pub type TestAccuracy = sp_runtime::Perbill;

pub fn p(p: u8) -> TestAccuracy {
	TestAccuracy::from_percent(p.into())
}

pub type MockAssignment = crate::Assignment<AccountId, TestAccuracy>;
pub type Voter = (AccountId, crate::VoteWeight, Vec<AccountId>);

crate::generate_solution_type! {
	pub struct TestSolution::<
		VoterIndex = u32,
		TargetIndex = u16,
		Accuracy = TestAccuracy,
		MaxVoters = frame_support::traits::ConstU32::<2_500>,
	>(16)
}

/// Generate voter and assignment lists. Makes no attempt to be realistic about winner or assignment
/// fairness.
///
/// Maintains these invariants:
///
/// - candidate ids have `CANDIDATE_MASK` bit set
/// - voter ids do not have `CANDIDATE_MASK` bit set
/// - assignments have the same ordering as voters
/// - `assignments.distribution.iter().map(|(_, frac)| frac).sum() == One::one()`
/// - a coherent set of winners is chosen.
/// - the winner set is a subset of the candidate set.
/// - `assignments.distribution.iter().all(|(who, _)| winners.contains(who))`
pub fn generate_random_votes(
	candidate_count: usize,
	voter_count: usize,
	mut rng: impl Rng,
) -> (Vec<Voter>, Vec<MockAssignment>, Vec<AccountId>) {
	// cache for fast generation of unique candidate and voter ids
	let mut used_ids = HashSet::with_capacity(candidate_count + voter_count);

	// candidates are easy: just a completely random set of IDs
	let mut candidates: Vec<AccountId> = Vec::with_capacity(candidate_count);
	while candidates.len() < candidate_count {
		let mut new = || rng.gen::<AccountId>() | CANDIDATE_MASK;
		let mut id = new();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = new();
		}
		candidates.push(id);
	}

	// voters are random ids, random weights, random selection from the candidates
	let mut voters = Vec::with_capacity(voter_count);
	while voters.len() < voter_count {
		let mut new = || rng.gen::<AccountId>() & !CANDIDATE_MASK;
		let mut id = new();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = new();
		}

		let vote_weight = rng.gen();

		// it's not interesting if a voter chooses 0 or all candidates, so rule those cases out.
		// also, let's not generate any cases which result in a compact overflow.
		let n_candidates_chosen =
			rng.gen_range(1..candidates.len().min(<TestSolution as crate::NposSolution>::LIMIT));

		let mut chosen_candidates = Vec::with_capacity(n_candidates_chosen);
		chosen_candidates.extend(candidates.choose_multiple(&mut rng, n_candidates_chosen));
		voters.push((id, vote_weight, chosen_candidates));
	}

	// always generate a sensible number of winners: elections are uninteresting if nobody wins,
	// or everybody wins
	let num_winners = rng.gen_range(1..candidate_count);
	let mut winners: HashSet<AccountId> = HashSet::with_capacity(num_winners);
	winners.extend(candidates.choose_multiple(&mut rng, num_winners));
	assert_eq!(winners.len(), num_winners);

	let mut assignments = Vec::with_capacity(voters.len());
	for (voter_id, _, votes) in voters.iter() {
		let chosen_winners = votes.iter().filter(|vote| winners.contains(vote)).cloned();
		let num_chosen_winners = chosen_winners.clone().count();

		// distribute the available stake randomly
		let stake_distribution = if num_chosen_winners == 0 {
			continue
		} else {
			let mut available_stake = 1000;
			let mut stake_distribution = Vec::with_capacity(num_chosen_winners);
			for _ in 0..num_chosen_winners - 1 {
				let stake = rng.gen_range(0..available_stake).min(1);
				stake_distribution.push(TestAccuracy::from_perthousand(stake));
				available_stake -= stake;
			}
			stake_distribution.push(TestAccuracy::from_perthousand(available_stake));
			stake_distribution.shuffle(&mut rng);
			stake_distribution
		};

		assignments.push(MockAssignment {
			who: *voter_id,
			distribution: chosen_winners.zip(stake_distribution).collect(),
		});
	}

	(voters, assignments, candidates)
}

fn generate_cache<Voters, Item>(voters: Voters) -> HashMap<Item, usize>
where
	Voters: Iterator<Item = Item>,
	Item: Hash + Eq + Copy,
{
	let mut cache = HashMap::new();
	for (idx, voter_id) in voters.enumerate() {
		cache.insert(voter_id, idx);
	}
	cache
}

/// Create a function that returns the index of a voter in the voters list.
pub fn make_voter_fn<VoterIndex>(voters: &[Voter]) -> impl Fn(&AccountId) -> Option<VoterIndex>
where
	usize: TryInto<VoterIndex>,
{
	let cache = generate_cache(voters.iter().map(|(id, _, _)| *id));
	move |who| {
		if cache.get(who).is_none() {
			println!("WARNING: voter {} will raise InvalidIndex", who);
		}
		cache.get(who).cloned().and_then(|i| i.try_into().ok())
	}
}

/// Create a function that returns the index of a candidate in the candidates list.
pub fn make_target_fn<TargetIndex>(
	candidates: &[AccountId],
) -> impl Fn(&AccountId) -> Option<TargetIndex>
where
	usize: TryInto<TargetIndex>,
{
	let cache = generate_cache(candidates.iter().cloned());
	move |who| {
		if cache.get(who).is_none() {
			println!("WARNING: target {} will raise InvalidIndex", who);
		}
		cache.get(who).cloned().and_then(|i| i.try_into().ok())
	}
}
