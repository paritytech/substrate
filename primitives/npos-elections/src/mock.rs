// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Mock file for npos-elections.

#![cfg(any(test, mocks))]

use std::{
	collections::{HashMap, HashSet},
	convert::TryInto,
	hash::Hash,
};

use rand::{self, seq::SliceRandom, Rng};
use sp_arithmetic::{
	traits::{One, SaturatedConversion, Zero},
	PerThing,
};
use sp_runtime::assert_eq_error_rate;
use sp_std::collections::btree_map::BTreeMap;

use crate::{seq_phragmen, Assignment, ElectionResult, ExtendedBalance, PerThing128, VoteWeight};

sp_npos_elections_compact::generate_solution_type!(
	#[compact]
	pub struct Compact::<VoterIndex = u32, TargetIndex = u16, Accuracy = Accuracy>(16)
);

pub type AccountId = u64;
/// The candidate mask allows easy disambiguation between voters and candidates: accounts
/// for which this bit is set are candidates, and without it, are voters.
pub const CANDIDATE_MASK: AccountId = 1 << ((std::mem::size_of::<AccountId>() * 8) - 1);
pub type CandidateId = AccountId;

pub type Accuracy = sp_runtime::Perbill;

pub type MockAssignment = crate::Assignment<AccountId, Accuracy>;
pub type Voter = (AccountId, VoteWeight, Vec<AccountId>);

#[derive(Default, Debug)]
pub(crate) struct _Candidate<A> {
	who: A,
	score: f64,
	approval_stake: f64,
	elected: bool,
}

#[derive(Default, Debug)]
pub(crate) struct _Voter<A> {
	who: A,
	edges: Vec<_Edge<A>>,
	budget: f64,
	load: f64,
}

#[derive(Default, Debug)]
pub(crate) struct _Edge<A> {
	who: A,
	load: f64,
	candidate_index: usize,
}

#[derive(Default, Debug, PartialEq)]
pub(crate) struct _Support<A> {
	pub own: f64,
	pub total: f64,
	pub others: Vec<_Assignment<A>>,
}

pub(crate) type _Assignment<A> = (A, f64);
pub(crate) type _SupportMap<A> = BTreeMap<A, _Support<A>>;

#[derive(Debug, Clone)]
pub(crate) struct _ElectionResult<A: Clone> {
	pub winners: Vec<(A, ExtendedBalance)>,
	pub assignments: Vec<(A, Vec<_Assignment<A>>)>,
}

pub(crate) fn auto_generate_self_voters<A: Clone>(candidates: &[A]) -> Vec<(A, Vec<A>)> {
	candidates.iter().map(|c| (c.clone(), vec![c.clone()])).collect()
}

pub(crate) fn elect_float<A>(
	candidate_count: usize,
	initial_candidates: Vec<A>,
	initial_voters: Vec<(A, Vec<A>)>,
	stake_of: impl Fn(&A) -> VoteWeight,
) -> Option<_ElectionResult<A>>
where
	A: Default + Ord + Copy,
{
	let mut elected_candidates: Vec<(A, ExtendedBalance)>;
	let mut assigned: Vec<(A, Vec<_Assignment<A>>)>;
	let mut c_idx_cache = BTreeMap::<A, usize>::new();
	let num_voters = initial_candidates.len() + initial_voters.len();
	let mut voters: Vec<_Voter<A>> = Vec::with_capacity(num_voters);

	let mut candidates = initial_candidates
		.into_iter()
		.enumerate()
		.map(|(idx, who)| {
			c_idx_cache.insert(who.clone(), idx);
			_Candidate { who, ..Default::default() }
		})
		.collect::<Vec<_Candidate<A>>>();

	voters.extend(initial_voters.into_iter().map(|(who, votes)| {
		let voter_stake = stake_of(&who) as f64;
		let mut edges: Vec<_Edge<A>> = Vec::with_capacity(votes.len());
		for v in votes {
			if let Some(idx) = c_idx_cache.get(&v) {
				candidates[*idx].approval_stake = candidates[*idx].approval_stake + voter_stake;
				edges.push(_Edge { who: v.clone(), candidate_index: *idx, ..Default::default() });
			}
		}
		_Voter { who, edges, budget: voter_stake, load: 0f64 }
	}));

	let to_elect = candidate_count.min(candidates.len());
	elected_candidates = Vec::with_capacity(candidate_count);
	assigned = Vec::with_capacity(candidate_count);

	for _round in 0..to_elect {
		for c in &mut candidates {
			if !c.elected {
				c.score = 1.0 / c.approval_stake;
			}
		}
		for n in &voters {
			for e in &n.edges {
				let c = &mut candidates[e.candidate_index];
				if !c.elected && !(c.approval_stake == 0f64) {
					c.score += n.budget * n.load / c.approval_stake;
				}
			}
		}

		if let Some(winner) = candidates
			.iter_mut()
			.filter(|c| !c.elected)
			.min_by(|x, y| x.score.partial_cmp(&y.score).unwrap_or(sp_std::cmp::Ordering::Equal))
		{
			winner.elected = true;
			for n in &mut voters {
				for e in &mut n.edges {
					if e.who == winner.who {
						e.load = winner.score - n.load;
						n.load = winner.score;
					}
				}
			}

			elected_candidates.push((winner.who.clone(), winner.approval_stake as ExtendedBalance));
		} else {
			break
		}
	}

	for n in &mut voters {
		let mut assignment = (n.who.clone(), vec![]);
		for e in &mut n.edges {
			if let Some(c) =
				elected_candidates.iter().cloned().map(|(c, _)| c).find(|c| *c == e.who)
			{
				if c != n.who {
					let ratio = e.load / n.load;
					assignment.1.push((e.who.clone(), ratio));
				}
			}
		}
		if assignment.1.len() > 0 {
			assigned.push(assignment);
		}
	}

	Some(_ElectionResult { winners: elected_candidates, assignments: assigned })
}

pub(crate) fn equalize_float<A, FS>(
	mut assignments: Vec<(A, Vec<_Assignment<A>>)>,
	supports: &mut _SupportMap<A>,
	tolerance: f64,
	iterations: usize,
	stake_of: FS,
) where
	for<'r> FS: Fn(&'r A) -> VoteWeight,
	A: Ord + Clone + std::fmt::Debug,
{
	for _i in 0..iterations {
		let mut max_diff = 0.0;
		for (voter, assignment) in assignments.iter_mut() {
			let voter_budget = stake_of(&voter);
			let diff = do_equalize_float(voter, voter_budget, assignment, supports, tolerance);
			if diff > max_diff {
				max_diff = diff;
			}
		}

		if max_diff < tolerance {
			break
		}
	}
}

pub(crate) fn do_equalize_float<A>(
	voter: &A,
	budget_balance: VoteWeight,
	elected_edges: &mut Vec<_Assignment<A>>,
	support_map: &mut _SupportMap<A>,
	tolerance: f64,
) -> f64
where
	A: Ord + Clone,
{
	let budget = budget_balance as f64;
	if elected_edges.is_empty() {
		return 0.0
	}

	let stake_used = elected_edges.iter().fold(0.0, |s, e| s + e.1);

	let backed_stakes_iter =
		elected_edges.iter().filter_map(|e| support_map.get(&e.0)).map(|e| e.total);

	let backing_backed_stake = elected_edges
		.iter()
		.filter(|e| e.1 > 0.0)
		.filter_map(|e| support_map.get(&e.0))
		.map(|e| e.total)
		.collect::<Vec<f64>>();

	let mut difference;
	if backing_backed_stake.len() > 0 {
		let max_stake = backing_backed_stake
			.iter()
			.max_by(|x, y| x.partial_cmp(&y).unwrap_or(sp_std::cmp::Ordering::Equal))
			.expect("vector with positive length will have a max; qed");
		let min_stake = backed_stakes_iter
			.min_by(|x, y| x.partial_cmp(&y).unwrap_or(sp_std::cmp::Ordering::Equal))
			.expect("iterator with positive length will have a min; qed");

		difference = max_stake - min_stake;
		difference = difference + budget - stake_used;
		if difference < tolerance {
			return difference
		}
	} else {
		difference = budget;
	}

	// Undo updates to support
	elected_edges.iter_mut().for_each(|e| {
		if let Some(support) = support_map.get_mut(&e.0) {
			support.total = support.total - e.1;
			support.others.retain(|i_support| i_support.0 != *voter);
		}
		e.1 = 0.0;
	});

	elected_edges.sort_by(|x, y| {
		support_map
			.get(&x.0)
			.and_then(|x| support_map.get(&y.0).and_then(|y| x.total.partial_cmp(&y.total)))
			.unwrap_or(sp_std::cmp::Ordering::Equal)
	});

	let mut cumulative_stake = 0.0;
	let mut last_index = elected_edges.len() - 1;
	elected_edges.iter_mut().enumerate().for_each(|(idx, e)| {
		if let Some(support) = support_map.get_mut(&e.0) {
			let stake = support.total;
			let stake_mul = stake * (idx as f64);
			let stake_sub = stake_mul - cumulative_stake;
			if stake_sub > budget {
				last_index = idx.checked_sub(1).unwrap_or(0);
				return
			}
			cumulative_stake = cumulative_stake + stake;
		}
	});

	let last_stake = elected_edges[last_index].1;
	let split_ways = last_index + 1;
	let excess = budget + cumulative_stake - last_stake * (split_ways as f64);
	elected_edges.iter_mut().take(split_ways).for_each(|e| {
		if let Some(support) = support_map.get_mut(&e.0) {
			e.1 = excess / (split_ways as f64) + last_stake - support.total;
			support.total = support.total + e.1;
			support.others.push((voter.clone(), e.1));
		}
	});

	difference
}

pub(crate) fn create_stake_of(
	stakes: &[(AccountId, VoteWeight)],
) -> impl Fn(&AccountId) -> VoteWeight {
	let mut storage = BTreeMap::<AccountId, VoteWeight>::new();
	stakes.iter().for_each(|s| {
		storage.insert(s.0, s.1);
	});
	move |who: &AccountId| -> VoteWeight { storage.get(who).unwrap().to_owned() }
}

pub fn check_assignments_sum<T: PerThing>(assignments: &[Assignment<AccountId, T>]) {
	for Assignment { distribution, .. } in assignments {
		let mut sum: u128 = Zero::zero();
		distribution
			.iter()
			.for_each(|(_, p)| sum += p.deconstruct().saturated_into::<u128>());
		assert_eq!(sum, T::ACCURACY.saturated_into(), "Assignment ratio sum is not 100%");
	}
}

pub(crate) fn run_and_compare<Output: PerThing128, FS>(
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, Vec<AccountId>)>,
	stake_of: FS,
	to_elect: usize,
) where
	Output: PerThing128,
	FS: Fn(&AccountId) -> VoteWeight,
{
	// run fixed point code.
	let ElectionResult { winners, assignments } = seq_phragmen::<_, Output>(
		to_elect,
		candidates.clone(),
		voters
			.iter()
			.map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone()))
			.collect::<Vec<_>>(),
		None,
	)
	.unwrap();

	// run float poc code.
	let truth_value = elect_float(to_elect, candidates, voters, &stake_of).unwrap();

	assert_eq!(
		winners.iter().map(|(x, _)| x).collect::<Vec<_>>(),
		truth_value.winners.iter().map(|(x, _)| x).collect::<Vec<_>>()
	);

	for Assignment { who, distribution } in assignments.iter() {
		if let Some(float_assignments) = truth_value.assignments.iter().find(|x| x.0 == *who) {
			for (candidate, per_thingy) in distribution {
				if let Some(float_assignment) =
					float_assignments.1.iter().find(|x| x.0 == *candidate)
				{
					assert_eq_error_rate!(
						Output::from_float(float_assignment.1).deconstruct(),
						per_thingy.deconstruct(),
						Output::Inner::one(),
					);
				} else {
					panic!(
						"candidate mismatch. This should never happen. could not find ({:?}, {:?})",
						candidate, per_thingy,
					)
				}
			}
		} else {
			panic!("nominator mismatch. This should never happen.")
		}
	}

	check_assignments_sum(&assignments);
}

pub(crate) fn build_support_map_float(
	result: &mut _ElectionResult<AccountId>,
	stake_of: impl Fn(&AccountId) -> VoteWeight,
) -> _SupportMap<AccountId> {
	let mut supports = <_SupportMap<AccountId>>::new();
	result.winners.iter().map(|(e, _)| (e, stake_of(e) as f64)).for_each(|(e, s)| {
		let item = _Support { own: s, total: s, ..Default::default() };
		supports.insert(e.clone(), item);
	});

	for (n, assignment) in result.assignments.iter_mut() {
		for (c, r) in assignment.iter_mut() {
			let nominator_stake = stake_of(n) as f64;
			let other_stake = nominator_stake * *r;
			if let Some(support) = supports.get_mut(c) {
				support.total = support.total + other_stake;
				support.others.push((n.clone(), other_stake));
			}
			*r = other_stake;
		}
	}
	supports
}

/// Generate voter and assignment lists. Makes no attempt to be realistic about winner or assignment fairness.
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
) -> (Vec<Voter>, Vec<MockAssignment>, Vec<CandidateId>) {
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
		let n_candidates_chosen = rng.gen_range(1, candidates.len().min(16));

		let mut chosen_candidates = Vec::with_capacity(n_candidates_chosen);
		chosen_candidates.extend(candidates.choose_multiple(&mut rng, n_candidates_chosen));
		voters.push((id, vote_weight, chosen_candidates));
	}

	// always generate a sensible number of winners: elections are uninteresting if nobody wins,
	// or everybody wins
	let num_winners = rng.gen_range(1, candidate_count);
	let mut winners: HashSet<AccountId> = HashSet::with_capacity(num_winners);
	winners.extend(candidates.choose_multiple(&mut rng, num_winners));
	assert_eq!(winners.len(), num_winners);

	let mut assignments = Vec::with_capacity(voters.len());
	for (voter_id, _, votes) in voters.iter() {
		let chosen_winners = votes.iter().filter(|vote| winners.contains(vote)).cloned();
		let num_chosen_winners = chosen_winners.clone().count();

		// distribute the available stake randomly
		let stake_distribution = if num_chosen_winners == 0 {
			Vec::new()
		} else {
			let mut available_stake = 1000;
			let mut stake_distribution = Vec::with_capacity(num_chosen_winners);
			for _ in 0..num_chosen_winners - 1 {
				let stake = rng.gen_range(0, available_stake);
				stake_distribution.push(Accuracy::from_perthousand(stake));
				available_stake -= stake;
			}
			stake_distribution.push(Accuracy::from_perthousand(available_stake));
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
	move |who| cache.get(who).cloned().and_then(|i| i.try_into().ok())
}

/// Create a function that returns the index of a candidate in the candidates list.
pub fn make_target_fn<TargetIndex>(
	candidates: &[CandidateId],
) -> impl Fn(&CandidateId) -> Option<TargetIndex>
where
	usize: TryInto<TargetIndex>,
{
	let cache = generate_cache(candidates.iter().cloned());
	move |who| cache.get(who).cloned().and_then(|i| i.try_into().ok())
}
