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

//! Implements functions and interfaces to check solutions for being t-PJR.
//!
//! PJR stands for proportional justified representation. PJR is a string absolute measure to make
//! sure an NPoS solution adheres to a minimum standard.
//!
//! See [`pjr_check`] which is the main entry point of the module.

use crate::*;
use sp_std::rc::Rc;
use sp_std::collections::btree_map::BTreeMap;
use sp_arithmetic::{traits::Zero, Perbill};


/// The type used as the threshold.
///
/// Just some reading sugar; Must always be same as [`ExtendedBalance`];
type Threshold = ExtendedBalance;

/// Convert the data types that the user runtime has into ones that can be used by this module.
///
/// It is expected that this function's interface might change over time, or multiple variants of it
/// can be provided for different use cases.
///
/// The ultimate goal, in any case, is to convert the election data into [`Candidate`] and [`Voter`]
/// types defined by this crate, whilst setting correct value for some of their fields, namely:
/// 1. Candidate [`backing_stake`](Candidate::backing_stake) and [`elected`](Candidate::elected) if they are a winner.
/// 2. Voter edge [`weight`](Edge::weight) if they are backing a winner.
/// 3. Voter [`budget`](Voter::budget).
///
/// None of the `load` or `score` values are used and can be ignored. This is similar to
/// [`setup_inputs`] function of this crate.
///
/// ### Performance (Weight) Notes
///
/// Note that the current function is rather unfortunately inefficient. The most significant
/// slowdown is the fact that a typical solution that need to be checked for PJR only contains a
/// subset of the entire NPoS edge graph, encoded as `staked_assignment`. This only encodes the
/// edges that actually contribute to a winner's backing stake and ignores the rest to save space.
/// To check PJR, we need the entire voter set, including those edges that point to non-winners.
/// This could cause the caller runtime to have to read the entire list of voters, which is assumed
/// to be expensive.
///
/// A sensible user of this module should make sure that the PJR check is executed and checked as
/// little as possible, and take sufficient economical measures to ensure that this function cannot
/// be abused.
pub fn prepare_pjr_input<A: IdentifierT>(
	winners: Vec<A>,
	staked_assignments: Vec<StakedAssignment<A>>,
	supports: &SupportMap<A>,
	all_candidates: Vec<A>,
	all_voters: Vec<(A, VoteWeight, Vec<A>)>,
) -> (Vec<CandidatePtr<A>>, Vec<Voter<A>>) {
	// collect all candidates and winners into a unified `Vec<Candidate>`.
	let mut candidates_index: BTreeMap<A, usize> = BTreeMap::new();

	// dump the staked assignments in a voter-major map for faster access down the road.
	let mut assignment_map: BTreeMap<A, Vec<(A, ExtendedBalance)>> = BTreeMap::new();
	staked_assignments
		.into_iter()
		.for_each(|StakedAssignment { who, distribution }| {
			assignment_map.insert(who, distribution);
		});

	let candidates = all_candidates.into_iter().enumerate().map(|(i, c)| {
		candidates_index.insert(c.clone(), i);

		// set the backing value and elected flag if the candidate is among the winners.
		let who = c;
		let elected = winners.iter().any(|w| w == &who);
		let backed_stake = supports.get(&who).map(|s| s.total).unwrap_or_default();

		debug_assert!(
			!(elected ^ (backed_stake > 0)),
			"If a candidate is elected, then it must have a positive backing as well."
		);

		Candidate { who, elected, backed_stake, ..Default::default() }.to_ptr()
	}).collect::<Vec<_>>();

	// collect all voters into a unified Vec<Voters>.
	let voters = all_voters.into_iter().map(|(v, w, ts)| {
		let mut edges: Vec<Edge<A>> = Vec::with_capacity(ts.len());
		for t in ts {
			if edges.iter().any(|e| e.who == t) {
				// duplicate edge.
				continue;
			}

			if let Some(idx) = candidates_index.get(&t) {
				// if this edge is among the assignments, set the weight as well.
				let weight = assignment_map
					.get(&v)
					.and_then(|d| d.iter().find_map(|(x, y)| if x == &t { Some(y) } else { None }))
					.cloned()
					.unwrap_or_default();
				edges.push(Edge {
					who: t,
					candidate: Rc::clone(&candidates[*idx]),
					weight,
					..Default::default()
				});
			}
		}

		let who = v;
		let budget: ExtendedBalance = w.into();
		Voter { who, budget, edges, ..Default::default() }
	}).collect::<Vec<_>>();

	(candidates, voters)
}

/// Check a solution to be t-PJR.
///
/// ### Semantics
///
/// For a solution to be t-PJR, the original condition is as such: If there is a group of `N` voters
/// who have `r` common candidates and can afford to support each of them with backing stake `t`
/// (i.e `sum(stake(v) for all voters ) == r * t`), then this committee need to be represented by at
/// least `r` elected candidates.
///
/// Section 5 of the NPoS paper shows that this property is equal to: For a feasible solution, if
/// `Max {score(c)} < t` where c is every unelected candidate, then this solution is t-PJR.
///
/// In this implementation we use the latter definition due to its simplicity.
///
/// ### Interface
///
/// In addition to data that can be computed from the [`ElectionResult`] struct, a PJR check also
/// needs to inspect un-elected candidates and edges, thus `all_candidates` and `all_voters`.
///
/// See [`prepare_pjr_input`] for more info.
pub fn pjr_check<A: IdentifierT>(
	winners: Vec<A>,
	staked_assignments: Vec<StakedAssignment<A>>,
	supports: &SupportMap<A>,
	all_candidates: Vec<A>,
	all_voters: Vec<(A, VoteWeight, Vec<A>)>,
	t: Threshold,
) -> bool {
	// prepare data.
	let (candidates, voters) = prepare_pjr_input(
		winners,
		staked_assignments,
		supports,
		all_candidates,
		all_voters,
	);
	// compute with threshold t.
	pjr_check_core(candidates.as_ref(), voters.as_ref(), t)
}

/// The internal implementation of the PJR check after having the data converted.
///
/// See [`pjr_check`] for more info.
pub fn pjr_check_core<A: IdentifierT>(
	candidates: &[CandidatePtr<A>],
	voters: &[Voter<A>],
	t: Threshold,
) -> bool {
	let unelected = candidates.iter().filter(|c| !c.borrow().elected);
	let maybe_max_pre_score = unelected.map(|c| pre_score(Rc::clone(c), voters, t)).max();
	// if unelected is empty then the solution is indeed PJR.
	maybe_max_pre_score.map_or(true, |max_pre_score| max_pre_score < t)
}

/// The pre-score of an unelected candidate.
///
/// This is the amount of stake that *all voter* can spare to devote to this candidate without
/// allowing the backing stake of any other elected candidate to fall below `t`.
///
/// In essence, it is the sum(slack(n, t)) for all `n` who vote for `unelected`.
pub fn pre_score<A: IdentifierT>(
	unelected: CandidatePtr<A>,
	voters: &[Voter<A>],
	t: Threshold,
) -> ExtendedBalance {
	debug_assert!(!unelected.borrow().elected);
	voters
		.iter()
		.filter(|ref v| v.votes_for(&unelected.borrow().who))
		.fold(Zero::zero(), |acc: ExtendedBalance, voter| acc.saturating_add(slack(voter, t)))
}


/// The slack of a voter at a given state.
///
/// The slack of each voter, with threshold `t` is the total amount of stake that this voter can
/// spare to a new potential member, whilst not dropping the backing stake of any of its currently
/// active members below `t`. In essence, for each of the current active candidates `c`, we assume
/// that we reduce the edge weight of `voter` to `c` from `w` to `w * min(1 / (t / support(c)))`.
///
/// More accurately:
///
/// 1. If `c` exactly has `t` backing or less, then we don't generate any slack.
/// 2. If `c` has more than `t`, then we reduce it to `t`.
pub fn slack<A: IdentifierT>(voter: &Voter<A>, t: Threshold) -> ExtendedBalance {
	let budget = voter.budget;
	let leftover = voter.edges.iter().fold(Zero::zero(), |acc: ExtendedBalance, edge| {
		let candidate = edge.candidate.borrow();
		if candidate.elected {
			// TODO: using perbill here is just going to cause annoyance, why not just subtract?
			let extra =
				Perbill::one().min(Perbill::from_rational_approximation(t, candidate.backed_stake))
				* edge.weight;
			acc.saturating_add(extra)
		} else {
			// No slack generated here.
			acc
		}
	});

	// NOTE: candidate for saturating_log_sub()
	budget.saturating_sub(leftover)
}

#[cfg(test)]
mod tests {
	use super::*;

	fn setup_voter(who: u32, votes: Vec<(u32, u128, bool)>) -> Voter<u32> {
		let mut voter = Voter::new(who);
		let mut budget = 0u128;
		let candidates = votes.into_iter().map(|(t, w, e)| {
			budget += w;
			Candidate { who: t, elected: e, backed_stake: w, ..Default::default() }
		}).collect::<Vec<_>>();
		let edges = candidates.into_iter().map(|c|
			Edge { who: c.who, weight: c.backed_stake, candidate: c.to_ptr(), ..Default::default() }
		).collect::<Vec<_>>();
		voter.edges = edges;
		voter.budget = budget;
		voter
	}

	#[test]
	fn slack_works() {
		let voter = setup_voter(10, vec![(1, 10, true), (2, 20, true)]);

		assert_eq!(slack(&voter, 15), 5);
		assert_eq!(slack(&voter, 17), 3);
		assert_eq!(slack(&voter, 10), 10);
		assert_eq!(slack(&voter, 5), 20);

	}

	#[test]
	fn pre_score_works() {
		// will give 5 slack
		let v1 = setup_voter(10, vec![(1, 10, true), (2, 20, true), (3, 0, false)]);
		// will give no slack
		let v2 = setup_voter(20, vec![(1, 5, true), (2, 5, true)]);
		// will give 10 slack.
		let v3 = setup_voter(30, vec![(1, 20, true), (2, 20, true), (3, 0, false)]);

		let unelected = Candidate { who: 3u32, elected: false, ..Default::default() }.to_ptr();
		let score = pre_score(unelected, &vec![v1, v2, v3], 15);

		assert_eq!(score, 15);
	}

	#[test]
	fn can_convert_data_from_external_api() {
		let winners = vec![20u32, 40];
		let all_candidates = vec![10, 20, 30, 40];
		let staked_assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(20, 5), (40, 5)] },
			StakedAssignment { who: 2, distribution: vec![(20, 10), (40, 10)] },
		];
		let all_voters = vec![
			(1, 10, vec![10, 20, 30, 40]),
			(2, 20, vec![10, 20, 30, 40]),
			(3, 30, vec![10, 30]),
		];
		let mut supports = SupportMap::<u32>::new();
		supports.insert(20, Support { total: 15, voters: vec![(5, 1), (10, 2)]} );
		supports.insert(40, Support { total: 15, voters: vec![(5, 1), (10, 2)]} );

		let (candidates, voters) = prepare_pjr_input(
			winners,
			staked_assignments,
			&supports,
			all_candidates,
			all_voters,
		);

		// elected flag and backing must be set correctly
		assert_eq!(
			candidates
				.iter()
				.map(|c| (c.borrow().who.clone(), c.borrow().elected, c.borrow().backed_stake))
				.collect::<Vec<_>>(),
			vec![(10, false, 0), (20, true, 15), (30, false, 0), (40, true, 15)],
		);

		// edge weight must be set correctly
		assert_eq!(
			voters
				.iter()
				.map(|v| (
					v.who,
					v.budget,
					v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>(),
				)).collect::<Vec<_>>(),
			vec![
				(1, 10, vec![(10, 0), (20, 5), (30, 0), (40, 5)]),
				(2, 20, vec![(10, 0), (20, 10), (30, 0), (40, 10)]),
				(3, 30, vec![(10, 0), (30, 0)]),
			],
		);

		// fyi. this is not PJR, obviously because the votes of 3 can bump the stake a lot but they
		// are being ignored.
		assert!(!pjr_check_core(&candidates, &voters, 1));
		assert!(!pjr_check_core(&candidates, &voters, 10));
		assert!(!pjr_check_core(&candidates, &voters, 20));
	}
}
