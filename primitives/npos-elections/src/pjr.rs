 // This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
//! PJR stands for proportional justified representation. PJR is an absolute measure to make
//! sure an NPoS solution adheres to a minimum standard.
//!
//! See [`pjr_check`] which is the main entry point of the module.

use crate::{
	Candidate,
	CandidatePtr,
	Edge,
	ExtendedBalance,
	IdentifierT,
	Support,
	SupportMap,
	Supports,
	Voter,
	VoteWeight,
};
use sp_std::{rc::Rc, vec::Vec};
use sp_std::collections::btree_map::BTreeMap;
use sp_arithmetic::{traits::Zero, Perbill};

/// The type used as the threshold.
///
/// Just some reading sugar; Must always be same as [`ExtendedBalance`];
type Threshold = ExtendedBalance;

/// Compute the threshold corresponding to the standard PJR property
///
/// `t-PJR` checks can check PJR according to an arbitrary threshold. The threshold can be any value,
/// but the property gets stronger as the threshold gets smaller. The strongest possible `t-PJR` property
/// corresponds to `t == 0`.
///
/// However, standard PJR is less stringent than that. This function returns the threshold whose
/// strength corresponds to the standard PJR property.
///
/// - `committee_size` is the number of winners of the election.
/// - `weights` is an iterator of voter stakes. If the sum of stakes is already known,
///   `std::iter::once(sum_of_stakes)` is appropriate here.
pub fn standard_threshold(
	committee_size: usize,
	weights: impl IntoIterator<Item = ExtendedBalance>,
) -> Threshold {
	weights
		.into_iter()
		.fold(Threshold::zero(), |acc, elem| {
			acc.saturating_add(elem)
		})
	/ committee_size.max(1) as Threshold
}

/// Check a solution to be PJR.
///
/// The PJR property is true if `t-PJR` is true when `t == sum(stake) / committee_size`.
pub fn pjr_check<AccountId: IdentifierT>(
	supports: &Supports<AccountId>,
	all_candidates: Vec<AccountId>,
	all_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
) -> bool {
	let t = standard_threshold(supports.len(), all_voters.iter().map(|voter| voter.1 as ExtendedBalance));
	t_pjr_check(supports, all_candidates, all_voters, t)
}

/// Check a solution to be t-PJR.
///
/// ### Semantics
///
/// The t-PJR property is defined in the paper ["Validator Election in Nominated Proof-of-Stake"][NPoS],
/// section 5, definition 1.
///
/// In plain language, the t-PJR condition is: if there is a group of `N` voters
/// who have `r` common candidates and can afford to support each of them with backing stake `t`
/// (i.e `sum(stake(v) for v in voters) == r * t`), then this committee needs to be represented by at
/// least `r` elected candidates.
///
/// Section 5 of the NPoS paper shows that this property can be tested by: for a feasible solution,
/// if `Max {score(c)} < t` where c is every unelected candidate, then this solution is t-PJR. There
/// may exist edge cases which satisfy the formal definition of t-PJR but do not pass this test, but
/// those should be rare enough that we can discount them.
///
/// ### Interface
///
/// In addition to data that can be computed from the [`Supports`] struct, a PJR check also
/// needs to inspect un-elected candidates and edges, thus `all_candidates` and `all_voters`.
///
/// [NPoS]: https://arxiv.org/pdf/2004.12990v1.pdf
//
// ### Implementation Notes
//
// The paper uses mathematical notation, which priorities single-symbol names. For programmer ease,
// we map these to more descriptive names as follows:
//
// C      => all_candidates
// N      => all_voters
// (A, w) => (candidates, voters)
//
// Note that while the names don't explicitly say so, `candidates` are the winning candidates, and
// `voters` is the set of weighted edges from nominators to winning validators.
pub fn t_pjr_check<AccountId: IdentifierT>(
	supports: &Supports<AccountId>,
	all_candidates: Vec<AccountId>,
	all_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	t: Threshold,
) -> bool {
	// First order of business: derive `(candidates, voters)` from `supports`.
	let (candidates, voters) = prepare_pjr_input(
		supports,
		all_candidates,
		all_voters,
	);
	// compute with threshold t.
	pjr_check_core(candidates.as_ref(), voters.as_ref(), t)
}

/// The internal implementation of the PJR check after having the data converted.
///
/// [`pjr_check`] or [`t_pjr_check`] are typically easier to work with.
pub fn pjr_check_core<AccountId: IdentifierT>(
	candidates: &[CandidatePtr<AccountId>],
	voters: &[Voter<AccountId>],
	t: Threshold,
) -> bool {
	let unelected = candidates.iter().filter(|c| !c.borrow().elected);
	let maybe_max_pre_score = unelected.map(|c| (pre_score(Rc::clone(c), voters, t), c.borrow().who.clone())).max();
	// if unelected is empty then the solution is indeed PJR.
	maybe_max_pre_score.map_or(true, |(max_pre_score, _)| max_pre_score < t)
}



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
/// subset of the entire NPoS edge graph, encoded as `supports`. This only encodes the
/// edges that actually contribute to a winner's backing stake and ignores the rest to save space.
/// To check PJR, we need the entire voter set, including those edges that point to non-winners.
/// This could cause the caller runtime to have to read the entire list of voters, which is assumed
/// to be expensive.
///
/// A sensible user of this module should make sure that the PJR check is executed and checked as
/// little as possible, and take sufficient economical measures to ensure that this function cannot
/// be abused.
fn prepare_pjr_input<AccountId: IdentifierT>(
	supports: &Supports<AccountId>,
	all_candidates: Vec<AccountId>,
	all_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
) -> (Vec<CandidatePtr<AccountId>>, Vec<Voter<AccountId>>) {
	let mut candidates_index: BTreeMap<AccountId, usize> = BTreeMap::new();

	// dump the staked assignments in a voter-major map for faster access down the road.
	let mut assignment_map: BTreeMap<AccountId, Vec<(AccountId, ExtendedBalance)>> = BTreeMap::new();
	for (winner_id, Support { voters, .. }) in supports.iter() {
		for (voter_id, support) in voters.iter() {
			assignment_map.entry(voter_id.clone()).or_default().push((winner_id.clone(), *support));
		}
	}

	// Convert Suppports into a SupportMap
	//
	// As a flat list, we're limited to linear search. That gives the production of `candidates`,
	// below, a complexity of `O(s*c)`, where `s == supports.len()` and `c == all_candidates.len()`.
	// For large lists, that's pretty bad.
	//
	// A `SupportMap`, as a `BTreeMap`, has access timing of `O(lg n)`. This means that constructing
	// the map and then indexing from it gives us timing of `O((s + c) * lg(s))`. If in the future
	// we get access to a deterministic `HashMap`, we can further improve that to `O(s+c)`.
	//
	// However, it does mean allocating sufficient space to store all the data again.
	let supports: SupportMap<AccountId> = supports.iter().cloned().collect();

	// collect all candidates and winners into a unified `Vec<CandidatePtr>`.
	let candidates = all_candidates.into_iter().enumerate().map(|(i, c)| {
		candidates_index.insert(c.clone(), i);

		// set the backing value and elected flag if the candidate is among the winners.
		let who = c;
		let maybe_support = supports.get(&who);
		let elected = maybe_support.is_some();
		let backed_stake = maybe_support.map(|support| support.total).unwrap_or_default();

		Candidate { who, elected, backed_stake, ..Default::default() }.to_ptr()
	}).collect::<Vec<_>>();

	// collect all voters into a unified Vec<Voters>.
	let voters = all_voters.into_iter().map(|(v, w, ts)| {
		let mut edges: Vec<Edge<AccountId>> = Vec::with_capacity(ts.len());
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

/// The pre-score of an unelected candidate.
///
/// This is the amount of stake that *all voter* can spare to devote to this candidate without
/// allowing the backing stake of any other elected candidate to fall below `t`.
///
/// In essence, it is the sum(slack(n, t)) for all `n` who vote for `unelected`.
fn pre_score<AccountId: IdentifierT>(
	unelected: CandidatePtr<AccountId>,
	voters: &[Voter<AccountId>],
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
fn slack<AccountId: IdentifierT>(voter: &Voter<AccountId>, t: Threshold) -> ExtendedBalance {
	let budget = voter.budget;
	let leftover = voter.edges.iter().fold(Zero::zero(), |acc: ExtendedBalance, edge| {
		let candidate = edge.candidate.borrow();
		if candidate.elected {
			let extra =
				Perbill::one().min(Perbill::from_rational_approximation(t, candidate.backed_stake))
				* edge.weight;
			acc.saturating_add(extra)
		} else {
			// No slack generated here.
			acc
		}
	});

	// NOTE: candidate for saturating_log_sub(). Defensive-only.
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
		let all_candidates = vec![10, 20, 30, 40];
		let all_voters = vec![
			(1, 10, vec![10, 20, 30, 40]),
			(2, 20, vec![10, 20, 30, 40]),
			(3, 30, vec![10, 30]),
		];
		// tuples in voters vector are (AccountId, Balance)
		let supports: Supports<u32> = vec![
			(20, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
			(40, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
		];

		let (candidates, voters) = prepare_pjr_input(
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

	// These next tests ensure that the threshold phase change property holds for us, but that's not their real purpose.
	// They were written to help develop an intuition about what the threshold value actually means
	// in layman's terms.
	//
	// The results tend to support the intuition that the threshold is the voting power at and below
	// which a voter's preferences can simply be ignored.
	#[test]
	fn find_upper_bound_for_threshold_scenario_1() {
		let all_candidates = vec![10, 20, 30, 40];
		let all_voters = vec![
			(1, 10, vec![10, 20, 30, 40]),
			(2, 20, vec![10, 20, 30, 40]),
			(3, 30, vec![10, 30]),
		];
		// tuples in voters vector are (AccountId, Balance)
		let supports: Supports<u32> = vec![
			(20, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
			(40, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
		];

		let (candidates, voters) = prepare_pjr_input(
			&supports,
			all_candidates,
			all_voters,
		);

		find_threshold_phase_change_for_scenario(candidates, voters);
	}

	#[test]
	fn find_upper_bound_for_threshold_scenario_2() {
		let all_candidates = vec![10, 20, 30, 40];
		let all_voters = vec![
			(1, 10, vec![10, 20, 30, 40]),
			(2, 20, vec![10, 20, 30, 40]),
			(3, 25, vec![10, 30]),
		];
		// tuples in voters vector are (AccountId, Balance)
		let supports: Supports<u32> = vec![
			(20, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
			(40, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
		];

		let (candidates, voters) = prepare_pjr_input(
			&supports,
			all_candidates,
			all_voters,
		);

		find_threshold_phase_change_for_scenario(candidates, voters);
	}

	#[test]
	fn find_upper_bound_for_threshold_scenario_3() {
		let all_candidates = vec![10, 20, 30, 40];
		let all_voters = vec![
			(1, 10, vec![10, 20, 30, 40]),
			(2, 20, vec![10, 20, 30, 40]),
			(3, 35, vec![10, 30]),
		];
		// tuples in voters vector are (AccountId, Balance)
		let supports: Supports<u32> = vec![
			(20, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
			(40, Support { total: 15, voters: vec![(1, 5), (2, 10)]}),
		];

		let (candidates, voters) = prepare_pjr_input(
			&supports,
			all_candidates,
			all_voters,
		);

		find_threshold_phase_change_for_scenario(candidates, voters);
	}

	fn find_threshold_phase_change_for_scenario<AccountId: IdentifierT>(
		candidates: Vec<CandidatePtr<AccountId>>,
		voters: Vec<Voter<AccountId>>
	) -> Threshold {
		let mut threshold = 1;
		let mut prev_threshold = 0;

		// find the binary range containing the threshold beyond which the PJR check succeeds
		while !pjr_check_core(&candidates, &voters, threshold) {
			prev_threshold = threshold;
			threshold = threshold.checked_mul(2).expect("pjr check must fail before we run out of capacity in u128");
		}

		// now binary search within that range to find the phase threshold
		let mut high_bound = threshold;
		let mut low_bound = prev_threshold;

		while high_bound - low_bound > 1 {
			// maintain the invariant that low_bound fails and high_bound passes
			let test = low_bound + ((high_bound - low_bound) / 2);
			if pjr_check_core(&candidates, &voters, test) {
				high_bound = test;
			} else {
				low_bound = test;
			}
		}

		println!("highest failing check:   {}", low_bound);
		println!("lowest succeeding check: {}", high_bound);

		// for a value to be a threshold, it must be the boundary between two conditions
		let mut unexpected_failures = Vec::new();
		let mut unexpected_successes = Vec::new();
		for t in 0..=low_bound {
			if pjr_check_core(&candidates, &voters, t) {
				unexpected_successes.push(t);
			}
		}
		for t in high_bound..(high_bound*2) {
			if !pjr_check_core(&candidates, &voters, t) {
				unexpected_failures.push(t);
			}
		}
		dbg!(&unexpected_successes, &unexpected_failures);
		assert!(unexpected_failures.is_empty() && unexpected_successes.is_empty());

		high_bound
	}
}
