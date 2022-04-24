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

//! Implementation of the MMS method.
//!
//! This is algorithm 1 from the paper: <https://arxiv.org/pdf/2004.12990.pdf>
//!
//! It is also further explained in [The Maximin Support Method: An Extension of the D'Hondt Method to Approval-Based Multiwinner Elections](https://arxiv.org/abs/1609.05370).

use crate::{
	balance, setup_inputs, CandidatePtr, ElectionResult, ExtendedBalance, IdentifierT, PerThing128,
	Rc, Vec, VoteWeight, Voter, Zero,
};

use sp_std::vec;

/// Execute the `MMS` method.
///
/// This can be used interchangeably with [`seq-phragmen`] or `phragmms` and offers a
/// similar API, namely:
///
/// - The resulting edge weight distribution is normalized (thus, safe to use for submission).
/// - The accuracy can be configured via the generic type `P`.
/// - The algorithm is a _best-effort_ to elect `to_elect`. If less candidates are provided, less
///   winners are returned, without an error.
///
/// Inputs are:
/// - `to_elect` is the number of winners to elect.
/// - `candidates` is the list of candidates.
/// - `voters` is the list of voters.
/// - `iterations` is the number of iterations to perform while balancing.
/// - `tolerance` is the tolerance of the balancing.
///
/// This can only fail in 2 cases: 1) the `candidates` set is empty, 2) the normalization fails.
/// The latter can happen if for any of the resulting assignments, `assignment.distribution.map(|p|
/// p.deconstruct()).sum()` fails to fit inside `UpperOf<P>`. A user of this crate may statically
/// assert that this can never happen and safely `expect` this to return `Ok`.
pub fn mms<AccountId: IdentifierT, P: PerThing128>(
	to_elect: usize,
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	iterations: usize,
	tolerance: ExtendedBalance,
) -> Result<ElectionResult<AccountId, P>, crate::Error> {
	let mut winners = vec![]; // `A` in the paper.

	if candidates.is_empty() {
		return Err(crate::Error::NoCandidates)
	}

	// To be able to amend it below
	let mut candidates = candidates;
	let voters = convert_voters(voters);

	for _round in 0..to_elect {
		let mut max_support = Zero::zero();
		let mut winner_idx = 0; // we tested above that it's not empty
		for (index, candidate) in candidates.iter().enumerate() {
			// Find `argmax_{c in C\A} supp_{w_c}(A+c)`
			let support = calculate_support(
				winners.clone(),
				(*candidate).clone(),
				voters.clone(),
				iterations,
				tolerance,
			);

			// maximize stake
			if support > max_support {
				max_support = support;
				winner_idx = index;
			}
		}

		// `c in C \ A` in the paper. so we need to remove the winner from the candidates.
		winners.push(candidates.swap_remove(winner_idx));
	}

	// Make sure weights are correct and normalized.
	let (used_candidates, used_voters) =
		setup_inputs_with_balance(winners, voters, iterations, tolerance);

	crate::voter_candidate_to_election_result(used_voters, used_candidates)
}

/// Utility function to avoid having to add Clone as a trait
fn convert_voters<AccountId>(
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
) -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
	voters
		.into_iter()
		.map(|(voter, weight, votes)| (voter, weight, votes.into_iter().collect()))
		.collect()
}

/// Constructs the `voters` and `candidates` inputs for the `mms` function.
///
/// This is an internal part of the [`mms`].
fn setup_inputs_with_balance<AccountId: IdentifierT>(
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	iterations: usize,
	tolerance: ExtendedBalance,
) -> (Vec<CandidatePtr<AccountId>>, Vec<Voter<AccountId>>) {
	let (used_candidates, mut used_voters) = setup_inputs(candidates, voters);
	for (index, c) in used_candidates.iter().enumerate() {
		c.borrow_mut().elected = true;
		c.borrow_mut().round = index;
		apply_elected(&mut used_voters, Rc::clone(c));
	}
	balance(&mut used_voters, iterations, tolerance);

	(used_candidates, used_voters)
}

/// Calculates the balance weight vector `w_c` for `A + c`
///
/// This is an internal part of the [`mms`].
fn calculate_support<AccountId: IdentifierT>(
	mut candidates: Vec<AccountId>,
	candidate: AccountId,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	iterations: usize,
	tolerance: ExtendedBalance,
) -> ExtendedBalance {
	candidates.push(candidate.clone());

	// Calculate the balance weight vector `w_c` for `A + c`
	let (used_candidates, _) = setup_inputs_with_balance(candidates, voters, iterations, tolerance);

	let support = used_candidates
		.iter()
		.find(|x| x.borrow().who == candidate)
		.unwrap()
		.borrow()
		.backed_stake;

	support
}

/// Update the weights of `voters` given that `elected_ptr` has been elected in the previous round.
///
/// Updates `voters` in place.
///
/// This is an internal part of the [`mms`] and should be called before calling [`balance`].
fn apply_elected<AccountId: IdentifierT>(
	voters: &mut Vec<Voter<AccountId>>,
	elected_ptr: CandidatePtr<AccountId>,
) {
	let elected_who = elected_ptr.borrow().who.clone();
	let mut elected_backed_stake: ExtendedBalance = Zero::zero();

	for voter in voters {
		if let Some(new_edge_index) = voter.edges.iter().position(|e| e.who == elected_who) {
			elected_backed_stake = elected_backed_stake.saturating_add(voter.budget);
			voter.edges[new_edge_index].weight = voter.budget;
		}
	}

	elected_ptr.borrow_mut().backed_stake = elected_backed_stake;
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{Assignment, ElectionResult};
	use sp_runtime::Perbill;
	#[test]
	fn basic_election_works() {
		let candidates = vec![1, 2, 3];
		let voters = vec![(10, 10, vec![1, 2]), (20, 20, vec![1, 3]), (30, 30, vec![2, 3])];

		let ElectionResult::<_, Perbill> { winners, assignments } =
			mms(2, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners, vec![(3, 30), (1, 30)]);
		assert_eq!(
			assignments,
			vec![
				Assignment { who: 10u64, distribution: vec![(1, Perbill::one())] },
				Assignment { who: 20, distribution: vec![(1, Perbill::one())] },
				Assignment { who: 30, distribution: vec![(3, Perbill::one()),] },
			]
		)
	}

	#[test]
	fn linear_voting_example_works() {
		let candidates = vec![11, 21, 31, 41, 51, 61, 71];
		let voters = vec![
			(2, 2000, vec![11]),
			(4, 1000, vec![11, 21]),
			(6, 1000, vec![21, 31]),
			(8, 1000, vec![31, 41]),
			(110, 1000, vec![41, 51]),
			(120, 1000, vec![51, 61]),
			(130, 1000, vec![61, 71]),
		];

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(4, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners, vec![(11, 2000), (21, 2000), (61, 2000), (41, 2000),]);
	}

	#[test]
	fn large_balance_wont_overflow() {
		let candidates = vec![1u32, 2, 3];
		let mut voters = (0..1000).map(|i| (10 + i, u64::MAX, vec![1, 2, 3])).collect::<Vec<_>>();

		// give a bit more to 1 and 3.
		voters.push((2, u64::MAX, vec![1, 3]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(2, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners.into_iter().map(|(w, _)| w).collect::<Vec<_>>(), vec![1u32, 3]);
	}

	#[test]
	fn paper_example_works() {
		let candidates = vec![1, 2, 3, 4, 5, 6, 7];
		let voters = vec![
			(10, 10_000, vec![1, 2]),
			(20, 6_000, vec![1, 3]),
			(30, 4_000, vec![2]),
			(40, 5_500, vec![3]),
			(50, 9_500, vec![4]),
			(60, 5_000, vec![5, 6, 7]),
			(70, 3_000, vec![5]),
		];

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(3, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners, vec![(1, 10750), (3, 10750), (4, 9500)]);
	}

	#[test]
	fn mms_solution_house_monotonic() {
		let candidates = vec![1, 2, 3, 4, 5, 6, 7];
		let voters = vec![
			(10, 10_000, vec![1, 2]),
			(20, 6_000, vec![1, 3]),
			(30, 4_000, vec![2]),
			(40, 5_500, vec![3]),
			(50, 9_500, vec![4]),
			(60, 5_000, vec![5, 6, 7]),
			(70, 3_000, vec![5]),
		];

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(2, candidates.clone(), voters.clone(), 2, 0).unwrap();
		let ElectionResult::<_, Perbill> { winners: winners2, assignments: _ } =
			mms(2, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners2[..2], winners);
	}

	#[test]
	fn mms_not_strong_monotonicity() {
		let mut candidates = vec![1, 2, 3, 4, 5, 6, 7];
		let mut voters = (0..13).map(|i| (10 + i, 100, vec![3, 4, 5, 6, 7])).collect::<Vec<_>>();
		voters.push((30, 100, vec![1, 2]));
		voters.push((31, 100, vec![1, 2]));
		voters.push((40, 100, vec![1]));
		voters.push((41, 100, vec![1]));
		voters.push((50, 100, vec![2]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(6, candidates.clone(), voters.clone(), 2, 0).unwrap();
		assert_eq!(winners, vec![(3, 260), (7, 260), (6, 260), (1, 400), (4, 260), (5, 260)]);

		voters.push((60, 100, vec![1, 3, 4, 5, 6, 7]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(6, candidates.clone(), voters.clone(), 2, 0).unwrap();
		assert_eq!(winners, vec![(3, 325), (7, 325), (1, 300), (5, 325), (4, 325), (2, 300)]);

		voters.pop();
		candidates.push(8);
		voters.push((60, 100, vec![8]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(6, candidates.clone(), voters.clone(), 2, 0).unwrap();
		assert_eq!(winners, vec![(3, 260), (4, 260), (7, 260), (1, 400), (5, 260), (6, 260)]);

		voters.pop();
		voters.push((60, 100, vec![1, 3, 4, 5, 6, 7, 8]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(6, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners, vec![(3, 325), (4, 325), (1, 300), (6, 325), (5, 325), (2, 300)]);
	}

	#[test]
	fn mms_not_pjr() {
		let candidates = vec![1, 2, 3, 4, 5, 6, 7];
		let voters = vec![
			(10, 500, vec![1, 4, 5, 6, 7]),
			(20, 400, vec![2, 4, 5, 6, 7]),
			(30, 300, vec![3, 4, 5, 6, 7]),
			(40, 200, vec![1]),
			(50, 100, vec![2]),
			(60, 100, vec![3]),
		];

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(4, candidates, voters, 20, 0).unwrap();
		assert_eq!(winners, vec![(4, 400), (1, 400), (2, 400), (3, 400)]);
	}
}
