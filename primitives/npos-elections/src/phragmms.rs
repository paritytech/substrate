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

//! Implementation of the PhragMMS method.
//!
//! The naming comes from the fact that this method is highly inspired by Phragmen's method, yet it
//! _also_ provides a constant factor approximation of the Maximin problem, similar to that of the
//! MMS algorithm.

use crate::{
	IdentifierT, ElectionResult, ExtendedBalance, setup_inputs, VoteWeight, Voter, CandidatePtr,
	balance,
};
use sp_arithmetic::{PerThing, InnerOf, Rational128, traits::Bounded};
use sp_std::{prelude::*, rc::Rc};

/// Execute the phragmms method.
///
/// This can be used interchangeably with [`seq-phragmen`] and offers a similar API, namely:
///
/// - The resulting edge weight distribution is normalized (thus, safe to use for submission).
/// - The accuracy can be configured via the generic type `P`.
/// - The algorithm is a _best-effort_ to elect `to_elect`. If less candidates are provided, less
///   winners are returned, without an error.
///
/// This can only fail of the normalization fails. This can happen if for any of the resulting
/// assignments, `assignment.distribution.map(|p| p.deconstruct()).sum()` fails to fit inside
/// `UpperOf<P>`. A user of this crate may statically assert that this can never happen and safely
/// `expect` this to return `Ok`.
pub fn phragmms<AccountId: IdentifierT, P: PerThing>(
	to_elect: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	balancing_config: Option<(usize, ExtendedBalance)>,
) -> Result<ElectionResult<AccountId, P>, &'static str>
	where ExtendedBalance: From<InnerOf<P>>
{
	let (candidates, mut voters) = setup_inputs(initial_candidates, initial_voters);

	let mut winners = vec![];
	for round in 0..to_elect {
		if let Some(round_winner) = calculate_max_score::<AccountId, P>(&candidates, &voters) {
			apply_elected::<AccountId>(&mut voters, Rc::clone(&round_winner));

			round_winner.borrow_mut().round = round;
			round_winner.borrow_mut().elected = true;
			winners.push(round_winner);

			if let Some((iterations, tolerance)) = balancing_config {
				balance(&mut voters, iterations, tolerance);
			}
		} else {
			break;
		}
	}

	let mut assignments = voters.into_iter().filter_map(|v| v.into_assignment()).collect::<Vec<_>>();
	let _ = assignments.iter_mut().map(|a| a.try_normalize()).collect::<Result<(), _>>()?;
	let winners = winners.into_iter().map(|w_ptr|
		(w_ptr.borrow().who.clone(), w_ptr.borrow().backed_stake)
	).collect();

	Ok(ElectionResult { winners, assignments })
}

/// Find the candidate that can yield the maximum score for this round.
///
/// Returns a new `Some(CandidatePtr)` to the winner candidate. The score of the candidate is
/// updated and can be read from the returned pointer.
///
/// If no winner can be determined (i.e. everyone is already elected), then `None` is returned.
///
/// This is an internal part of the [`phragmms`].
pub(crate) fn calculate_max_score<AccountId: IdentifierT, P: PerThing>(
	candidates: &[CandidatePtr<AccountId>],
	voters: &[Voter<AccountId>],
) -> Option<CandidatePtr<AccountId>> where ExtendedBalance: From<InnerOf<P>> {
	for c_ptr in candidates.iter() {
		let mut candidate = c_ptr.borrow_mut();
		if !candidate.elected {
			candidate.score = Rational128::from(1, P::ACCURACY.into());
		}
	}

	for voter in voters.iter() {
		let mut denominator_contribution: ExtendedBalance = 0;

		// gather contribution from all elected edges.
		for edge in voter.edges.iter() {
			let edge_candidate = edge.candidate.borrow();
			if edge_candidate.elected {
				let edge_contribution: ExtendedBalance = P::from_rational_approximation(
					edge.weight,
					edge_candidate.backed_stake,
				).deconstruct().into();
				denominator_contribution += edge_contribution;
			}
		}

		// distribute to all _unelected_ edges.
		for edge in voter.edges.iter() {
			let mut edge_candidate = edge.candidate.borrow_mut();
			if !edge_candidate.elected {
				let prev_d = edge_candidate.score.d();
				edge_candidate.score = Rational128::from(1, denominator_contribution + prev_d);
			}
		}
	}

	// finalise the score value, and find the best.
	let mut best_score = Rational128::zero();
	let mut best_candidate = None;

	for c_ptr in candidates.iter() {
		let mut candidate = c_ptr.borrow_mut();
		if candidate.approval_stake > 0  {
			// finalise the score value.
			let score_d = candidate.score.d();
			let one: ExtendedBalance = P::ACCURACY.into();
			// Note: the accuracy here is questionable.
			// First, let's consider what will happen if this saturates. In this case, two very
			// whale-like validators will be effectively the same and their score will be equal.
			// This is, more or less fine if the threshold of saturation is high and only a small
			// subset or ever likely to become saturated. Once saturated, the score of these whales
			// are effectively the same.
			// Let's consider when this will happen. The approval stake of a target is the sum of
			// stake of all the voter who have backed this target. Given the fact that the total
			// issuance of a sane chain will fit in u128, it is safe to also assume that the
			// approval stake will, since it is a subset of the total issuance at most.
			// Finally, the only chance of overflow is multiplication by `one`. This highly depends
			// on the `P` generic argument. With a PerBill and a 12 decimal token the maximum value
			// that `candidate.approval_stake` can have is:
			// (2 ** 128 - 1) / 10**9 / 10**12  = 340,282,366,920,938,463
			// Assuming that each target will have 200,000 voters, then each voter's stake can be
			// roughly:
			// (2 ** 128 - 1) / 10**9 / 10**12 / 200000 = 1,701,411,834,604
			//
			// It is worth noting that these value would be _very_ different if one were to use
			// `PerQuintill` as `P`. For now, we prefer the performance of using `Rational128` here.
			// For the future, a properly benchmarked pull request can prove that using
			// `RationalInfinite` as the score type does not introduce significant overhead. Then we
			// can switch the score type to `RationalInfinite` and ensure compatibility with any
			// crazy token scale.
			let score_n = candidate.approval_stake.checked_mul(one).unwrap_or_else(|| Bounded::max_value());
			candidate.score = Rational128::from(score_n, score_d);

			// check if we have a new winner.
			if !candidate.elected && candidate.score > best_score {
				best_score = candidate.score;
				best_candidate = Some(Rc::clone(&c_ptr));
			}
		} else {
			candidate.score = Rational128::zero();
		}
	}

	best_candidate
}

/// Update the weights of `voters` given that `elected_ptr` has been elected in the previous round.
///
/// Updates `voters` in place.
///
/// This is an internal part of the [`phragmms`] and should be called after
/// [`calculate_max_score`].
pub(crate) fn apply_elected<AccountId: IdentifierT>(
	voters: &mut Vec<Voter<AccountId>>,
	elected_ptr: CandidatePtr<AccountId>,
) {
	let elected_who = elected_ptr.borrow().who.clone();
	let cutoff = elected_ptr.borrow().score.to_den(1)
		.expect("(n / d) < u128::max() and (n' / 1) == (n / d), thus n' < u128::max()'; qed.")
		.n();

	let mut elected_backed_stake = elected_ptr.borrow().backed_stake;
	for voter in voters {
		if let Some(new_edge_index) = voter.edges.iter().position(|e| e.who == elected_who) {
			let used_budget: ExtendedBalance = voter.edges.iter().map(|e| e.weight).sum();

			let mut new_edge_weight = voter.budget.saturating_sub(used_budget);
			elected_backed_stake = elected_backed_stake.saturating_add(new_edge_weight);

			// Iterate over all other edges.
			for (_, edge) in voter.edges
				.iter_mut()
				.enumerate()
				.filter(|(edge_index, edge_inner)| *edge_index != new_edge_index && edge_inner.weight > 0)
			{
				let mut edge_candidate = edge.candidate.borrow_mut();
				if edge_candidate.backed_stake > cutoff {
					let stake_to_take = edge.weight.saturating_mul(cutoff) / edge_candidate.backed_stake.max(1);

					// subtract this amount from this edge.
					edge.weight = edge.weight.saturating_sub(stake_to_take);
					edge_candidate.backed_stake = edge_candidate.backed_stake.saturating_sub(stake_to_take);

					// inject it into the outer loop's edge.
					elected_backed_stake = elected_backed_stake.saturating_add(stake_to_take);
					new_edge_weight = new_edge_weight.saturating_add(stake_to_take);
				}
			}

			voter.edges[new_edge_index].weight = new_edge_weight;
		}
	}

	// final update.
	elected_ptr.borrow_mut().backed_stake = elected_backed_stake;
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{ElectionResult, Assignment};
	use sp_runtime::{Perbill, Percent};
	use sp_std::rc::Rc;

	#[test]
	fn basic_election_manual_works() {
		//! Manually run the internal steps of phragmms. In each round we select a new winner by
		//! `max_score`, then apply this change by `apply_elected`, and finally do a `balance` round.
		let candidates = vec![1, 2, 3];
		let voters = vec![
			(10, 10, vec![1, 2]),
			(20, 20, vec![1, 3]),
			(30, 30, vec![2, 3]),
		];

		let (candidates, mut voters) = setup_inputs(candidates, voters);

		// Round 1
		let winner = calculate_max_score::<u32, Percent>(candidates.as_ref(), voters.as_ref()).unwrap();
		assert_eq!(winner.borrow().who, 3);
		assert_eq!(winner.borrow().score, 50u32.into());

		apply_elected(&mut voters, Rc::clone(&winner));
		assert_eq!(
			voters.iter().find(|x| x.who == 30).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(30, vec![(2, 0), (3, 30)]),
		);
		assert_eq!(
			voters.iter().find(|x| x.who == 20).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(20, vec![(1, 0), (3, 20)]),
		);

		// finish the round.
		winner.borrow_mut().elected = true;
		winner.borrow_mut().round = 0;
		drop(winner);

		// balancing makes no difference here but anyhow.
		balance(&mut voters, 10, 0);

		// round 2
		let winner = calculate_max_score::<u32, Percent>(candidates.as_ref(), voters.as_ref()).unwrap();
		assert_eq!(winner.borrow().who, 2);
		assert_eq!(winner.borrow().score, 25u32.into());

		apply_elected(&mut voters, Rc::clone(&winner));
		assert_eq!(
			voters.iter().find(|x| x.who == 30).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(30, vec![(2, 15), (3, 15)]),
		);
		assert_eq!(
			voters.iter().find(|x| x.who == 20).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(20, vec![(1, 0), (3, 20)]),
		);
		assert_eq!(
			voters.iter().find(|x| x.who == 10).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(10, vec![(1, 0), (2, 10)]),
		);

		// finish the round.
		winner.borrow_mut().elected = true;
		winner.borrow_mut().round = 0;
		drop(winner);

		// balancing will improve stuff here.
		balance(&mut voters, 10, 0);

		assert_eq!(
			voters.iter().find(|x| x.who == 30).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(30, vec![(2, 20), (3, 10)]),
		);
		assert_eq!(
			voters.iter().find(|x| x.who == 20).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(20, vec![(1, 0), (3, 20)]),
		);
		assert_eq!(
			voters.iter().find(|x| x.who == 10).map(|v| (
				v.who,
				v.edges.iter().map(|e| (e.who, e.weight)).collect::<Vec<_>>()
			)).unwrap(),
			(10, vec![(1, 0), (2, 10)]),
		);
	}

	#[test]
	fn basic_election_works() {
		let candidates = vec![1, 2, 3];
		let voters = vec![
			(10, 10, vec![1, 2]),
			(20, 20, vec![1, 3]),
			(30, 30, vec![2, 3]),
		];

		let ElectionResult { winners, assignments } = phragmms::<_, Perbill>(2, candidates, voters, Some((2, 0))).unwrap();
		assert_eq!(winners, vec![(3, 30), (2, 30)]);
		assert_eq!(
			assignments,
			vec![
				Assignment {
					who: 10u64,
					distribution: vec![(2, Perbill::one())],
				},
				Assignment {
					who: 20,
					distribution: vec![(3, Perbill::one())],
				},
				Assignment {
					who: 30,
					distribution: vec![
						(2, Perbill::from_parts(666666666)),
						(3, Perbill::from_parts(333333334)),
					],
				},
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

		let ElectionResult { winners, assignments: _ } = phragmms::<_, Perbill>(4, candidates, voters, Some((2, 0))).unwrap();
		assert_eq!(winners, vec![
			(11, 3000),
			(31, 2000),
			(51, 1500),
			(61, 1500),
		]);
	}

	#[test]
	fn large_balance_wont_overflow() {
		let candidates = vec![1u32, 2, 3];
		let mut voters = (0..1000).map(|i| (10 + i, u64::max_value(), vec![1, 2, 3])).collect::<Vec<_>>();

		// give a bit more to 1 and 3.
		voters.push((2, u64::max_value(), vec![1, 3]));

		let ElectionResult { winners, assignments: _ } = phragmms::<_, Perbill>(2, candidates, voters, Some((2, 0))).unwrap();
		assert_eq!(winners.into_iter().map(|(w, _)| w).collect::<Vec<_>>(), vec![1u32, 3]);
	}
}
