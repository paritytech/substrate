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

//! Implementation of the sequential-phragmen election method.
//!
//! This method is ensured to achieve PJR, yet, it does not achieve a constant factor approximation
//! to the Maximin problem.

use crate::{
	balancing, setup_inputs, BalancingConfig, CandidatePtr, ElectionResult, ExtendedBalance,
	IdentifierT, PerThing128, VoteWeight, Voter,
};
use sp_arithmetic::{
	helpers_128bit::multiply_by_rational_with_rounding,
	traits::{Bounded, Zero},
	Rational128, Rounding,
};
use sp_std::prelude::*;

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::MAX is needed. For maximum accuracy we simply use u128;
const DEN: ExtendedBalance = ExtendedBalance::max_value();

/// Execute sequential phragmen with potentially some rounds of `balancing`. The return type is list
/// of winners and a weight distribution vector of all voters who contribute to the winners.
///
/// - This function is a best effort to elect `rounds` members. Nonetheless, if less candidates are
///   available, it will only return what is available. It is the responsibility of the call site to
///   ensure they have provided enough members.
/// - If `balance` parameter is `Some(i, t)`, `i` iterations of balancing is with tolerance `t` is
///   performed.
/// - Returning winners are sorted based on desirability. Voters are unsorted. Nonetheless,
///   seq-phragmen is in general an un-ranked election and the desirability should not be
///   interpreted with any significance.
/// - The returning winners are zipped with their final backing stake. Yet, to get the exact final
///   weight distribution from the winner's point of view, one needs to build a support map. See
///   [`crate::SupportMap`] for more info. Note that this backing stake is computed in
///   ExtendedBalance and may be slightly different that what will be computed from the support map,
///   due to accuracy loss.
/// - The accuracy of the returning edge weight ratios can be configured via the `P` generic
///   argument.
/// - The returning weight distribution is _normalized_, meaning that it is guaranteed that the sum
///   of the ratios in each voter's distribution sums up to exactly `P::one()`.
///
/// This can only fail of the normalization fails. This can happen if for any of the resulting
/// assignments, `assignment.distribution.map(|p| p.deconstruct()).sum()` fails to fit inside
/// `UpperOf<P>`. A user of this crate may statically assert that this can never happen and safely
/// `expect` this to return `Ok`.
///
/// This can only fail if the normalization fails.
///
/// Note that rounding errors can potentially cause the output of this function to fail a t-PJR
/// check where t is the standard threshold. The underlying algorithm is sound, but the conversions
/// between numeric types can be lossy.
pub fn seq_phragmen<AccountId: IdentifierT, P: PerThing128>(
	to_elect: usize,
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	balancing: Option<BalancingConfig>,
) -> Result<ElectionResult<AccountId, P>, crate::Error> {
	let (candidates, voters) = setup_inputs(candidates, voters);

	let (candidates, mut voters) = seq_phragmen_core::<AccountId>(to_elect, candidates, voters)?;

	if let Some(ref config) = balancing {
		// NOTE: might create zero-edges, but we will strip them again when we convert voter into
		// assignment.
		let _iters = balancing::balance::<AccountId>(&mut voters, config);
	}

	let mut winners = candidates
		.into_iter()
		.filter(|c_ptr| c_ptr.borrow().elected)
		// defensive only: seq-phragmen-core returns only up to rounds.
		.take(to_elect)
		.collect::<Vec<_>>();

	// sort winners based on desirability.
	winners.sort_by_key(|c_ptr| c_ptr.borrow().round);

	let mut assignments =
		voters.into_iter().filter_map(|v| v.into_assignment()).collect::<Vec<_>>();
	let _ = assignments
		.iter_mut()
		.try_for_each(|a| a.try_normalize().map_err(crate::Error::ArithmeticError))?;
	let winners = winners
		.into_iter()
		.map(|w_ptr| (w_ptr.borrow().who.clone(), w_ptr.borrow().backed_stake))
		.collect();

	Ok(ElectionResult { winners, assignments })
}

/// Core implementation of seq-phragmen.
///
/// This is the internal implementation that works with the types defined in this crate. see
/// `seq_phragmen` for more information. This function is left public in case a crate needs to use
/// the implementation in a custom way.
///
/// This can only fail if the normalization fails.
// To create the inputs needed for this function, see [`crate::setup_inputs`].
pub fn seq_phragmen_core<AccountId: IdentifierT>(
	to_elect: usize,
	candidates: Vec<CandidatePtr<AccountId>>,
	mut voters: Vec<Voter<AccountId>>,
) -> Result<(Vec<CandidatePtr<AccountId>>, Vec<Voter<AccountId>>), crate::Error> {
	// we have already checked that we have more candidates than minimum_candidate_count.
	let to_elect = to_elect.min(candidates.len());

	// main election loop
	for round in 0..to_elect {
		// loop 1: initialize score
		for c_ptr in &candidates {
			let mut candidate = c_ptr.borrow_mut();
			if !candidate.elected {
				// 1 / approval_stake == (DEN / approval_stake) / DEN. If approval_stake is zero,
				// then the ratio should be as large as possible, essentially `infinity`.
				if candidate.approval_stake.is_zero() {
					candidate.score = Bounded::max_value();
				} else {
					candidate.score = Rational128::from(DEN / candidate.approval_stake, DEN);
				}
			}
		}

		// loop 2: increment score
		for voter in &voters {
			for edge in &voter.edges {
				let mut candidate = edge.candidate.borrow_mut();
				if !candidate.elected && !candidate.approval_stake.is_zero() {
					let temp_n = multiply_by_rational_with_rounding(
						voter.load.n(),
						voter.budget,
						candidate.approval_stake,
						Rounding::Down,
					)
					.unwrap_or(Bounded::max_value());
					let temp_d = voter.load.d();
					let temp = Rational128::from(temp_n, temp_d);
					candidate.score = candidate.score.lazy_saturating_add(temp);
				}
			}
		}

		// loop 3: find the best
		if let Some(winner_ptr) = candidates
			.iter()
			.filter(|c| !c.borrow().elected)
			.min_by_key(|c| c.borrow().score)
		{
			let mut winner = winner_ptr.borrow_mut();
			// loop 3: update voter and edge load
			winner.elected = true;
			winner.round = round;
			for voter in &mut voters {
				for edge in &mut voter.edges {
					if edge.who == winner.who {
						edge.load = winner.score.lazy_saturating_sub(voter.load);
						voter.load = winner.score;
					}
				}
			}
		} else {
			break
		}
	}

	// update backing stake of candidates and voters
	for voter in &mut voters {
		for edge in &mut voter.edges {
			if edge.candidate.borrow().elected {
				// update internal state.
				edge.weight = multiply_by_rational_with_rounding(
					voter.budget,
					edge.load.n(),
					voter.load.n(),
					Rounding::Down,
				)
				// If result cannot fit in u128. Not much we can do about it.
				.unwrap_or(Bounded::max_value());
			} else {
				edge.weight = 0
			}
			let mut candidate = edge.candidate.borrow_mut();
			candidate.backed_stake = candidate.backed_stake.saturating_add(edge.weight);
		}

		// remove all zero edges. These can become phantom edges during normalization.
		voter.edges.retain(|e| e.weight > 0);
		// edge of all candidates that eventually have a non-zero weight must be elected.
		debug_assert!(voter.edges.iter().all(|e| e.candidate.borrow().elected));
		// inc budget to sum the budget.
		voter.try_normalize_elected().map_err(crate::Error::ArithmeticError)?;
	}

	Ok((candidates, voters))
}
