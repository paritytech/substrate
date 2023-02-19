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

//! Balancing algorithm implementation.
//!
//! Given a committee `A` and an edge weight vector `w`, a balanced solution is one that
//!
//! 1.  it maximizes the sum of member supports, i.e `Argmax { sum(support(c)) }`. for all `c` in
//! `A`.
//! 2. it minimizes the sum of supports squared, i.e `Argmin { sum(support(c).pow(2)) }` for all `c`
//! in `A`.
//!
//! See [`balance`] for more information.

use crate::{BalancingConfig, Edge, ExtendedBalance, IdentifierT, Voter};
use sp_arithmetic::traits::Zero;
use sp_std::prelude::*;

/// Balance the weight distribution of a given `voters` at most `iterations` times, or up until the
/// point where the biggest difference created per iteration of all stakes is `tolerance`. If this
/// is called with `tolerance = 0`, then exactly `iterations` rounds will be executed, except if no
/// change has been made (`difference = 0`). `tolerance` and `iterations` are part of the
/// [`BalancingConfig`] struct.
///
/// In almost all cases, a balanced solution will have a better score than an unbalanced solution,
/// yet this is not 100% guaranteed because the first element of a [`crate::ElectionScore`] does not
/// directly relate to balancing.
///
/// Note that some reference implementation adopt an approach in which voters are balanced randomly
/// per round. To advocate determinism, we don't do this. In each round, all voters are exactly
/// balanced once, in the same order.
///
/// Also, note that due to re-distribution of weights, the outcome of this function might contain
/// edges with weight zero. The call site should filter such weight if desirable. Moreover, the
/// outcome might need balance re-normalization, see `Voter::try_normalize`.
///
/// ### References
///
/// - [A new approach to the maximum flow problem](https://dl.acm.org/doi/10.1145/48014.61051).
/// - [Validator election in nominated proof-of-stake](https://arxiv.org/abs/2004.12990) (Appendix
///   A.)
/// - [Computing a balanced solution](https://research.web3.foundation/en/latest/polkadot/NPoS/3.%20Balancing.html),
///   which contains the details of the algorithm implementation.
pub fn balance<AccountId: IdentifierT>(
	voters: &mut Vec<Voter<AccountId>>,
	config: &BalancingConfig,
) -> usize {
	if config.iterations == 0 {
		return 0
	}

	let mut iter = 0;
	loop {
		let mut max_diff = 0;
		for voter in voters.iter_mut() {
			let diff = balance_voter(voter, config.tolerance);
			if diff > max_diff {
				max_diff = diff;
			}
		}

		iter += 1;
		if max_diff <= config.tolerance || iter >= config.iterations {
			break iter
		}
	}
}

/// Internal implementation of balancing for one voter.
pub(crate) fn balance_voter<AccountId: IdentifierT>(
	voter: &mut Voter<AccountId>,
	tolerance: ExtendedBalance,
) -> ExtendedBalance {
	// create a shallow copy of the elected ones. The original one will not be used henceforth.
	let mut elected_edges = voter
		.edges
		.iter_mut()
		.filter(|e| e.candidate.borrow().elected)
		.collect::<Vec<&mut Edge<AccountId>>>();

	// Either empty, or a self vote. Not much to do in either case.
	if elected_edges.len() <= 1 {
		return Zero::zero()
	}

	// amount of stake from this voter that is used in edges.
	let stake_used =
		elected_edges.iter().fold(0, |a: ExtendedBalance, e| a.saturating_add(e.weight));

	// backed stake of each of the elected edges.
	let backed_stakes = elected_edges
		.iter()
		.map(|e| e.candidate.borrow().backed_stake)
		.collect::<Vec<_>>();

	// backed stake of all the edges for whom we've spent some stake.
	let backing_backed_stake = elected_edges
		.iter()
		.filter_map(|e| if e.weight > 0 { Some(e.candidate.borrow().backed_stake) } else { None })
		.collect::<Vec<_>>();

	let difference = if backing_backed_stake.len() > 0 {
		let max_stake = backing_backed_stake
			.iter()
			.max()
			.expect("vector with positive length will have a max; qed");
		let min_stake = backed_stakes
			.iter()
			.min()
			.expect("iterator with positive length will have a min; qed");
		let mut difference = max_stake.saturating_sub(*min_stake);
		difference = difference.saturating_add(voter.budget.saturating_sub(stake_used));
		if difference < tolerance {
			return difference
		}
		difference
	} else {
		voter.budget
	};

	// remove all backings.
	for edge in elected_edges.iter_mut() {
		let mut candidate = edge.candidate.borrow_mut();
		candidate.backed_stake = candidate.backed_stake.saturating_sub(edge.weight);
		edge.weight = 0;
	}

	elected_edges.sort_by_key(|e| e.candidate.borrow().backed_stake);

	let mut cumulative_backed_stake = Zero::zero();
	let mut last_index = elected_edges.len() - 1;

	for (index, edge) in elected_edges.iter().enumerate() {
		let index = index as ExtendedBalance;
		let backed_stake = edge.candidate.borrow().backed_stake;
		let temp = backed_stake.saturating_mul(index);
		if temp.saturating_sub(cumulative_backed_stake) > voter.budget {
			// defensive only. length of elected_edges is checked to be above 1.
			last_index = index.saturating_sub(1) as usize;
			break
		}
		cumulative_backed_stake = cumulative_backed_stake.saturating_add(backed_stake);
	}

	let last_stake = elected_edges
		.get(last_index)
		.expect(
			"length of elected_edges is greater than or equal 2; last_index index is at the \
 			 minimum elected_edges.len() - 1; index is within range; qed",
		)
		.candidate
		.borrow()
		.backed_stake;
	let ways_to_split = last_index + 1;
	let excess = voter
		.budget
		.saturating_add(cumulative_backed_stake)
		.saturating_sub(last_stake.saturating_mul(ways_to_split as ExtendedBalance));

	// Do the final update.
	for edge in elected_edges.into_iter().take(ways_to_split) {
		// first, do one scoped borrow to get the previous candidate stake.
		let candidate_backed_stake = {
			let candidate = edge.candidate.borrow();
			candidate.backed_stake
		};

		let new_edge_weight = (excess / ways_to_split as ExtendedBalance)
			.saturating_add(last_stake)
			.saturating_sub(candidate_backed_stake);

		// write the new edge weight
		edge.weight = new_edge_weight;

		// write the new candidate stake
		let mut candidate = edge.candidate.borrow_mut();
		candidate.backed_stake = candidate.backed_stake.saturating_add(new_edge_weight);
	}

	// excess / ways_to_split can cause a small un-normalized voters to be created.
	// We won't `expect` here because even a result which is not normalized is not corrupt;
	let _ = voter.try_normalize_elected();

	difference
}
