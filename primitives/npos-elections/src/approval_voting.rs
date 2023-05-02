// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Implementation of the approval voting election method.
//!
//! This method allows voters to select many candidates and backing each of them with the same
//! vote weight. The candidates with the most backing are the election winners.

use crate::{setup_inputs, ElectionResult, IdentifierT, PerThing128, VoteWeight};
use sp_arithmetic::traits::Zero;
use sp_std::{cmp::Reverse, vec::Vec};

/// Execute an approvals voting election scheme. The return type is a list of winners. The weight
/// vector of all voters who contribute to the winners, which for this scheme is always 100% per
/// vote.
///
/// - The vote assignment distribution for each vote is always 100%, since a voter backs a candidate
///   with its full stake, regardless of how many candidates are backed by the same stake. However,
///   the caller may normalize votes on site if required.
/// - Returning winners are sorted based on desirability. Voters are unsorted.
/// - The returning winners are zipped with their final backing stake. Yet, to get the exact final
///   weight distribution from the winner's point of view, one needs to build a support map. See
///   [`crate::SupportMap`] for more info. Note that this backing stake is computed in
///   ExtendedBalance and may be slightly different that what will be computed from the support map,
///   due to accuracy loss.
///
/// This can only fail if the normalization fails. This can happen if for any of the resulting
/// assignments, `assignment.distribution.map(|p| p.deconstruct()).sum()` fails to fit inside
/// `UpperOf<P>`. A user of this crate may statically assert that this can never happen and safely
/// `expect` this to return `Ok`.
pub fn approval_voting<AccountId: IdentifierT, P: PerThing128>(
	to_elect: usize,
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
) -> Result<ElectionResult<AccountId, P>, crate::Error> {
	let to_elect = to_elect.min(candidates.len());

	let (mut candidates, mut voters) = setup_inputs(candidates, voters);

	candidates.sort_by_key(|c| Reverse(c.borrow().approval_stake));

	let winners = candidates
		.into_iter()
		.take(to_elect)
		.map(|w| {
			w.borrow_mut().elected = true;
			w
		})
		.map(|w_ptr| (w_ptr.borrow().who.clone(), w_ptr.borrow().approval_stake))
		.collect();

	for voter in &mut voters {
		for edge in &mut voter.edges {
			if edge.candidate.borrow().elected {
				edge.weight = voter.budget
			} else {
				edge.weight = Zero::zero()
			}
		}
	}

	let assignments = voters.into_iter().filter_map(|v| v.into_assignment()).collect::<Vec<_>>();

	Ok(ElectionResult { winners, assignments })
}
