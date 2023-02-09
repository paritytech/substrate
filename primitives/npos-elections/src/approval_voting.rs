// This file is part of Substrate.

// Copyright (C) 2020-2023 Parity Technologies (UK) Ltd.
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
use sp_arithmetic::{traits::{Bounded, Zero}, Rounding, helpers_128bit::multiply_by_rational_with_rounding};
use sp_std::cmp::Reverse;

/// Execute an approvals voting election scheme. The return type is a list of winners and a weight
/// distribution vector of all voters who contribute to the winners.
///
/// - Returning winners are sorted based on desirability. Voters are unsorted.
/// - The returning winners are zipped with their final backing stake. Yet, to get the exact final
///   weight distribution from the winner's point of view, one needs to build a support map. See
///   [`crate::SupportMap`] for more info. Note that this backing stake is computed in
///   ExtendedBalance and may be slightly different that what will be computed from the support map,
///   due to accuracy loss.
///
/// This can only fail of the normalization fails. This can happen if for any of the resulting
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

	let mut winners_count = 0;
	let winners = candidates
		.into_iter()
		.take_while(|_| {
			winners_count += 1;
			winners_count <= to_elect
		})
        .map(|w| {
            w.borrow_mut().elected = true;
            w
        })
		.map(|w_ptr| (w_ptr.borrow().who.clone(), w_ptr.borrow().approval_stake))
		.collect();

    for voter in &mut voters {
        for edge in &mut voter.edges {
            if edge.candidate.borrow().elected {
                edge.weight = multiply_by_rational_with_rounding(
                    voter.budget,
                    edge.load.n(),
                    voter.load.n(),
                    Rounding::Down,
                ).unwrap_or(Bounded::max_value());
            } else {
                edge.weight = Zero::zero()
            }
        }
    }

	let mut assignments = voters
		.into_iter()
		.filter_map(|v| v.into_assignment())
		.collect::<Vec<_>>();
    let _ = assignments
		.iter_mut()
		.try_for_each(|a| a.try_normalize().map_err(crate::Error::ArithmeticError))?;

	Ok(ElectionResult { winners, assignments })
}
