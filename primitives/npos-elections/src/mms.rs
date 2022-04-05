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
//! This is explained a bit further in issue <https://github.com/paritytech/substrate/issues/6639>
//!
//! This is also further explained in [The Maximin Support Method: An Extension of the D'Hondt Method to Approval-Based Multiwinner Elections](https://arxiv.org/abs/1609.05370).

use crate::{
	balance, setup_inputs, Assignment, ElectionResult, ExtendedBalance, IdentifierT, PerThing128,
	VoteWeight,
};
use core::ops::Add;

/// Execute the mms method.
///
/// This can be used interchangeably with [`seq-phragmen`] or [`phragmms`] and offers a similar API,
/// namely:
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
/// This can only fail of the normalization fails. This can happen if for any of the resulting
/// assignments, `assignment.distribution.map(|p| p.deconstruct()).sum()` fails to fit inside
/// `UpperOf<P>`. A user of this crate may statically assert that this can never happen and safely
/// `expect` this to return `Ok`.
pub fn mms<AccountId: IdentifierT, P: PerThing128 + Add<Output = P>>(
	to_elect: usize,
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	iterations: usize,
	tolerance: ExtendedBalance,
) -> Result<ElectionResult<AccountId, P>, crate::Error> {
	let mut winners = vec![];
	for _round in 0..to_elect {
		let mut max_support = P::zero();
		let mut winner;
		for candidate in &candidates {
			let mut augmented_winners = winners.clone();
			augmented_winners.push(candidate);
			let (_, mut used_voters) = setup_inputs(augmented_winners, voters);
			let mut support = P::zero();
			balance(&mut used_voters, iterations, tolerance);
			for Assignment { who, distribution } in
				used_voters.into_iter().filter_map(|v| v.into_assignment::<P>())
			{
				for (c, weight_extended) in distribution.into_iter() {
					if c == candidate {
						support = support.add(weight_extended);
					}
				}
			}

			if support > max_support {
				max_support = support;
				winner = candidate;
			}
		}

		if !max_support.is_zero() {
			winners.push(winner);
		}
	}
	Err(crate::Error::SolutionWeightOverflow)
}
