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
	Rc, VoteWeight,
};

/// Execute the `MMS` method.
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
pub fn mms<AccountId: IdentifierT + Default, P: PerThing128>(
	to_elect: usize,
	candidates: Vec<AccountId>,
	voters: Vec<(AccountId, VoteWeight, impl IntoIterator<Item = AccountId>)>,
	iterations: usize,
	tolerance: ExtendedBalance,
) -> Result<ElectionResult<AccountId, P>, crate::Error> {
	let mut winners: Vec<CandidatePtr<AccountId>> = vec![]; // `A` in the paper.
	let (candidates, mut voters) = setup_inputs(candidates, voters);

	for round in 0..to_elect {
		let mut bal: ExtendedBalance = 0;
		let mut winner: CandidatePtr<AccountId> = Default::default();
		for candidate in &candidates {
			if winners.iter().any(|w| w.borrow().who == candidate.borrow().who) {
				// `c in C \ A` in the paper.
				continue
			}

			candidate.borrow_mut().elected = true;
			candidate.borrow_mut().round = round;

			// Calculate the balance weight vector `w_c` for `A + c`
			balance(&mut voters, iterations, tolerance);

			// Find `argmax_{c in C\A} supp_{w_c}(A+c)`
			let support = candidate.borrow().backed_stake;

			// maximize stake
			if support >= bal {
				bal = support;
				winner = Rc::clone(candidate);
			}

			candidate.borrow_mut().elected = false;
			candidate.borrow_mut().round = 0;
		}

		// winner is always initialized in the previous loop. We have a winner!
		winner.borrow_mut().elected = true;
		winner.borrow_mut().round = round;
		winners.push(winner);
	}

	// Make sure weights are correct and normalized.
	balance(&mut voters, iterations, tolerance);

	crate::voter_candidate_to_election_result(voters, winners)
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
		assert_eq!(winners, vec![(3, 30), (2, 30)]);
		assert_eq!(
			assignments,
			vec![
				Assignment {
					who: 10u64,
					distribution: vec![
						(1, Perbill::from_parts(500000000)),
						(2, Perbill::from_parts(500000000))
					]
				},
				Assignment {
					who: 20,
					distribution: vec![
						(1, Perbill::from_parts(500000000)),
						(3, Perbill::from_parts(500000000))
					]
				},
				Assignment {
					who: 30,
					distribution: vec![
						(2, Perbill::from_parts(666666666)),
						(3, Perbill::from_parts(333333334)),
					]
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

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(4, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners, vec![(11, 2000), (61, 2000), (41, 2000), (21, 2000),]);
	}

	#[test]
	fn large_balance_wont_overflow() {
		let candidates = vec![1u32, 2, 3];
		let mut voters = (0..1000).map(|i| (10 + i, u64::MAX, vec![1, 2, 3])).collect::<Vec<_>>();

		// give a bit more to 1 and 3.
		voters.push((2, u64::MAX, vec![1, 3]));

		let ElectionResult::<_, Perbill> { winners, assignments: _ } =
			mms(2, candidates, voters, 2, 0).unwrap();
		assert_eq!(winners.into_iter().map(|(w, _)| w).collect::<Vec<_>>(), vec![3u32, 1]);
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
}
