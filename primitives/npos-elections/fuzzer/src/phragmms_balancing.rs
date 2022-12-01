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

//! Fuzzing for phragmms.

mod common;

use common::*;
use honggfuzz::fuzz;
use rand::{self, SeedableRng};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, is_score_better, phragmms, to_supports, EvaluateSupport,
	VoteWeight,
};
use sp_runtime::Perbill;

fn main() {
	loop {
		fuzz!(|data: (usize, usize, usize, usize, u64)| {
			let (mut target_count, mut voter_count, mut iterations, mut to_elect, seed) = data;
			let rng = rand::rngs::SmallRng::seed_from_u64(seed);
			target_count = to_range(target_count, 100, 200);
			voter_count = to_range(voter_count, 100, 200);
			iterations = to_range(iterations, 5, 30);
			to_elect = to_range(to_elect, 25, target_count);

			println!(
				"++ [voter_count: {} / target_count:{} / to_elect:{} / iterations:{}]",
				voter_count, target_count, to_elect, iterations,
			);
			let (unbalanced, candidates, voters, stake_of_tree) = generate_random_npos_result(
				voter_count as u64,
				target_count as u64,
				to_elect,
				rng,
				ElectionType::Phragmms(None),
			);

			let stake_of = |who: &AccountId| -> VoteWeight { *stake_of_tree.get(who).unwrap() };

			let unbalanced_score = {
				let staked = assignment_ratio_to_staked_normalized(
					unbalanced.assignments.clone(),
					&stake_of,
				)
				.unwrap();
				let score = to_supports(&staked).evaluate();

				if score[0] == 0 {
					// such cases cannot be improved by balancing.
					return
				}
				score
			};

			let balanced = phragmms::<AccountId, sp_runtime::Perbill>(
				to_elect,
				candidates,
				voters,
				Some((iterations, 0)),
			)
			.unwrap();

			let balanced_score = {
				let staked =
					assignment_ratio_to_staked_normalized(balanced.assignments.clone(), &stake_of)
						.unwrap();
				to_supports(staked.as_ref()).evaluate()
			};

			let enhance = is_score_better(balanced_score, unbalanced_score, Perbill::zero());

			println!(
				"iter = {} // {:?} -> {:?} [{}]",
				iterations, unbalanced_score, balanced_score, enhance,
			);

			// The only guarantee of balancing is such that the first and third element of the score
			// cannot decrease.
			assert!(
				balanced_score[0] >= unbalanced_score[0] &&
					balanced_score[1] == unbalanced_score[1] &&
					balanced_score[2] <= unbalanced_score[2]
			);
		});
	}
}
