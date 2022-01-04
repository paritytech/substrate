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

//! Fuzzing for the reduce algorithm.
//!
//! It that reduce always return a new set og edges in which the bound is kept (`edges_after <= m +
//! n,`) and the result must effectively be the same, meaning that the same support map should be
//! computable from both.
//!
//! # Running
//!
//! Run with `cargo hfuzz run reduce`. `honggfuzz`.
//!
//! # Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug reduce hfuzz_workspace/reduce/*.fuzz`.

use honggfuzz::fuzz;

mod common;
use common::to_range;
use rand::{self, Rng, RngCore, SeedableRng};
use sp_npos_elections::{reduce, to_support_map, ExtendedBalance, StakedAssignment};

type Balance = u128;
type AccountId = u64;

/// Or any other token type.
const KSM: Balance = 1_000_000_000_000;

fn main() {
	loop {
		fuzz!(|data: (usize, usize, u64)| {
			let (mut voter_count, mut target_count, seed) = data;
			let rng = rand::rngs::SmallRng::seed_from_u64(seed);
			target_count = to_range(target_count, 100, 1000);
			voter_count = to_range(voter_count, 100, 2000);
			let (assignments, winners) =
				generate_random_phragmen_assignment(voter_count, target_count, 8, 8, rng);
			reduce_and_compare(&assignments, &winners);
		});
	}
}

fn generate_random_phragmen_assignment(
	voter_count: usize,
	target_count: usize,
	avg_edge_per_voter: usize,
	edge_per_voter_var: usize,
	mut rng: impl RngCore,
) -> (Vec<StakedAssignment<AccountId>>, Vec<AccountId>) {
	// prefix to distinguish the voter and target account ranges.
	let target_prefix = 1_000_000;
	assert!(voter_count < target_prefix);

	let mut assignments = Vec::with_capacity(voter_count as usize);
	let mut winners: Vec<AccountId> = Vec::new();

	let all_targets = (target_prefix..(target_prefix + target_count))
		.map(|a| a as AccountId)
		.collect::<Vec<AccountId>>();

	(1..=voter_count).for_each(|acc| {
		let mut targets_to_chose_from = all_targets.clone();
		let targets_to_chose = if edge_per_voter_var > 0 {
			rng.gen_range(
				avg_edge_per_voter - edge_per_voter_var,
				avg_edge_per_voter + edge_per_voter_var,
			)
		} else {
			avg_edge_per_voter
		};

		let distribution = (0..targets_to_chose)
			.map(|_| {
				let target =
					targets_to_chose_from.remove(rng.gen_range(0, targets_to_chose_from.len()));
				if winners.iter().find(|w| **w == target).is_none() {
					winners.push(target.clone());
				}
				(target, rng.gen_range(1 * KSM, 100 * KSM))
			})
			.collect::<Vec<(AccountId, ExtendedBalance)>>();

		assignments.push(StakedAssignment { who: (acc as AccountId), distribution });
	});

	(assignments, winners)
}

fn assert_assignments_equal(
	ass1: &Vec<StakedAssignment<AccountId>>,
	ass2: &Vec<StakedAssignment<AccountId>>,
) {
	let support_1 = to_support_map::<AccountId>(ass1);
	let support_2 = to_support_map::<AccountId>(ass2);
	for (who, support) in support_1.iter() {
		assert_eq!(support.total, support_2.get(who).unwrap().total);
	}
}

fn reduce_and_compare(assignment: &Vec<StakedAssignment<AccountId>>, winners: &Vec<AccountId>) {
	let mut altered_assignment = assignment.clone();
	let n = assignment.len() as u32;
	let m = winners.len() as u32;

	let edges_before = assignment_len(&assignment);
	let num_changed = reduce(&mut altered_assignment);
	let edges_after = edges_before - num_changed;

	assert!(
		edges_after <= m + n,
		"reduce bound not satisfied. n = {}, m = {}, edges after reduce = {} (removed {})",
		n,
		m,
		edges_after,
		num_changed,
	);

	assert_assignments_equal(&assignment, &altered_assignment);
}

fn assignment_len(assignments: &[StakedAssignment<AccountId>]) -> u32 {
	let mut counter = 0;
	assignments
		.iter()
		.for_each(|x| x.distribution.iter().for_each(|_| counter += 1));
	counter
}
