// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Running
//!
//! Run with `cargo hfuzz run reduce`. `honggfuzz`.
//!
//! # Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug reduce hfuzz_workspace/reduce/*.fuzz`.

use honggfuzz::fuzz;
use sp_phragmen::{StakedAssignment, ExtendedBalance, build_support_map, reduce};
use rand::{self, Rng};

type Balance = u128;
type AccountId = u64;

/// Or any other token type.
const KSM: Balance = 1_000_000_000_000;

fn main() {
	loop {
		fuzz!(|_data: _| {
	 		let (assignments, winners) = generate_random_phragmen_assignment(
	 			rr(100, 1000),
	 			rr(100, 2000),
	 			10,
	 			6,
	 		);
			reduce_and_compare(&assignments, &winners);
	 	});
	}
}

fn generate_random_phragmen_assignment(
	voter_count: usize,
	target_count: usize,
	avg_edge_per_voter: usize,
	edge_per_voter_var: usize,
) -> (Vec<StakedAssignment<AccountId>>, Vec<AccountId>) {
	// random in range of (a, b)
	let rr_128 = |a: u128, b: u128| -> u128 { rand::thread_rng().gen_range(a, b) };

	// prefix to distinguish the voter and target account ranges.
	let target_prefix = 1_000_000;
	// let target_prefix = 1000;
	assert!(voter_count < target_prefix);

	let mut assignments = Vec::with_capacity(voter_count as usize);
	let mut winners: Vec<AccountId> = Vec::new();

	let all_targets = (target_prefix..(target_prefix + target_count))
		.map(|a| a as AccountId)
		.collect::<Vec<AccountId>>();

	(1..=voter_count).for_each(|acc| {
		let mut targets_to_chose_from = all_targets.clone();
		let targets_to_chose = if edge_per_voter_var > 0 { rr(
			avg_edge_per_voter - edge_per_voter_var,
			avg_edge_per_voter + edge_per_voter_var,
		) } else { avg_edge_per_voter };

		let distribution = (0..targets_to_chose).map(|_| {
			let target = targets_to_chose_from.remove(rr(0, targets_to_chose_from.len()));
			if winners.iter().find(|w| **w == target).is_none() {
				winners.push(target.clone());
			}
			(target, rr_128(1 * KSM, 100 * KSM))
		}).collect::<Vec<(AccountId, ExtendedBalance)>>();

		assignments.push(StakedAssignment {
			who: (acc as AccountId),
			distribution,
		});
	});

	(assignments, winners)
}

fn assert_assignments_equal(
	winners: &Vec<AccountId>,
	ass1: &Vec<StakedAssignment<AccountId>>,
	ass2: &Vec<StakedAssignment<AccountId>>,
) {

	let (support_1, _) = build_support_map::<AccountId>(winners, ass1);
	let (support_2, _) = build_support_map::<AccountId>(winners, ass2);

	for (who, support) in support_1.iter() {
		assert_eq!(support.total, support_2.get(who).unwrap().total);
	}
}

fn reduce_and_compare(
	assignment: &Vec<StakedAssignment<AccountId>>,
	winners: &Vec<AccountId>,
) {
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

	assert_assignments_equal(
		winners,
		&assignment,
		&altered_assignment,
	);
}

fn assignment_len(assignments: &[StakedAssignment<AccountId>]) -> u32 {
	let mut counter = 0;
	assignments.iter().for_each(|x| x.distribution.iter().for_each(|_| counter += 1));
	counter
}

fn rr(a: usize, b: usize) -> usize {
	rand::thread_rng().gen_range(a, b)
}
