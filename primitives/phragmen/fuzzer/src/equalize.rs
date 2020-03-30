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

//! Fuzzing fro the equalize algorithm.

use honggfuzz::fuzz;
use sp_phragmen::{
	equalize, assignment_ratio_to_staked, build_support_map, to_without_backing, elect,
	PhragmenResult, VoteWeight, evaluate_support, is_score_better,
};
use sp_std::collections::btree_map::BTreeMap;
use sp_runtime::Perbill;
use rand::{self, Rng};

fn rr(a: usize, b: usize) -> usize {
	rand::thread_rng().gen_range(a, b)
}

fn generate_random_phragmen_result(
	num_targets: u64,
	num_voters: u64,
	to_elect: usize,
	edge_per_voter: u64,
) -> (PhragmenResult<u64, Perbill>, BTreeMap<u64, VoteWeight>) {
	let prefix = 100_000;
	let base_stake = 100_000;

	let mut candidates = Vec::with_capacity(num_targets as usize);
	let mut stake_of_tree: BTreeMap<u64, VoteWeight> = BTreeMap::new();

	(1 ..= num_targets).for_each(|acc| {
		candidates.push(acc);
		let stake_var = rr(10, 10000) as VoteWeight;
		stake_of_tree.insert(acc, base_stake + stake_var);
	});

	let mut voters = Vec::with_capacity(num_voters as usize);
	(prefix ..= (prefix + num_voters)).for_each(|acc| {
		// all possible targets
		let mut all_targets = candidates.clone();
		// we remove and pop into `targets` `edge_per_voter` times.
		let targets = (0..edge_per_voter).map(|_| {
			let upper = all_targets.len() - 1;
			let idx = rr(0, upper);
			all_targets.remove(idx)
		})
		.collect::<Vec<u64>>();

		let stake_var = rr(10, 1000) as VoteWeight;
		let stake = base_stake + stake_var;
		stake_of_tree.insert(acc, stake);
		voters.push((acc, stake, targets));
	});

	(
		elect::<u64, sp_runtime::Perbill>(
			to_elect,
			0,
			candidates,
			voters,
		).unwrap(),
		stake_of_tree,
	)
}

fn main() {
	fuzz!(|_data: (u64, u64, u64, u64)| {
		// let (num_targets, num_voters, iterations, to_elect) = data;
		// if iterations > 20 || to_elect > num_targets || num_targets > num_voters {
		// 		return
		// }
		let num_targets = rr(50, 1000);
		let iterations = rr(1, 20);
		let num_voters = rr(50, 2000);
		let to_elect = rr(50, num_targets);
		let (PhragmenResult { winners, assignments }, stake_of_tree) = generate_random_phragmen_result(
			num_targets as u64,
			num_voters as u64,
			to_elect,
			8,
		);

		let stake_of = |who: &u64| -> VoteWeight {
			*stake_of_tree.get(who).unwrap()
		};

		let staked = assignment_ratio_to_staked(assignments.clone(), &stake_of);
		let winners = to_without_backing(winners);
		let mut support = build_support_map(winners.as_ref(), staked.as_ref()).0;

		let initial_score = evaluate_support(&support);
		if initial_score[0] == 0 {
			// such cases cannot be improved by reduce.
			return;
		}

		let i = equalize(
			staked.into_iter().map(|a| (a.clone(), stake_of(&a.who))).collect(),
			&mut support,
			10,
			iterations,
		);
		let final_score = evaluate_support(&support);
		let enhance = is_score_better(initial_score, final_score);
		println!("++ [{} / {} / {}] i = {} // {:?} -> {:?} [{}]", num_voters, num_targets, to_elect, i, initial_score, final_score, enhance);
		// if more than one iteration has been done, it must enhance the score.
		assert!(enhance || i == 0)
	});
}
