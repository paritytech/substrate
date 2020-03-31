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

//! Fuzzing fro the equalize algorithm
//!
//! It ensures that any solution which gets equalized will lead into a better or equally scored
//! one.

use honggfuzz::fuzz;
use sp_phragmen::{
	equalize, assignment_ratio_to_staked, build_support_map, to_without_backing, elect,
	PhragmenResult, VoteWeight, evaluate_support, is_score_better,
};
use sp_std::collections::btree_map::BTreeMap;
use sp_runtime::Perbill;
use rand::{self, Rng, SeedableRng, RngCore};

type AccountId = u64;

fn generate_random_phragmen_result(
	voter_count: u64,
	target_count: u64,
	to_elect: usize,
	edge_per_voter: u64,
	mut rng: impl RngCore,
) -> (PhragmenResult<AccountId, Perbill>, BTreeMap<AccountId, VoteWeight>) {
	let prefix = 100_000;
	let base_stake = 100_000;

	let mut candidates = Vec::with_capacity(target_count as usize);
	let mut stake_of_tree: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();

	(1..=target_count).for_each(|acc| {
		candidates.push(acc);
		let stake_var = rng.gen_range(10, 10000) as VoteWeight;
		stake_of_tree.insert(acc, base_stake + stake_var);
	});

	dbg!(&candidates);
	let mut voters = Vec::with_capacity(voter_count as usize);
	(prefix ..= (prefix + voter_count)).for_each(|acc| {
		// all possible targets
		let mut all_targets = candidates.clone();
		// we remove and pop into `targets` `edge_per_voter` times.
		let targets = (0..edge_per_voter).map(|_| {
			let upper = all_targets.len() - 1;
			let idx = rng.gen_range(0, upper);
			all_targets.remove(idx)
		})
		.collect::<Vec<AccountId>>();

		let stake_var = rng.gen_range(10, 10000) as VoteWeight;
		let stake = base_stake + stake_var;
		stake_of_tree.insert(acc, stake);
		voters.push((acc, stake, targets));
	});

	(
		elect::<AccountId, sp_runtime::Perbill>(
			to_elect,
			0,
			candidates,
			voters,
		).unwrap(),
		stake_of_tree,
	)
}

fn main() {
	let to_range = |x: usize, a: usize, b: usize| ((x % b).saturating_add(a));
	loop {
		fuzz!(|data: (usize, usize, usize, usize, u64)| {
			let (mut target_count, mut voter_count, mut iterations, mut to_elect, seed) = data;
			let rng = rand::rngs::SmallRng::seed_from_u64(seed);
			target_count = to_range(target_count, 50, 1000);
			voter_count = to_range(voter_count, 50, 2000);
			iterations = to_range(iterations, 1, 20);
			to_elect = to_range(to_elect, 50, target_count);

			println!("++ [{} / {} / {} / {}]", target_count, voter_count, to_elect, iterations);
			let (PhragmenResult { winners, assignments }, stake_of_tree) = generate_random_phragmen_result(
				voter_count as u64,
				target_count as u64,
				to_elect,
				8,
				rng,
			);

			let stake_of = |who: &AccountId| -> VoteWeight {
				*stake_of_tree.get(who).unwrap()
			};

			let staked = assignment_ratio_to_staked(assignments.clone(), &stake_of);
			let winners = to_without_backing(winners);
			let mut support = build_support_map(winners.as_ref(), staked.as_ref()).0;

			println!("Initial support = {:?}", support);
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

			println!("Equalized support = {:?}", support);
			let final_score = evaluate_support(&support);
			let enhance = is_score_better(initial_score, final_score);

			println!(
				"iter = {} // {:?} -> {:?} [{}]",
				i,
				initial_score,
				final_score,
				enhance,
			);
			// if more than one iteration has been done, or they must be equal.
			assert!(enhance || initial_score == final_score || i == 0)
		});
	}
}
