// Copyright 2019-2020 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


//! Benchmarks of the phragmen election algorithm.
//! Note that execution times will not be accurate in an absolute scale, since
//! - Everything is executed in the context of `TestExternalities`
//! - Everything is executed in native environment.

#![cfg(feature = "bench")]
#![feature(test)]

extern crate test;
use test::Bencher;

use rand::{self, Rng};
use sp_npos_elections::{ElectionResult, VoteWeight};

use std::collections::BTreeMap;
use sp_runtime::{Perbill, PerThing, traits::Zero};
use sp_npos_elections::{
	balance_solution, assignment_ratio_to_staked, to_support_map, to_without_backing, VoteWeight,
	ExtendedBalance, Assignment, StakedAssignment, IdentifierT, assignment_ratio_to_staked,
	seq_phragmen,
};

// default params. Each will be scaled by the benchmarks individually.
const VALIDATORS: u64 = 100;
const NOMINATORS: u64 = 1_000;
const EDGES: u64 = 2;
const TO_ELECT: usize = 10;
const STAKE: VoteWeight = 1000;

const PREFIX: AccountId = 1000_000;

type AccountId = u64;

mod bench_closure_and_slice {
	use super::*;

	fn random_assignment() -> Assignment<u32, Perbill> {
		let mut rng = rand::thread_rng();
		let who = rng.next_u32();
		let distribution = (0..5)
			.map(|x| (x + rng.next_u32(), Perbill::from_percent(rng.next_u32() % 100)))
			.collect::<Vec<_>>();
		Assignment { who, distribution }
	}

	/// Converts a vector of ratio assignments into ones with absolute budget value.
	pub fn assignment_ratio_to_staked_slice<A: IdentifierT, P: PerThing>(
		ratio: Vec<Assignment<A, P>>,
		stakes: &[VoteWeight],
	) -> Vec<StakedAssignment<A>>
	where
		T: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	{
		ratio
			.into_iter()
			.zip(stakes.into_iter().map(|x| *x as ExtendedBalance))
			.map(|(a, stake)| {
				a.into_staked(stake.into(), true)
			})
			.collect()
	}

	#[bench]
	fn closure(b: &mut Bencher) {
		let assignments = (0..1000).map(|_| random_assignment()).collect::<Vec<Assignment<_ ,_>>>();
		let stake_of = |x: &u32| -> VoteWeight { (x * 2 + 100).into() };

		// each have one clone of assignments
		b.iter(|| assignment_ratio_to_staked(assignments.clone(), stake_of));
	}

	#[bench]
	fn slice(b: &mut Bencher) {
		let assignments = (0..1000).map(|_| random_assignment()).collect::<Vec<Assignment<_ ,_>>>();
		let stake_of = |x: &u32| -> VoteWeight { (x * 2 + 100).into() };

		b.iter(|| {
			let local = assignments.clone();
			let stakes = local.iter().map(|x| stake_of(&x.who)).collect::<Vec<_>>();
			assignment_ratio_to_staked_slice(local, stakes.as_ref());
		});
	}
}

fn do_phragmen(
	b: &mut Bencher,
	num_validators: u64,
	num_nominators: u64,
	to_elect: usize,
	edge_per_voter: u64,
	eq_iters: usize,
	eq_tolerance: u128,
) {
	assert!(num_validators > edge_per_voter);
	let rr = |a, b| rand::thread_rng().gen_range(a as usize, b as usize) as VoteWeight;

	let mut candidates = Vec::with_capacity(num_validators as usize);
	let mut stake_of_tree: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();

	(1 ..= num_validators).for_each(|acc| {
		candidates.push(acc);
		stake_of_tree.insert(acc, STAKE + rr(10, 1000));
	});

	let mut voters = Vec::with_capacity(num_nominators as usize);
	(PREFIX ..= (PREFIX + num_nominators)).for_each(|acc| {
		// all possible targets
		let mut all_targets = candidates.clone();
		// we remove and pop into `targets` `edge_per_voter` times.
		let targets = (0 .. edge_per_voter).map(|_| {
			all_targets.remove(rr(0, all_targets.len()) as usize)
		})
		.collect::<Vec<AccountId>>();

		let stake = STAKE + rr(10, 1000);
		stake_of_tree.insert(acc, stake);
		voters.push((acc, stake, targets));
	});

	b.iter(|| {
		let ElectionResult { winners, assignments } = seq_phragmen::<AccountId, Perbill>(
			to_elect,
			Zero::zero(),
			candidates.clone(),
			voters.clone(),
		).unwrap();

		let stake_of = |who: &AccountId| -> VoteWeight {
			*stake_of_tree.get(who).unwrap()
		};

		// Do the benchmarking with balancing.
		if eq_iters > 0 {
			let staked = assignment_ratio_to_staked(assignments, &stake_of);
			let winners = to_without_backing(winners);
			let mut support = to_support_map(
				winners.as_ref(),
				staked.as_ref(),
			).unwrap();

			balance_solution(
				staked.into_iter().map(|a| (a.clone(), stake_of(&a.who))).collect(),
				&mut support,
				eq_tolerance,
				eq_iters,
			);
		}
	})
}

macro_rules! phragmen_benches {
	($($name:ident: $tup:expr,)*) => {
	$(
		#[bench]
		fn $name(b: &mut Bencher) {
			let (v, n, t, e, eq_iter, eq_tol) = $tup;
			println!("----------------------");
			println!(
				"++ Benchmark: {} Validators // {} Nominators // {} Edges-per-nominator // {} \
				total edges // electing {} // Equalize: {} iterations -- {} tolerance",
				v, n, e, e * n, t, eq_iter, eq_tol,
			);
			do_phragmen(b, v, n, t, e, eq_iter, eq_tol);
		}
	)*
	}
}

phragmen_benches! {
	bench_1_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_2: (VALIDATORS * 2, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_3: (VALIDATORS * 4, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_4: (VALIDATORS * 8, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_2_eq: (VALIDATORS * 2, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_3_eq: (VALIDATORS * 4, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_4_eq: (VALIDATORS * 8, NOMINATORS, TO_ELECT, EDGES, 2, 0),

	bench_0_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_0_2: (VALIDATORS, NOMINATORS, TO_ELECT * 4, EDGES, 0, 0),
	bench_0_3: (VALIDATORS, NOMINATORS, TO_ELECT * 8, EDGES, 0, 0),
	bench_0_4: (VALIDATORS, NOMINATORS, TO_ELECT * 16, EDGES , 0, 0),
	bench_0_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_0_2_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 4, EDGES, 2, 0),
	bench_0_3_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 8, EDGES, 2, 0),
	bench_0_4_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 16, EDGES , 2, 0),

	bench_2_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_2_2: (VALIDATORS, NOMINATORS * 2, TO_ELECT, EDGES, 0, 0),
	bench_2_3: (VALIDATORS, NOMINATORS * 4, TO_ELECT, EDGES, 0, 0),
	bench_2_4: (VALIDATORS, NOMINATORS * 8, TO_ELECT, EDGES, 0, 0),
	bench_2_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_2_2_eq: (VALIDATORS, NOMINATORS * 2, TO_ELECT, EDGES, 2, 0),
	bench_2_3_eq: (VALIDATORS, NOMINATORS * 4, TO_ELECT, EDGES, 2, 0),
	bench_2_4_eq: (VALIDATORS, NOMINATORS * 8, TO_ELECT, EDGES, 2, 0),

	bench_3_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0 ),
	bench_3_2: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 2, 0, 0),
	bench_3_3: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 4, 0, 0),
	bench_3_4: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 8, 0, 0),
	bench_3_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_3_2_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 2, 2, 0),
	bench_3_3_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 4, 2, 0),
	bench_3_4_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES * 8, 2, 0),
}
