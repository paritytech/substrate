// Copyright 2019 Parity Technologies
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
extern crate substrate_phragmen as phragmen;
use phragmen::{Support, SupportMap, PhragmenStakedAssignment};

use std::collections::BTreeMap;
use sr_primitives::traits::{Convert, SaturatedConversion};

const VALIDATORS: u64 = 1000;
const NOMINATORS: u64 = 10_000;
const EDGES: u64 = 2;
const TO_ELECT: usize = 100;
const STAKE: Balance = 1000;

type Balance = u128;
type AccountId = u64;

pub struct TestCurrencyToVote;
impl Convert<Balance, u64> for TestCurrencyToVote {
	fn convert(x: Balance) -> u64 { x.saturated_into() }
}
impl Convert<u128, Balance> for TestCurrencyToVote {
	fn convert(x: u128) -> Balance { x.saturated_into() }
}

fn do_phragmen(
	b: &mut Bencher,
	num_vals: u64,
	num_noms: u64,
	count: usize,
	votes_per: u64,
	eq_iters: usize,
	_eq_tolerance: u128,
) {
	assert!(num_vals > votes_per);
	let rr = |a, b| rand::thread_rng().gen_range(a as usize, b as usize) as Balance;

	// prefix to distinguish the validator and nominator account ranges.
	let np = 10_000;

	let mut candidates = Vec::with_capacity(num_vals as usize);
	let mut slashable_balance_of: BTreeMap<AccountId, Balance> = BTreeMap::new();

	(1 ..= num_vals)
		.for_each(|acc| {
			candidates.push(acc);
			slashable_balance_of.insert(acc, STAKE + rr(10, 50));
		});

	let mut voters = Vec::with_capacity(num_noms as usize);
	(np ..= (np + num_noms))
		.for_each(|acc| {
			let mut stashes_to_vote = candidates.clone();
			let votes = (0 .. votes_per)
				.map(|_| {
					stashes_to_vote.remove(rr(0, stashes_to_vote.len()) as usize)
				})
				.collect::<Vec<AccountId>>();
			voters.push((acc, votes));
			slashable_balance_of.insert(acc, STAKE + rr(10, 50));
		});

	let slashable_balance = |who: &AccountId| -> Balance {
		*slashable_balance_of.get(who).unwrap()
	};

	b.iter(|| {
		let r = phragmen::elect::<AccountId, Balance, _, TestCurrencyToVote>(
			count,
			1_usize,
			candidates.clone(),
			voters.clone(),
			slashable_balance,
			true,
		).unwrap();

		// Do the benchmarking with equalize.
		if eq_iters > 0 {
			let elected_stashes = r.winners;
			let assignments = r.assignments;

			let to_votes = |b: Balance|
				<TestCurrencyToVote as Convert<Balance, u128>>::convert(b) as u128;

			// Initialize the support of each candidate.
			let mut supports = <SupportMap<u64>>::new();
			elected_stashes
				.iter()
				.map(|(e, _)| (e, to_votes(slashable_balance(e))))
				.for_each(|(e, s)| {
					let item = Support { own: s, total: s, ..Default::default() };
					supports.insert(e.clone(), item);
				});

			// build support struct.
			for (n, assignment) in assignments.iter() {
				for (c, per_thing) in assignment.iter() {
					let nominator_stake = to_votes(slashable_balance(n));
					let other_stake = *per_thing * nominator_stake;
					if let Some(support) = supports.get_mut(c) {
						support.total = support.total.saturating_add(other_stake);
						support.others.push((n.clone(), other_stake));
					}
				}
			}

			let mut staked_assignments
				: Vec<(AccountId, Vec<PhragmenStakedAssignment<AccountId>>)>
				= Vec::with_capacity(assignments.len());
			for (n, assignment) in assignments.iter() {
				let mut staked_assignment
					: Vec<PhragmenStakedAssignment<AccountId>>
					= Vec::with_capacity(assignment.len());
				for (c, per_thing) in assignment.iter() {
					let nominator_stake = to_votes(slashable_balance(n));
					let other_stake = *per_thing * nominator_stake;
					staked_assignment.push((c.clone(), other_stake));
				}
				staked_assignments.push((n.clone(), staked_assignment));
			}

			let tolerance = 0_u128;
			let iterations = 2_usize;
			phragmen::equalize::<_, _, TestCurrencyToVote, _>(
				staked_assignments,
				&mut supports,
				tolerance,
				iterations,
				slashable_balance,
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
	bench_1_2: (VALIDATORS*2, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_3: (VALIDATORS*4, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_4: (VALIDATORS*8, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_1_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_2_eq: (VALIDATORS*2, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_3_eq: (VALIDATORS*4, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_1_4_eq: (VALIDATORS*8, NOMINATORS, TO_ELECT, EDGES, 2, 0),

	bench_0_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_0_2: (VALIDATORS, NOMINATORS, TO_ELECT * 4, EDGES, 0, 0),
	bench_0_3: (VALIDATORS, NOMINATORS, TO_ELECT * 8, EDGES, 0, 0),
	bench_0_4: (VALIDATORS, NOMINATORS, TO_ELECT * 16, EDGES , 0, 0),
	bench_0_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_0_2_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 4, EDGES, 2, 0),
	bench_0_3_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 8, EDGES, 2, 0),
	bench_0_4_eq: (VALIDATORS, NOMINATORS, TO_ELECT * 16, EDGES , 2, 0),

	bench_2_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0),
	bench_2_2: (VALIDATORS, NOMINATORS*2, TO_ELECT, EDGES, 0, 0),
	bench_2_3: (VALIDATORS, NOMINATORS*4, TO_ELECT, EDGES, 0, 0),
	bench_2_4: (VALIDATORS, NOMINATORS*8, TO_ELECT, EDGES, 0, 0),
	bench_2_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_2_2_eq: (VALIDATORS, NOMINATORS*2, TO_ELECT, EDGES, 2, 0),
	bench_2_3_eq: (VALIDATORS, NOMINATORS*4, TO_ELECT, EDGES, 2, 0),
	bench_2_4_eq: (VALIDATORS, NOMINATORS*8, TO_ELECT, EDGES, 2, 0),

	bench_3_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 0, 0 ),
	bench_3_2: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*2, 0, 0),
	bench_3_3: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*4, 0, 0),
	bench_3_4: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*8, 0, 0),
	bench_3_1_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES, 2, 0),
	bench_3_2_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*2, 2, 0),
	bench_3_3_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*4, 2, 0),
	bench_3_4_eq: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*8, 2, 0),
}
