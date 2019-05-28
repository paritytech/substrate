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
//!
//! Run using:
//!
//! ```zsh
//!  cargo bench --features bench --color always
//! ```

use test::Bencher;
use runtime_io::with_externalities;
use mock::*;
use super::*;
use rand::{self, Rng};

const VALIDATORS: u64 = 1000;
const NOMINATORS: u64 = 10_000;
const EDGES: u64 = 2;
const TO_ELECT: usize = 100;
const STAKE: u64 = 1000;

fn do_phragmen(b: &mut Bencher, num_vals: u64, num_noms: u64, count: usize, votes_per: u64) {
	with_externalities(&mut ExtBuilder::default().nominate(false).build(), || {
		assert!(num_vals > votes_per);
		let rr = |a, b| rand::thread_rng().gen_range(a as usize, b as usize) as u64;

		// prefix to distinguish the validator and nominator account ranges.
		let np = 10_000;

		(1 ..= 2*num_vals)
			.step_by(2)
			.for_each(|acc| bond_validator(acc, STAKE + rr(10, 50)));

		(np ..= (np + 2*num_noms))
			.step_by(2)
			.for_each(|acc| {
				let mut stashes_to_vote = (1 ..= 2*num_vals)
					.step_by(2)
					.map(|ctrl| ctrl + 1)
					.collect::<Vec<AccountIdType>>();
				let votes = (0 .. votes_per)
					.map(|_| {
						stashes_to_vote.remove(rr(0, stashes_to_vote.len()) as usize)
					})
					.collect::<Vec<AccountIdType>>();
				bond_nominator(acc, STAKE + rr(10, 50), votes);
			});

		b.iter(|| {
			let _ = phragmen::elect::<Test, _, _, _>(
				count,
				1_usize,
				<Validators<Test>>::enumerate(),
				<Nominators<Test>>::enumerate(),
				Staking::slashable_balance_of
			);
		})
	})
}

macro_rules! phragmen_benches {
	($($name:ident: $tup:expr,)*) => {
    $(
        #[bench]
        fn $name(b: &mut Bencher) {
			let (v, n, t, e) = $tup;
			println!("");
			println!(
				"++ Benchmark: {} Validators // {} Nominators // {} Edges-per-nominator // {} total edges // electing {}",
				v, n, e, e * n, t
			);
			do_phragmen(b, v, n, t, e);
        }
    )*
	}
}

phragmen_benches! {
	bench_1_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES),
	bench_1_2: (VALIDATORS*2, NOMINATORS, TO_ELECT, EDGES),
	bench_1_3: (VALIDATORS*4, NOMINATORS, TO_ELECT, EDGES),
	bench_1_4: (VALIDATORS*8, NOMINATORS, TO_ELECT, EDGES),

	bench_0_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES),
	bench_0_2: (VALIDATORS, NOMINATORS, TO_ELECT * 4, EDGES),
	bench_0_3: (VALIDATORS, NOMINATORS, TO_ELECT * 8, EDGES),
	bench_0_4: (VALIDATORS, NOMINATORS, TO_ELECT * 16, EDGES),

	bench_2_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES),
	bench_2_2: (VALIDATORS, NOMINATORS*2, TO_ELECT, EDGES),
	bench_2_3: (VALIDATORS, NOMINATORS*4, TO_ELECT, EDGES),
	bench_2_4: (VALIDATORS, NOMINATORS*8, TO_ELECT, EDGES),

	bench_3_1: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES),
	bench_3_2: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*2),
	bench_3_3: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*4),
	bench_3_4: (VALIDATORS, NOMINATORS, TO_ELECT, EDGES*8),
}
