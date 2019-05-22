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

use test::Bencher;
use runtime_io::with_externalities;
use mock::*;
use super::*;

fn do_phragmen(num_vals: u64, num_noms: u64, count: usize, votes_per: u64) {
	with_externalities(&mut ExtBuilder::default().build(), || {
		// prefix to distinguish the validator and nominator account ranges.
		let np = 10_000;
		(1..=2*num_vals)
			.step_by(2)
			.for_each(|acc| bond_validator(acc, 100));

		// TODO: properly feed `votes_per` random votes to each created nominator.
		(np..=(np + 2*num_noms))
			.step_by(2)
			.for_each(|acc| {
				bond_nominator(acc, 100, vec![1]);
			});

		let _ = phragmen::elect::<Test, _, _, _>(
			count,
			Staking::minimum_validator_count() as usize,
			<Validators<Test>>::enumerate(),
			<Nominators<Test>>::enumerate(),
			Staking::slashable_balance_of,
		);
	})
}

#[bench]
fn bench_phragmen_10_vals(b: &mut Bencher) {
	b.iter(|| do_phragmen(10, 100, 10, 1));
}

#[bench]
fn bench_phragmen_100_vals(b: &mut Bencher) {
	b.iter(|| do_phragmen(100, 100, 10, 1));
}

#[bench]
fn bench_phragmen_1000_vals(b: &mut Bencher) {
	b.iter(|| do_phragmen(1000, 100, 10, 1));
}

#[bench]
fn bench_phragmen_2000_vals(b: &mut Bencher) {
	b.iter(|| do_phragmen(2000, 100, 10, 1));
}

#[bench]
fn bench_phragmen_4000_vals(b: &mut Bencher) {
	b.iter(|| do_phragmen(4000, 100, 10, 1));
}
