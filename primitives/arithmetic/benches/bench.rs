// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::Rng;
use sp_arithmetic::biguint::{BigUint, Single};

fn random_big_uint(size: usize) -> BigUint {
	let mut rng = rand::thread_rng();
	let digits: Vec<_> = (0..size).map(|_| rng.gen_range(0, Single::max_value())).collect();
	BigUint::from_limbs(&digits)
}

fn bench_op<F: Fn(&BigUint, &BigUint)>(c: &mut Criterion, name: &str, op: F) {
	let mut group = c.benchmark_group(name);

	for size in [2, 4, 6, 8, 10].iter() {
		group.throughput(Throughput::Elements(*size));
		group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
			let a = random_big_uint(size as usize);
			let b = random_big_uint(size as usize);

			bencher.iter(|| op(&a, &b));
		});
	}
}

fn bench_addition(c: &mut Criterion) {
	bench_op(c, "addition", |a, b| {
		let _ = a.clone().add(&b);
	});
}

fn bench_subtraction(c: &mut Criterion) {
	bench_op(c, "subtraction", |a, b| {
		let _ = a.clone().sub(&b);
	});
}

fn bench_multiplication(c: &mut Criterion) {
	bench_op(c, "multiplication", |a, b| {
		let _ = a.clone().mul(&b);
	});
}

fn bench_division(c: &mut Criterion) {
	let mut group = c.benchmark_group("division");

	for size in [4, 6, 8, 10].iter() {
		group.throughput(Throughput::Elements(*size));
		group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
			let a = random_big_uint(size as usize);
			let b = random_big_uint(rand::thread_rng().gen_range(2, size as usize));

			bencher.iter(|| {
				let _ = a.clone().div(&b, true);
			});
		});
	}
}

criterion_group! {
	name = benches;
	config = Criterion::default();
	targets = bench_addition, bench_subtraction, bench_multiplication, bench_division
}
criterion_main!(benches);
