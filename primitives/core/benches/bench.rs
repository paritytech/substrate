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

#[macro_use]
extern crate criterion;

use criterion::{black_box, Bencher, BenchmarkId, Criterion};
use sp_core::{
	crypto::Pair as _,
	hashing::{blake2_128, twox_128},
};

const MAX_KEY_SIZE: u32 = 32;

fn get_key(key_size: u32) -> Vec<u8> {
	use rand::{Rng, SeedableRng};

	let rnd: [u8; 32] = rand::rngs::StdRng::seed_from_u64(12).gen();
	let mut rnd = rnd.iter().cycle();

	(0..key_size).map(|_| *rnd.next().unwrap()).collect()
}

fn bench_blake2_128(b: &mut Bencher, key: &Vec<u8>) {
	b.iter(|| {
		let _a = blake2_128(black_box(key));
	});
}

fn bench_twox_128(b: &mut Bencher, key: &Vec<u8>) {
	b.iter(|| {
		let _a = twox_128(black_box(key));
	});
}

fn bench_hash_128_fix_size(c: &mut Criterion) {
	let mut group = c.benchmark_group("fix size hashing");

	let key = get_key(MAX_KEY_SIZE);

	group.bench_with_input("blake2_128", &key, bench_blake2_128);
	group.bench_with_input("twox_128", &key, bench_twox_128);

	group.finish();
}

fn bench_hash_128_dyn_size(c: &mut Criterion) {
	let mut group = c.benchmark_group("dyn size hashing");

	for i in (2..MAX_KEY_SIZE).step_by(4) {
		let key = get_key(i);

		group.bench_with_input(
			BenchmarkId::new("blake2_128", format!("{}", i)),
			&key,
			bench_blake2_128,
		);
		group.bench_with_input(
			BenchmarkId::new("twox_128", format!("{}", i)),
			&key,
			bench_twox_128,
		);
	}

	group.finish();
}

fn bench_ed25519(c: &mut Criterion) {
	let mut group = c.benchmark_group("ed25519");

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::ed25519::Pair::generate().0;
		group.bench_function(BenchmarkId::new("signing", format!("{}", msg_size)), |b| {
			b.iter(|| key.sign(&msg))
		});
	}

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::ed25519::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		group.bench_function(BenchmarkId::new("verifying", format!("{}", msg_size)), |b| {
			b.iter(|| sp_core::ed25519::Pair::verify(&sig, &msg, &public))
		});
	}

	group.finish();
}

fn bench_sr25519(c: &mut Criterion) {
	let mut group = c.benchmark_group("sr25519");

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::sr25519::Pair::generate().0;
		group.bench_function(BenchmarkId::new("signing", format!("{}", msg_size)), |b| {
			b.iter(|| key.sign(&msg))
		});
	}

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::sr25519::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		group.bench_function(BenchmarkId::new("verifying", format!("{}", msg_size)), |b| {
			b.iter(|| sp_core::sr25519::Pair::verify(&sig, &msg, &public))
		});
	}

	group.finish();
}

fn bench_ecdsa(c: &mut Criterion) {
	let mut group = c.benchmark_group("ecdsa");

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::ecdsa::Pair::generate().0;
		group.bench_function(BenchmarkId::new("signing", format!("{}", msg_size)), |b| {
			b.iter(|| key.sign(&msg))
		});
	}

	for &msg_size in &[32, 1024, 1024 * 1024] {
		let msg = (0..msg_size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
		let key = sp_core::ecdsa::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		group.bench_function(BenchmarkId::new("verifying", format!("{}", msg_size)), |b| {
			b.iter(|| sp_core::ecdsa::Pair::verify(&sig, &msg, &public))
		});
	}

	group.finish();
}

criterion_group!(
	benches,
	bench_hash_128_fix_size,
	bench_hash_128_dyn_size,
	bench_ed25519,
	bench_sr25519,
	bench_ecdsa,
);
criterion_main!(benches);
