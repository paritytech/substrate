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

use criterion::{Criterion, black_box, Bencher, Fun};
use std::time::Duration;
use sp_core::crypto::Pair as _;
use sp_core::hashing::{twox_128, blake2_128};

const MAX_KEY_SIZE: u32 = 32;

fn get_key(key_size: u32) -> Vec<u8> {
	use rand::SeedableRng;
	use rand::Rng;

	let rnd: [u8; 32] = rand::rngs::StdRng::seed_from_u64(12).gen();
	let mut rnd = rnd.iter().cycle();

	(0..key_size)
		.map(|_| rnd.next().unwrap().clone())
		.collect()
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
	let key = get_key(MAX_KEY_SIZE);
	let blake_fn = Fun::new("blake2_128", bench_blake2_128);
	let twox_fn = Fun::new("twox_128", bench_twox_128);
	let fns = vec![blake_fn, twox_fn];

	c.bench_functions("fixed size hashing", fns, key);
}

fn bench_hash_128_dyn_size(c: &mut Criterion) {
	let mut keys = Vec::new();
	for i in (2..MAX_KEY_SIZE).step_by(4) {
		keys.push(get_key(i).clone())
	}

	c.bench_function_over_inputs("dyn size hashing - blake2", |b, key| bench_blake2_128(b, &key), keys.clone());
	c.bench_function_over_inputs("dyn size hashing - twox", |b, key| bench_twox_128(b, &key), keys);
}

fn bench_ed25519(c: &mut Criterion) {
	c.bench_function_over_inputs("signing - ed25519", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::ed25519::Pair::generate().0;
		b.iter(|| key.sign(&msg))
	}, vec![32, 1024, 1024 * 1024]);

	c.bench_function_over_inputs("verifying - ed25519", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::ed25519::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		b.iter(|| sp_core::ed25519::Pair::verify(&sig, &msg, &public))
	}, vec![32, 1024, 1024 * 1024]);
}

fn bench_sr25519(c: &mut Criterion) {
	c.bench_function_over_inputs("signing - sr25519", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::sr25519::Pair::generate().0;
		b.iter(|| key.sign(&msg))
	}, vec![32, 1024, 1024 * 1024]);

	c.bench_function_over_inputs("verifying - sr25519", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::sr25519::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		b.iter(|| sp_core::sr25519::Pair::verify(&sig, &msg, &public))
	}, vec![32, 1024, 1024 * 1024]);
}

fn bench_ecdsa(c: &mut Criterion) {
	c.bench_function_over_inputs("signing - ecdsa", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::ecdsa::Pair::generate().0;
		b.iter(|| key.sign(&msg))
	}, vec![32, 1024, 1024 * 1024]);

	c.bench_function_over_inputs("verifying - ecdsa", |b, &msg_size| {
		let msg = (0..msg_size)
			.map(|_| rand::random::<u8>())
			.collect::<Vec<_>>();
		let key = sp_core::ecdsa::Pair::generate().0;
		let sig = key.sign(&msg);
		let public = key.public();
		b.iter(|| sp_core::ecdsa::Pair::verify(&sig, &msg, &public))
	}, vec![32, 1024, 1024 * 1024]);
}

criterion_group!{
	name = benches;
	config = Criterion::default().warm_up_time(Duration::from_millis(500)).without_plots();
	targets = bench_hash_128_fix_size, bench_hash_128_dyn_size, bench_ed25519, bench_sr25519, bench_ecdsa
}
criterion_main!(benches);
