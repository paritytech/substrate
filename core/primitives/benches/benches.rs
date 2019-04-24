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

// TODO: Move benchmark to criterion #2354
#![feature(test)]

extern crate test;
use hex_literal::{hex, hex_impl};
use substrate_primitives::hashing::{twox_128, blake2_128};


const MAX_KEY_SIZE: u32 = 32;

fn data_set() -> Vec<Vec<u8>> {
	use rand::SeedableRng;
	use rand::Rng;

	let rnd: [u8; 32] = rand::rngs::StdRng::seed_from_u64(12).gen();
	let mut rnd = rnd.iter().cycle();
	let mut res = Vec::new();
	for size in 1..=MAX_KEY_SIZE {
		for _ in 0..1_000 {
			let value = (0..size)
				.map(|_| rnd.next().unwrap().clone())
				.collect();
			res.push(value);
		}
	}
	res
}

fn bench_hash_128(b: &mut test::Bencher, f: &Fn(&[u8]) -> [u8; 16]) {
	let data_set = data_set();
	b.iter(|| {
		for data in &data_set {
			let _a = f(data);
		}
	});
}

#[bench]
fn bench_blake2_128(b: &mut test::Bencher) {
	bench_hash_128(b, &blake2_128);
}

#[bench]
fn bench_twox_128(b: &mut test::Bencher) {
	bench_hash_128(b, &twox_128);
}
