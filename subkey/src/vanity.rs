// Copyright 2018 Parity Technologies (UK) Ltd.
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

use rand::{OsRng, Rng};
use substrate_primitives::ed25519::Pair;

fn good_waypoint(done: u64) -> u64 {
	match done {
		0 ... 1_000_000 => 100_000,
		0 ... 10_000_000 => 1_000_000,
		0 ... 100_000_000 => 10_000_000,
		_ => 100_000_000,
	}
}

fn next_seed(mut seed: [u8; 32]) -> [u8; 32] {
	for i in 0..32 {
		match seed[i] {
			255 => { seed[i] = 0; }
			_ => { seed[i] += 1; break; }
		}
	}
	return seed;
}

/// A structure used to carry both Pair and seed.
/// This should usually NOT been used. If unsure, use Pair.
pub struct KeyPair {
	pub pair: Pair,
	pub seed: [u8; 32],
	pub score: usize,
}

/// Calculate the score of a key based on the desired
/// input.
fn calculate_score(_desired: &str, key: &str) -> usize {
	for truncate in 0.._desired.len() {
		let snip_size = _desired.len() - truncate;
		let truncated = &_desired[0..snip_size];
		if let Some(pos) = key.find(truncated) {
			return (47 - pos) + (snip_size * 48);
		}
	}
	0
}

pub fn generate_key(_desired: &str) -> Result<KeyPair, &str> {
	println!("Generating key containing pattern '{}'", _desired);

	let top = 45 + (_desired.len() * 48);
	let mut best = 0;
	let mut seed = [0u8; 32];
	let mut done = 0;

	OsRng::new().unwrap().fill_bytes(&mut seed[..]);

	loop {
		// reset to a new random seed at beginning and regularly thereafter
		if done % 100000 == 0 {
			OsRng::new().unwrap().fill_bytes(&mut seed[..]);
		}

		let p = Pair::from_seed(&seed);
		let ss58 = p.public().to_ss58check();
		let score = calculate_score(&_desired, &ss58);
		if score > best || _desired.len() < 2 {
			best = score;
			let keypair = KeyPair {
				pair: p,
				seed: seed.clone(),
				score: score,
			};
			if best >= top {
				println!("best: {} == top: {}", best, top);
				return Ok(keypair);
			}
		}
		seed = next_seed(seed);
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched; best is {}/{} complete", done, best, top);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	#[cfg(feature = "bench")]
	use test::Bencher;

	#[test]
	fn test_generation_with_single_char() {
		assert!(generate_key("j").unwrap().pair.public().to_ss58check().contains("j"));
	}

	#[test]
	fn test_score_1_char_100() {
		let score = calculate_score("j", "5jolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert_eq!(score, 94);
	}

	#[test]
	fn test_score_100() {
		let score = calculate_score("Polkadot", "5PolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert_eq!(score, 430);
	}

	#[test]
	fn test_score_50_2() {
		// 50% for the position + 50% for the size
		assert_eq!(calculate_score("Polkadot", "5PolkXXXXwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim"), 238);
	}

	#[test]
	fn test_score_0() {
		assert_eq!(calculate_score("Polkadot", "5GUWv4bLCchGUHJrzULXnh4JgXsMpTKRnjuXTY7Qo1Kh9uYK"), 0);
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_paranoiac(b: &mut Bencher) {
		b.iter(|| {
			generate_key("polk")
		});
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_not_paranoiac(b: &mut Bencher) {
		b.iter(|| {
			generate_key("polk")
		});
	}
}
