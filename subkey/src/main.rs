#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")]
extern crate test;
extern crate ed25519;
extern crate substrate_primitives;
extern crate rand;

use rand::{OsRng, Rng};
use std::env::args;
use ed25519::Pair;
use substrate_primitives::hexdisplay::HexDisplay;
use std::cmp;

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
			let score = cmp::min(100, (51 - pos) + (snip_size * 50 / _desired.len()));
			return score;
		}
	}
	0
}

pub fn generate_key(_desired: &str, _amount: usize, paranoiac: bool) -> Result<Vec<KeyPair>, &str> {
	println!("Generating {} keys with pattern '{}'", _amount, &_desired);

	let top = 30 + (_desired.len() * 32);
	let mut best = 0;
	let mut seed = [0u8; 32];
	let mut done = 0;
	let mut res = vec![];

	OsRng::new().unwrap().fill_bytes(&mut seed[..]);

	loop {
		if res.len() >= _amount { break; }

		// reset to a new random seed at beginning and regularly after for paranoia.
		if paranoiac || done % 100000 == 0 {
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
			res.push(keypair);
			if best == top {
				println!("best: {} == top: {}", best, top);
				break;
			}
		}
		seed = next_seed(seed);
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("Stopping after {} keys searched", done);
			break;
		}
	}
	res.sort_unstable_by(|a, b| b.score.cmp(&a.score));
	Ok(res)
}

fn main() {
	let desired: String = args().nth(1).unwrap_or_default();
	let amount_of_keys: String = args().nth(2).unwrap_or_else(|| String::from("1"));
	let amount_of_keys: usize = amount_of_keys.parse::<usize>().expect("Failed to parse number");

	let keys = generate_key(&desired, amount_of_keys, true).expect("Key generation failed");
	for key in keys {
		println!("{} - {} ({}%)",
			key.pair.public().to_ss58check(),
			HexDisplay::from(&key.seed),
			key.score);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	#[cfg(feature = "bench")]
	use test::Bencher;

	#[test]
	fn test_generation_no_args() {
		assert!(generate_key("",1, false).unwrap().len() == 1);
	}

	#[test]
	fn test_generation_with_single_char() {
		assert!(generate_key("j", 1, false).unwrap().len() == 1);
	}

	#[test]
	fn test_generation_with_args() {
		assert!(generate_key("polka", 2, false).unwrap().len() == 2);
	}

	#[test]
	fn test_score_1_char_100() {
		let score = calculate_score("j", "5jolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!(score  == 100, format!("Wrong score, we found {}", score));
	}

	#[test]
	fn test_score_100() {
		let score = calculate_score("Polkadot", "5PolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!( score == 100, format!("Wrong score, we found {}", score));
	}

	#[test]
	fn test_score_50_2() {
		// 50% for the position + 50% for the size
		assert!(calculate_score("Polkadot", "5PolkXXXXwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim") == 75);
	}

	#[test]
	fn test_score_0() {
		assert!(calculate_score("Polkadot", "5GUWv4bLCchGUHJrzULXnh4JgXsMpTKRnjuXTY7Qo1Kh9uYK") == 0);
	}

	#[cfg(feature = "bench")]
	#[bench]
    fn bench_paranoiac(b: &mut Bencher) {
        b.iter(|| {
			generate_key("polka", 3, true)
		});
    }

	#[cfg(feature = "bench")]
    #[bench]
    fn bench_not_paranoiac(b: &mut Bencher) {
        b.iter(|| {
			generate_key("polka", 3, false)
		});
    }
}
