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
use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};
// use ansi_term::{ANSIString};
use std::thread;
use std::sync::mpsc::channel;
use std::sync::mpsc::Sender;
use pbr::ProgressBar;

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

// pub struct KeySpecs<'a> {
// 	pub desired_pattern: &'a str,
// 	pub case_sensitive: bool,
// 	pub paranoiac: bool,
// 	pub minscore: f32,
// }

/// A structure used to carry both Pair and seed.
/// This should usually NOT been used. If unsure, use Pair.
pub struct KeyPair {
	pub pair: Pair,
	pub seed: [u8; 32],
	pub score: f32,
}

/// Calculate the score of a key based on the desired
/// input. The score is a value between 0.0 and 100.0
fn calculate_score(desired: String, case_sensitive:bool, key: &str) -> f32 {
	let top: f32 = match desired.len() {
		0 => 0.0,
		_ => (45 + (desired.len() * 48)) as f32,
	};

	for truncate in 0..desired.len() {
		let snip_size = desired.len() - truncate;
		let truncated = &desired[0..snip_size];

		if let Some(pos) = match case_sensitive {
			true =>  key.find(truncated),
			false => key.to_lowercase().find(&truncated.to_lowercase()),
		} {

			return ((47 - pos) + (snip_size * 48)) as f32 / top * 100.0;
		}
	}
	0.0
}

// TODO: Try that for the fun
// pub fn highlight_match (key: KeyPair, desired: &str) -> ANSIString<'static> {
// 	for truncate in 0..desired.len() {
// 		let snip_size = desired.len() - truncate;
// 		let truncated = &desired[0..snip_size];
// 		// if let Some(pos) = key.pair.public().to_ss58check().find(truncated) {
// 			let color = ansi_term::Colour::Red;
// 			color.paint(key.pair.public().to_ss58check().to_string())
// 		// }
// 	}
// }

/// Print a set of keys to stdout
pub fn print_keys(keys: Vec<KeyPair>) {

	for key in keys {
		println!(r#"Found match with a score of {:4.2}%
	 - Address  : {}
	 - Hex seed : 0x{}
	 - Seed     : {}"#,
			key.score ,
			key.pair.public().to_ss58check(),
			HexDisplay::from(&key.pair.public().0),
			HexDisplay::from(&key.seed));
	}
}

/// This function generates a single key
pub fn generate_key(desired: &str, case_sensitive: bool, paranoiac:bool , minscore: f32) -> Result<KeyPair, String> {
	let mut seed = [0u8; 32];
	let mut done = 0;
	OsRng::new().unwrap().fill_bytes(&mut seed[..]);

	loop {
		let p = Pair::from_seed(&seed);

		if paranoiac {
			OsRng::new().unwrap().fill_bytes(&mut seed[..]);
		}

		let ss58 = p.public().to_ss58check();
		let score = calculate_score(String::from(desired), case_sensitive, &ss58);
		if score >= minscore {
			let keypair = KeyPair {
				pair: p,
				seed: seed.clone(),
				score: score,
			};
			return Ok(keypair);
		}
		seed = next_seed(seed);
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched", done);
		}
	}
}

/// This function keeps generating keys until we reach the amount of keys we
/// were searching for.
fn threaded_generator(sender: Sender<KeyPair>, desired: &str,
	case_sensitive: bool, paranoiac:bool , minscore: f32, _thread_number: usize) {
    loop {
        let key = generate_key(desired, case_sensitive, paranoiac, minscore).unwrap();

        match sender.send(key) {
            Ok(_) => {},
            Err(_) => break,
        }
    }
}

/// Returns the number of CPU found as well
/// as the number of threads we will be using.
fn get_cpus_specs() -> (usize, usize) {
	let cpus = num_cpus::get();
	(cpus, cpus * 2)
}


/// This function create the threads and monitors whether we
/// have generated enough keys or not
pub fn generate_keys(
	desired: String,
	case_sensitive: bool,
	paranoiac:bool,
	minscore: f32,
	count: usize) -> Vec<KeyPair> {

    let (s, r) = channel();
    let mut result: Vec<KeyPair>  = Vec::new();
	let mut pb = ProgressBar::new(count as u64);

    let (nb_cpus, nb_threads) = get_cpus_specs();
	println!("Found {} CPUs, using {} threads.", nb_cpus, nb_threads);
	println!("Searching for keys matching '{}' with a minimum score of {}.", desired, minscore);

    for j in 0..nb_threads {
        let sender = s.clone();
    	let pattern = desired.clone();
        thread::spawn(move || {
            threaded_generator(sender, &pattern, case_sensitive, paranoiac , minscore, j);
        });
    }

    while result.len() < count {
        match r.recv() {
            Ok(key) => {
            	println!("{:>6.2}%\t{}\t{}", key.score, key.pair.public().to_ss58check(), HexDisplay::from(&key.pair.public().0));
            	result.push(key);
            	pb.inc();
            },
            Err(_) => break,
        };
    }

    result.sort_by(|a,b| b.score.partial_cmp(&a.score).unwrap_or(std::cmp::Ordering::Equal));
    result
}

#[cfg(test)]
mod tests {
	use super::*;
	#[cfg(feature = "bench")]
	use test::Bencher;

	#[test]
	fn test_generation_with_single_char() {
		assert!(generate_key("j", true, false, 75.0).unwrap().pair.public().to_ss58check().contains("j"));
	}

	#[test]
	fn test_score_1_char_100() {
		let score = calculate_score(String::from("j"), true, "5jolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!(score >= 100.0);
	}

	#[test]
	fn test_score_100() {
		let score = calculate_score(String::from("Polkadot"), true, "5PolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!(score >= 100.0);
	}

	#[test]
	fn test_score_50() {
		// ~50% for the position + ~50% for the size
		assert!(calculate_score(String::from("Polkadot"), true, "5PolkXXXXwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim") >= 50.0);
	}

	#[test]
	fn test_score_0() {
		assert_eq!(calculate_score(String::from("Polkadot"), true, "5GUWv4bLCchGUHJrzULXnh4JgXsMpTKRnjuXTY7Qo1Kh9uYK"), 0.0);
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_paranoiac(b: &mut Bencher) {
		b.iter(|| {
			generate_key("abc", false, true, 75.0)
		});
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_not_paranoiac(b: &mut Bencher) {
		b.iter(|| {
			generate_key("abc", false, false, 75.0)
		});
	}
}
