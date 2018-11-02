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

use keypair::KeyPair;
use keyspecs::KeySpecs;

use rand::{OsRng, Rng};
use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};
use std::thread;
use std::sync::mpsc::channel;
use std::sync::mpsc::Sender;
use pbr::ProgressBar;

pub enum OutputFormat {
	Stdout,
	Csv,
}

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

/// Calculate the score of a key based on the desired
/// input. The score is a value between 0.0 and 100.0
fn calculate_score(key_specs: &KeySpecs, key: &str) -> f32 {
	let desired = key_specs.desired_pattern.clone();
	let top: f32 = match desired.len() {
		0 => 0.0,
		_ => (45 + (desired.len() * 48)) as f32,
	};

	for truncate in 0..desired.len() {
		let snip_size = desired.len() - truncate;
		let truncated = &desired[0..snip_size];

		if let Some(pos) = match key_specs.case_sensitive {
			true =>  key.find(truncated),
			false => key.to_lowercase().find(&truncated.to_lowercase()),
		} {

			return ((47 - pos) + (snip_size * 48)) as f32 / top * 100.0;
		}
	}
	0.0
}

/// Print a set of keys to stdout
pub fn print_keys(keys: Vec<KeyPair>, format: OutputFormat) {
	match format {
		OutputFormat::Stdout => {
			for key in keys {
				println!("{}", key);
			}
		},
		OutputFormat::Csv => {
			println!("\n\nScore\tAddress\tHex seed\tSeed");
			for key in keys {
				key.print_csv();
			}
		}
	}
}

/// This function generates a single key matching the specs
pub fn generate_key(key_specs: &KeySpecs) -> Result<KeyPair, String> {
	let mut seed = [0u8; 32];
	let mut done = 0;
	OsRng::new().unwrap().fill_bytes(&mut seed[..]);

	loop {
		let p = Pair::from_seed(&seed);
		let ss58 = p.public().to_ss58check();
		let score = calculate_score(&key_specs, &ss58);
		if score >= key_specs.minscore {
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
fn threaded_generator(sender: Sender<KeyPair>, key_specs: &KeySpecs, _thread_number: u8) {
    loop {
        let key = generate_key(key_specs).unwrap();

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
pub fn generate_keys(key_specs: KeySpecs, count: usize, threads: u8) -> Vec<KeyPair> {
    let (s, r) = channel();
    let mut result: Vec<KeyPair> = Vec::new();
	let mut pb = ProgressBar::new(count as u64);

    let nb_threads = match threads {
    	0 => {
    		let (nb_cpus, nb_threads) = get_cpus_specs();
			println!("Found {} CPUs, using {} threads", nb_cpus, nb_threads);
			nb_threads as u8
    	},
    	n @ _ => {
			println!("Using {} threads", n);
			n as u8
    	}
    };
    println!("{}", key_specs);

    for j in 0..nb_threads {
        let sender = s.clone();
        let specs = key_specs.clone();
        thread::spawn(move || {
            threaded_generator(sender, &specs, j);
        });
    }

    while result.len() < count {
        match r.recv() {
            Ok(key) => {
            	println!("{:>6.2}%\t{}\t0x{}", key.score, key.pair.public().to_ss58check(),
            		HexDisplay::from(&key.pair.public().0));
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
		let specs = KeySpecs {
			desired_pattern: String::from("j"),
			case_sensitive: true,
			minscore: 75.0,
		};

		assert!(generate_key(&specs).unwrap().pair.public().to_ss58check().contains("j"));
	}

	#[test]
	fn test_score_1_char_100() {
		let specs = KeySpecs {
			desired_pattern: String::from("j"),
			case_sensitive: true,
			minscore: 75.0,
		};

		let score = calculate_score(&specs, "5jubstratewHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!(score >= 100.0);
	}

	#[test]
	fn test_score_100() {
		let specs = KeySpecs {
			desired_pattern: String::from("Substrate"),
			case_sensitive: true,
			minscore: 75.0,
		};
		let score = calculate_score(&specs, "5SubstratewHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert!(score >= 100.0);
	}

	#[test]
	fn test_score_50() {
		let specs = KeySpecs {
			desired_pattern: String::from("Substrate"),
			case_sensitive: true,
			minscore: 75.0,
		};

		// ~50% for the position + ~50% for the size
		assert!(calculate_score(&specs, "5SubstXXXwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim") >= 50.0);
	}

	#[test]
	fn test_score_0() {
		let specs = KeySpecs {
			desired_pattern: String::from("Substrate"),
			case_sensitive: true,
			minscore: 75.0,
		};

		assert_eq!(calculate_score(&specs, "5GUWv4bLCchGUHJrzULXnh4JgXsMpTKRnjuXTY7Qo1Kh9uYK"), 0.0);
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench(b: &mut Bencher) {
		let specs = KeySpecs {
			desired_pattern: String::from("oo7"),
			case_sensitive: false,
			minscore: 75.0,
		};

		b.iter(|| {
			generate_key(&specs)
		});
	}
}
