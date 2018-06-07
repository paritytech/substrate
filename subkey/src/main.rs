extern crate ed25519;
extern crate substrate_primitives;
extern crate rand;

use rand::{OsRng, Rng};
use std::env::args;
use ed25519::Pair;
use substrate_primitives::hexdisplay::HexDisplay;

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

fn main() {
	if args().len() != 2 {
		println!("Usage: subkey <search string>");
		return;
	}
	let desired = args().last().unwrap();
	let score = |s: &str| {
		for truncate in 0..desired.len() - 1 {
			let snip_size = desired.len() - truncate;
			let truncated = &desired[0..snip_size];
			if let Some(pos) = s.find(truncated) {
				return (31 - pos) + (snip_size * 32);
			}
		}
		0
	};
	let top = 30 + (desired.len() * 32);
	let mut best = 0;
	let mut seed = [0u8; 32];
	let mut done = 0;
	loop {
		// reset to a new random seed at beginning and regularly after for paranoia.
		if done % 100000 == 0 {
			OsRng::new().unwrap().fill_bytes(&mut seed[..]);
		}

		let p = Pair::from_seed(&seed);
		let ss58 = p.public().to_ss58check();
		let s = score(&ss58);
		if s > best {
			println!("{}: {} ({}% complete)", ss58, HexDisplay::from(&seed), s * 100 / top);
			best = s;
			if best == top {
				break;
			}
		}
		seed = next_seed(seed);
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched", done);
		}
	}
}
