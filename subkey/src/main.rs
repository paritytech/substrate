extern crate ed25519;
extern crate substrate_primitives;

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
	let mut seed = Pair::generate().public().0;
	let mut done = 0;
	loop {
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
		seed = p.public().0;
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched", done);
		}
	}
}
