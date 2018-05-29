extern crate ed25519;
extern crate substrate_primitives;

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
	let desired = "GavWood";
	let score = |s: &str| {
		for truncate in 0..desired.len() - 1 {
			let snip_size = desired.len() - truncate;
			let truncated = &desired[0..snip_size];
			if let Some(pos) = s.find(truncated) {
				return (32 - pos) + (snip_size << 16);
			}
		}
		0
	};
	let mut best = 0;
	let mut seed = Pair::generate().public().0;
	let mut done = 0;
	loop {
		let p = Pair::from_seed(&seed);
		let ss58 = p.public().to_ss58check();
		let s = score(&ss58);
		if s > best {
			println!("{}: {}", ss58, HexDisplay::from(&seed));
			best = s;
		}
		seed = p.public().0;
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched", done);
		}
	}
}
