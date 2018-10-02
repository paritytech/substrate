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

#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")]
extern crate test;
extern crate substrate_primitives;
extern crate rand;

#[macro_use]
extern crate clap;

use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};

mod vanity;

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	match matches.subcommand() {
		("vanity", Some(matches)) => {
			let desired: String = matches.value_of("pattern").map(str::to_string).unwrap_or_default();
			let amount_of_keys = matches.value_of("number")
				.expect("`number` has a default value; thus it can't be None; qed");
			let amount_of_keys: usize = amount_of_keys.parse::<usize>().expect("Failed to parse number");

			let keys = vanity::generate_key(&desired, amount_of_keys, true).expect("Key generation failed");
			for key in keys {
				println!("{} - {} ({}%)",
					key.pair.public().to_ss58check(),
					HexDisplay::from(&key.seed),
					key.score);
			}
		}
		("restore", Some(matches)) => {
			let mut raw_seed = matches.value_of("seed")
				.map(str::as_bytes)
				.expect("seed parameter is required; thus it can't be None; qed");

			if raw_seed.len() > 32 {
				raw_seed = &raw_seed[..32];
				println!("seed is too long and will be truncated to: {}", HexDisplay::from(&raw_seed));
			}

			// Copy the raw_seed into a buffer that already contains ' ' 0x20.
			// This will effectively get us padding for seeds shorter than 32.
			let mut seed = [' ' as u8; 32];
			let len = raw_seed.len().min(32);
			seed[..len].copy_from_slice(&raw_seed[..len]);
			let pair = Pair::from_seed(&seed);

			println!("{}: {}", HexDisplay::from(&seed), pair.public().to_ss58check());
		},
		_ => print_usage(&matches),
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}
