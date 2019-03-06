// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use clap::load_yaml;
use rand::{RngCore, rngs::OsRng};
use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};

mod vanity;

fn print_account(seed: &[u8; 32]) {
	let pair = Pair::from_seed(seed);
	println!("Seed 0x{} is account:\n  Public key (hex): 0x{}\n  Address (SS58): {}",
		HexDisplay::from(seed),
		HexDisplay::from(&pair.public().0),
		pair.public().to_ss58check()
	);
}

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	match matches.subcommand() {
		("generate", Some(_matches)) => {
			let mut seed = [0u8; 32];
			OsRng::new().unwrap().fill_bytes(&mut seed[..]);
			print_account(&seed);
		}
		("vanity", Some(matches)) => {
			let desired: String = matches.value_of("pattern").map(str::to_string).unwrap_or_default();
			let key = vanity::generate_key(&desired).expect("Key generation failed");
			println!("Found account with score {}%", key.score);
			print_account(&key.seed);
		}
		("restore", Some(matches)) => {
			// This subcommand is probably obsolete, see
			// https://github.com/paritytech/substrate/issues/1063

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
			print_account(&seed);
		},
		_ => print_usage(&matches),
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}
