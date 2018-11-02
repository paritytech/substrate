//! # subkey
//!
//! `subkey` is is a cli utility that allows operations on keys such as
//! restoration of keys from their seed, generation of vanity addresses, etc...
//! You can find the documentation [here](https://github.com/paritytech/substrate/blob/master/subkey/README.adoc).

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
extern crate num_cpus;

#[macro_use]
extern crate clap;
extern crate pbr;

use vanity::OutputFormat;
use keyspecs::KeySpecs;
use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};

mod vanity;
mod keypair;
mod keyspecs;

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	match matches.subcommand() {
		("vanity", Some(matches)) => {
			let number: u32 = matches.value_of("number").map(str::to_string).unwrap_or_default().parse::<u32>().unwrap();
			let threads: u8 = matches.value_of("threads").map(str::to_string).unwrap_or_default().parse::<u8>().unwrap();
			let format: OutputFormat = match matches.value_of("format").unwrap_or_default() {
				"csv" => OutputFormat::Csv,
				_ => OutputFormat::Stdout,
			};
			let key_specs = KeySpecs {
				 desired_pattern: matches.value_of("pattern").map(str::to_string).unwrap_or_default(),
				 case_sensitive: matches.is_present("case_sensitive"),
				 paranoiac: matches.is_present("paranoiac"),
				 minscore: ::std::cmp::min(
				 	matches.value_of("minscore").map(str::to_string).unwrap_or_default().parse::<u8>().unwrap(), 100) as f32,
			};

			let keys = vanity::generate_keys(key_specs, number as usize, threads);
			vanity::print_keys(keys, format);
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

			println!("Seed 0x{} is account:\n    SS58: {}\n    Hex: 0x{}",
				HexDisplay::from(&seed),
				pair.public().to_ss58check(),
				HexDisplay::from(&pair.public().0)
			);
		},
		_ => print_usage(&matches),
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}
