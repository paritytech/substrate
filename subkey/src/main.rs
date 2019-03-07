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

extern crate substrate_bip39;
extern crate rustc_hex;

use clap::load_yaml;
use rand::{RngCore, rngs::OsRng};
use substrate_bip39::{mini_secret_from_entropy};
use bip39::{Mnemonic, Language, MnemonicType};
use substrate_primitives::{ed25519, sr25519, hexdisplay::HexDisplay};
use schnorrkel::keys::MiniSecretKey;
use rustc_hex::FromHex;

mod vanity;

trait Crypto {
	type Seed: AsRef<[u8]> + AsMut<[u8]> + Sized + Default;
	type Pair;
	fn generate_phrase() -> String {
		Mnemonic::new(MnemonicType::Words12, Language::English).phrase().to_owned()
	}
	fn generate_seed() -> Self::Seed;
	fn seed_from_phrase(phrase: &str, password: Option<&str>) -> Self::Seed;
	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair;
	fn pair_from_phrase(phrase: &str, password: Option<&str>) -> Self::Pair {
		Self::pair_from_seed(&Self::seed_from_phrase(phrase, password))
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String;
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8>;
	fn print_from_seed(seed: &Self::Seed) {
		let pair = Self::pair_from_seed(seed);
		println!("Seed 0x{} is account:\n  Public key (hex): 0x{}\n  Address (SS58): {}",
			HexDisplay::from(&seed.as_ref()),
			HexDisplay::from(&Self::public_from_pair(&pair)),
			Self::ss58_from_pair(&pair)
		);
	}
	fn print_from_phrase(phrase: &str, password: Option<&str>) {
		let seed = Self::seed_from_phrase(phrase, password);
		let pair = Self::pair_from_seed(&seed);
		println!("Phrase `{}` is account:\n  Seed: 0x{}\n  Public key (hex): 0x{}\n  Address (SS58): {}",
			phrase,
			HexDisplay::from(&seed.as_ref()),
			HexDisplay::from(&Self::public_from_pair(&pair)),
			Self::ss58_from_pair(&pair)
		);
	}
}

struct OriginalEd25519;

impl Crypto for OriginalEd25519 {
	type Seed = [u8; 32];
	type Pair = ed25519::Pair;

	fn generate_seed() -> Self::Seed {
		let mut seed = [0u8; 32];
		OsRng::new().unwrap().fill_bytes(&mut seed[..]);
		seed
	}

	fn seed_from_phrase(phrase: &str, password: Option<&str>) -> Self::Seed {
		if password.is_some() {
			panic!("Ed25519 original doesn't support passwords")
		}

		let mut raw_seed = phrase.as_bytes();

		if raw_seed.len() > 32 {
			raw_seed = &raw_seed[..32];
			println!("seed is too long and will be truncated to: {}", HexDisplay::from(&raw_seed));
		}

		// Copy the raw_seed into a buffer that already contains ' ' 0x20.
		// This will effectively get us padding for seeds shorter than 32.
		let mut seed = [' ' as u8; 32];
		let len = raw_seed.len().min(32);
		seed[..len].copy_from_slice(&raw_seed[..len]);
		seed
	}

	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair { ed25519::Pair::from_seed(seed) }
	fn ss58_from_pair(pair: &Self::Pair) -> String { pair.public().to_ss58check() }
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8> { (&pair.public().0[..]).to_owned() }
}

struct Sr25519;

impl Crypto for Sr25519 {
	type Seed = [u8; 32];
	type Pair = sr25519::Pair;

	fn generate_seed() -> Self::Seed {
		let mut seed = [0u8; 32];
		OsRng::new().unwrap().fill_bytes(&mut seed[..]);
		seed
	}

	fn seed_from_phrase(phrase: &str, password: Option<&str>) -> Self::Seed {
		mini_secret_from_entropy(
			Mnemonic::from_phrase(phrase, Language::English)
				.unwrap_or_else(|_|
					panic!("Phrase is not a valid BIP-39 phrase: \n    {}", phrase)
				)
				.entropy(),
			password.unwrap_or("")
		)
			.expect("32 bytes can always build a key; qed")
			.to_bytes()
	}

	fn pair_from_phrase(phrase: &str, password: Option<&str>) -> Self::Pair {
		sr25519::Pair::from_phrase(phrase, password)
			.unwrap_or_else(||
				panic!("Phrase is not a valid BIP-39 phrase: \n    {}", phrase)
			)
	}

	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair {
		MiniSecretKey::from_bytes(seed)
			.expect("32 bytes can always build a key; qed")
			.into()
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String { pair.public().to_ss58check() }
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8> { (&pair.public().0[..]).to_owned() }
}

fn execute<C: Crypto<Seed=[u8; 32]>>(matches: clap::ArgMatches) {
	let password = matches.value_of("password");
	match matches.subcommand() {
		("generate", Some(_matches)) => {
			// create a new randomly generated mnemonic phrase
			let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
			C::print_from_phrase(mnemonic.phrase(), password);
		},
		("vanity", Some(matches)) => {
			let desired: String = matches.value_of("pattern").map(str::to_string).unwrap_or_default();
			let key = vanity::generate_key::<C>(&desired).expect("Key generation failed");
			C::print_from_seed(&key.seed);
		}
		("restore", Some(matches)) => {
			let phrase = matches.value_of("seed")
				.expect("seed parameter is required; thus it can't be None; qed");
			C::print_from_phrase(phrase, password);
		},
		("query", Some(matches)) => {
			let seed_data = matches.value_of("seed")
				.expect("seed parameter is required; thus it can't be None; qed");
			let seed_data = if seed_data.starts_with("0x") {
				&seed_data[2..]
			} else {
				seed_data
			};
			let seed_data: Vec<u8> = seed_data.from_hex().expect("seed is not valid hex");
			let correct_size = ::std::mem::size_of::<C::Seed>();
			if seed_data.len() != correct_size {
				panic!("Seed is incorrect size. It must be {} bytes for this cryptography", correct_size);
			}
			let mut seed = C::Seed::default();
			seed.as_mut().copy_from_slice(&seed_data);
			C::print_from_seed(&seed);
		},
		_ => print_usage(&matches),
	}
}

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	if matches.is_present("ed25519original") {
		execute::<OriginalEd25519>(matches)
	} else {
		execute::<Sr25519>(matches)
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}
