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

use std::io::{stdin, Read};
use clap::load_yaml;
use rand::{RngCore, rngs::OsRng};
use substrate_bip39::mini_secret_from_entropy;
use bip39::{Mnemonic, Language, MnemonicType};
use substrate_primitives::{ed25519, sr25519, hexdisplay::HexDisplay, Pair, crypto::Ss58Codec};
use schnorrkel::keys::MiniSecretKey;

mod vanity;

trait Crypto {
	type Seed: AsRef<[u8]> + AsMut<[u8]> + Sized + Default;
	type Pair: Pair;
	fn generate_phrase() -> String {
		Mnemonic::new(MnemonicType::Words12, Language::English).phrase().to_owned()
	}
	fn generate_seed() -> Self::Seed {
		let mut seed: Self::Seed = Default::default();
		OsRng::new().unwrap().fill_bytes(seed.as_mut());
		seed
	}
	fn seed_from_phrase(phrase: &str, password: Option<&str>) -> Self::Seed;
	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair;
	fn pair_from_suri(phrase: &str, password: Option<&str>) -> Self::Pair {
		Self::pair_from_seed(&Self::seed_from_phrase(phrase, password))
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String;
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8>;
	fn seed_from_pair(_pair: &Self::Pair) -> Option<&Self::Seed> { None }
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
	fn print_from_uri(uri: &str, password: Option<&str>) where <Self::Pair as Pair>::Public: Sized + Ss58Codec + AsRef<[u8]> {
		if let Ok(pair) = Self::Pair::from_string(uri, password) {
			let seed_text = Self::seed_from_pair(&pair)
				.map_or_else(Default::default, |s| format!("\n  Seed: 0x{}", HexDisplay::from(&s.as_ref())));
			println!("Secret Key URI `{}` is account:{}\n  Public key (hex): 0x{}\n  Address (SS58): {}",
				uri,
				seed_text,
				HexDisplay::from(&Self::public_from_pair(&pair)),
				Self::ss58_from_pair(&pair)
			);
		}
		if let Ok(public) = <Self::Pair as Pair>::Public::from_string(uri) {
			println!("Public Key URI `{}` is account:\n  Public key (hex): 0x{}\n  Address (SS58): {}",
				uri,
				HexDisplay::from(&public.as_ref()),
				public.to_ss58check()
			);
		}
	}
}

struct Ed25519;

impl Crypto for Ed25519 {
	type Seed = [u8; 32];
	type Pair = ed25519::Pair;

	fn seed_from_phrase(phrase: &str, password: Option<&str>) -> Self::Seed {
		Sr25519::seed_from_phrase(phrase, password)
	}
	fn pair_from_suri(suri: &str, password_override: Option<&str>) -> Self::Pair {
		ed25519::Pair::from_legacy_string(suri, password_override)
	}
	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair { ed25519::Pair::from_seed(seed.clone()) }
	fn ss58_from_pair(pair: &Self::Pair) -> String { pair.public().to_ss58check() }
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8> { (&pair.public().0[..]).to_owned() }
	fn seed_from_pair(pair: &Self::Pair) -> Option<&Self::Seed> { Some(pair.seed()) }
}

struct Sr25519;

impl Crypto for Sr25519 {
	type Seed = [u8; 32];
	type Pair = sr25519::Pair;

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

	fn pair_from_suri(suri: &str, password: Option<&str>) -> Self::Pair {
		sr25519::Pair::from_string(suri, password).expect("Invalid phrase")
	}

	fn pair_from_seed(seed: &Self::Seed) -> Self::Pair {
		MiniSecretKey::from_bytes(seed)
			.expect("32 bytes can always build a key; qed")
			.into()
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String { pair.public().to_ss58check() }
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8> { (&pair.public().0[..]).to_owned() }
}

fn execute<C: Crypto<Seed=[u8; 32]>>(matches: clap::ArgMatches) where
	<<C as Crypto>::Pair as Pair>::Signature: AsRef<[u8]> + AsMut<[u8]> + Default,
	<<C as Crypto>::Pair as Pair>::Public: Sized + AsRef<[u8]> + Ss58Codec + AsRef<<<C as Crypto>::Pair as Pair>::Public>,
{
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
		("inspect", Some(matches)) => {
			// TODO: Accept public key with derivation path.
			let uri = matches.value_of("uri")
				.expect("URI parameter is required; thus it can't be None; qed");
			C::print_from_uri(uri, password);
		},
		("sign", Some(matches)) => {
			let suri = matches.value_of("suri")
				.expect("secret URI parameter is required; thus it can't be None; qed");
			let pair = C::pair_from_suri(suri, password);
			let mut message = vec![];
			stdin().lock().read_to_end(&mut message).expect("Error reading from stdin");
			if matches.is_present("hex") {
				message = hex::decode(&message).expect("Invalid hex in message");
			}
			let sig = pair.sign(&message);
			println!("{}", hex::encode(&sig));
		}
		("verify", Some(matches)) => {
			let sig_data = matches.value_of("sig")
				.expect("signature parameter is required; thus it can't be None; qed");
			let mut sig = <<C as Crypto>::Pair as Pair>::Signature::default();
			let sig_data = hex::decode(sig_data).expect("signature is invalid hex");
			if sig_data.len() != sig.as_ref().len() {
				panic!("signature is an invalid length. {} bytes is not the expected value of {} bytes", sig_data.len(), sig.as_ref().len());
			}
			sig.as_mut().copy_from_slice(&sig_data);
			let uri = matches.value_of("uri")
				.expect("public uri parameter is required; thus it can't be None; qed");
			let pubkey = <<C as Crypto>::Pair as Pair>::Public::from_string(uri).ok().or_else(||
				<C as Crypto>::Pair::from_string(uri, password).ok().map(|p| p.public())
			).expect("Invalid URI; expecting either a secret URI or a public URI.");
			let mut message = vec![];
			stdin().lock().read_to_end(&mut message).expect("Error reading from stdin");
			if matches.is_present("hex") {
				message = hex::decode(&message).expect("Invalid hex in message");
			}
			if <<C as Crypto>::Pair as Pair>::verify(&sig, &message, &pubkey) {
				println!("Signature verifies correctly.")
			} else {
				println!("Signature invalid.")
			}
		}
		_ => print_usage(&matches),
	}
}

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml)
		.version(env!("CARGO_PKG_VERSION"))
		.get_matches();

	if matches.is_present("ed25519") {
		execute::<Ed25519>(matches)
	} else {
		execute::<Sr25519>(matches)
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}
