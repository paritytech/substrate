// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or 
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! implementation of the `vanity` subcommand

use crate::{
	error, utils, with_crypto_scheme,
	CryptoSchemeFlag, NetworkSchemeFlag, OutputTypeFlag,
};
use sp_core::crypto::{Ss58Codec, Ss58AddressFormat};
use structopt::StructOpt;
use rand::{rngs::OsRng, RngCore};
use sp_runtime::traits::IdentifyAccount;
use utils::print_from_uri;

/// The `vanity` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "vanity",
	about = "Generate a seed that provides a vanity address"
)]
pub struct VanityCmd {
	/// Desired pattern
	#[structopt(long, parse(try_from_str = assert_non_empty_string))]
	pattern: String,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	network_scheme: NetworkSchemeFlag,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	output_scheme: OutputTypeFlag,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	crypto_scheme: CryptoSchemeFlag,
}

impl VanityCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		let formated_seed = with_crypto_scheme!(
			self.crypto_scheme.scheme,
			generate_key(&self.pattern, self.network_scheme.network.clone().unwrap_or_default()),
		)?;

		with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_from_uri(
				&formated_seed,
				None,
				self.network_scheme.network.clone(),
				self.output_scheme.output_type.clone(),
			),
		);
		Ok(())
	}
}

/// genertae a key based on given pattern
fn generate_key<Pair>(
	desired: &str,
	network_override: Ss58AddressFormat,
) -> Result<String, &'static str>
	where
		Pair: sp_core::Pair,
		Pair::Public: IdentifyAccount,
		<Pair::Public as IdentifyAccount>::AccountId: Ss58Codec,
{
	println!("Generating key containing pattern '{}'", desired);

	let top = 45 + (desired.len() * 48);
	let mut best = 0;
	let mut seed = Pair::Seed::default();
	let mut done = 0;

	loop {
		if done % 100000 == 0 {
			OsRng.fill_bytes(seed.as_mut());
		} else {
			next_seed(seed.as_mut());
		}

		let p = Pair::from_seed(&seed);
		let ss58 = p.public().into_account().to_ss58check_with_version(network_override);
		let score = calculate_score(&desired, &ss58);
		if score > best || desired.len() < 2 {
			best = score;
			if best >= top {
				println!("best: {} == top: {}", best, top);
				return Ok(utils::format_seed::<Pair>(seed.clone()));
			}
		}
		done += 1;

		if done % good_waypoint(done) == 0 {
			println!("{} keys searched; best is {}/{} complete", done, best, top);
		}
	}
}

fn good_waypoint(done: u64) -> u64 {
	match done {
		0..=1_000_000 => 100_000,
		0..=10_000_000 => 1_000_000,
		0..=100_000_000 => 10_000_000,
		_ => 100_000_000,
	}
}

fn next_seed(seed: &mut [u8]) {
	for i in 0..seed.len() {
		match seed[i] {
			255 => {
				seed[i] = 0;
			}
			_ => {
				seed[i] += 1;
				break;
			}
		}
	}
}

/// Calculate the score of a key based on the desired
/// input.
fn calculate_score(_desired: &str, key: &str) -> usize {
	for truncate in 0.._desired.len() {
		let snip_size = _desired.len() - truncate;
		let truncated = &_desired[0..snip_size];
		if let Some(pos) = key.find(truncated) {
			return (47 - pos) + (snip_size * 48);
		}
	}
	0
}

/// checks that `pattern` is non-empty
fn assert_non_empty_string(pattern: &str) -> Result<String, &'static str> {
	if pattern.is_empty() {
		Err("Pattern must not be empty")
	} else {
		Ok(pattern.to_string())
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::{crypto::Ss58Codec, Pair};
	use sp_core::sr25519;
	#[cfg(feature = "bench")]
	use test::Bencher;
	use structopt::StructOpt;

	#[test]
	fn vanity() {
		let vanity = VanityCmd::from_iter(&["vanity", "--pattern", "j"]);
		assert!(vanity.run().is_ok());
	}

	#[test]
	fn test_generation_with_single_char() {
		let seed = generate_key::<sr25519::Pair>("ab", Default::default()).unwrap();
		assert!(
			sr25519::Pair::from_seed_slice(&hex::decode(&seed[2..]).unwrap())
				.unwrap()
				.public()
				.to_ss58check()
				.contains("ab")
		);
	}

	#[test]
	fn generate_key_respects_network_override() {
		let seed = generate_key::<sr25519::Pair>("ab", Ss58AddressFormat::PolkadotAccount).unwrap();
		assert!(
			sr25519::Pair::from_seed_slice(&hex::decode(&seed[2..]).unwrap())
				.unwrap()
				.public()
				.to_ss58check_with_version(Ss58AddressFormat::PolkadotAccount)
				.contains("ab")
		);
	}

	#[test]
	fn test_score_1_char_100() {
		let score = calculate_score("j", "5jolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim");
		assert_eq!(score, 94);
	}

	#[test]
	fn test_score_100() {
		let score = calculate_score(
			"Polkadot",
			"5PolkadotwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim",
		);
		assert_eq!(score, 430);
	}

	#[test]
	fn test_score_50_2() {
		// 50% for the position + 50% for the size
		assert_eq!(
			calculate_score(
				"Polkadot",
				"5PolkXXXXwHY5k9GpdTgpqs9xjuNvtv8EcwCFpEeyEf3KHim"
			),
			238
		);
	}

	#[test]
	fn test_score_0() {
		assert_eq!(
			calculate_score(
				"Polkadot",
				"5GUWv4bLCchGUHJrzULXnh4JgXsMpTKRnjuXTY7Qo1Kh9uYK"
			),
			0
		);
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_paranoiac(b: &mut Bencher) {
		b.iter(|| generate_key("polk"));
	}

	#[cfg(feature = "bench")]
	#[bench]
	fn bench_not_paranoiac(b: &mut Bencher) {
		b.iter(|| generate_key("polk"));
	}
}
