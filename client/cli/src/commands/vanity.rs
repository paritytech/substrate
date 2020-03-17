// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! implementation of the `vanity` subcommand

use crate::{
	error, format_seed, SharedParams,
	VersionInfo, print_from_uri, with_crypto_scheme,
};
use sp_core::crypto::Ss58Codec;
use structopt::StructOpt;
use rand::{rngs::OsRng, RngCore};
use sc_service::{Configuration, ChainSpec};
use sp_runtime::traits::IdentifyAccount;

/// The `vanity` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "vanity",
	about = "Generate a seed that provides a vanity address"
)]
pub struct VanityCmd {
	/// Number of keys to generate
	#[structopt(long, short)]
	number: String,

	/// Desired pattern
	#[structopt(long)]
	pattern: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl VanityCmd {
	/// Run the command
	pub fn run(self) -> error::Result<()> {
		let desired: String = self.pattern.unwrap_or_default();
		let formated_seed = with_crypto_scheme!(self.shared_params.scheme, generate_key(&desired))?;
		with_crypto_scheme!(
			self.shared_params.scheme,
			print_from_uri(
				&formated_seed,
				None,
				self.shared_params.network,
				self.shared_params.output_type
			)
		);
		Ok(())
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<F>(
		&self,
		mut config: &mut Configuration,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		F: FnOnce(&str) -> Result<Box<dyn ChainSpec>, String>,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;
		config.use_in_memory_keystore()?;

		Ok(())
	}
}

/// genertae a key based on given pattern
fn generate_key<Pair>(desired: &str) -> Result<String, &'static str>
	where
		Pair: sp_core::Pair,
		Pair::Public: IdentifyAccount,
		<Pair::Public as IdentifyAccount>::AccountId: Ss58Codec,
{
	if desired.is_empty() {
		return Err("Pattern must not be empty");
	}

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
		let ss58 = p.public().into_account().to_ss58check();
		let score = calculate_score(&desired, &ss58);
		if score > best || desired.len() < 2 {
			best = score;
			if best >= top {
				println!("best: {} == top: {}", best, top);
				return Ok(format_seed::<Pair>(seed.clone()));
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


#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::{crypto::Ss58Codec, Pair};
	use sp_core::sr25519;
	#[cfg(feature = "bench")]
	use test::Bencher;

	#[test]
	fn test_generation_with_single_char() {
		let seed = generate_key::<sr25519::Pair>("j").unwrap();
		assert!(
			sr25519::Pair::from_seed_slice(&hex::decode(&seed[2..]).unwrap())
				.unwrap()
				.public()
				.to_ss58check()
				.contains("j"));
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
