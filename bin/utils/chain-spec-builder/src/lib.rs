// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate's chain spec builder utility.
//!
//! A chain-spec is short for `chain-configuration`. See the [`sc-chain-spec`] for more information.
//!
//! Note that this binary is analogous to the `build-spec` subcommand, contained in typical
//! substrate-based nodes. This particular binary is capable of building a more sophisticated chain
//! specification that can be used with the substrate-node, ie. [`node-cli`].
//!
//! See [`ChainSpecBuilder`] for a list of available commands.
//!
//! [`sc-chain-spec`]: ../sc_chain_spec/index.html
//! [`node-cli`]: ../node_cli/index.html

use std::path::{Path, PathBuf};

use ansi_term::Style;
use clap::Parser;

use node_cli::chain_spec::{self, AccountId};
use sc_keystore::LocalKeystore;
use sp_core::crypto::{ByteArray, Ss58Codec};
use sp_keystore::KeystorePtr;

/// A utility to easily create a testnet chain spec definition with a given set
/// of authorities and endowed accounts and/or generate random accounts.
#[derive(Parser)]
#[command(rename_all = "kebab-case")]
pub enum ChainSpecBuilder {
	/// Create a new chain spec with the given authorities, endowed and sudo
	/// accounts.
	New {
		/// Authority key seed.
		#[arg(long, short, required = true)]
		authority_seeds: Vec<String>,
		/// Active nominators (SS58 format), each backing a random subset of the aforementioned
		/// authorities.
		#[arg(long, short, default_value = "0")]
		nominator_accounts: Vec<String>,
		/// Endowed account address (SS58 format).
		#[arg(long, short)]
		endowed_accounts: Vec<String>,
		/// Sudo account address (SS58 format).
		#[arg(long, short)]
		sudo_account: String,
		/// The path where the chain spec should be saved.
		#[arg(long, short, default_value = "./chain_spec.json")]
		chain_spec_path: PathBuf,
	},
	/// Create a new chain spec with the given number of authorities and endowed
	/// accounts. Random keys will be generated as required.
	Generate {
		/// The number of authorities.
		#[arg(long, short)]
		authorities: usize,
		/// The number of nominators backing the aforementioned authorities.
		///
		/// Will nominate a random subset of `authorities`.
		#[arg(long, short, default_value_t = 0)]
		nominators: usize,
		/// The number of endowed accounts.
		#[arg(long, short, default_value_t = 0)]
		endowed: usize,
		/// The path where the chain spec should be saved.
		#[arg(long, short, default_value = "./chain_spec.json")]
		chain_spec_path: PathBuf,
		/// Path to use when saving generated keystores for each authority.
		///
		/// At this path, a new folder will be created for each authority's
		/// keystore named `auth-$i` where `i` is the authority index, i.e.
		/// `auth-0`, `auth-1`, etc.
		#[arg(long, short)]
		keystore_path: Option<PathBuf>,
	},
}

impl ChainSpecBuilder {
	/// Returns the path where the chain spec should be saved.
	pub fn chain_spec_path(&self) -> &Path {
		match self {
			ChainSpecBuilder::New { chain_spec_path, .. } => chain_spec_path.as_path(),
			ChainSpecBuilder::Generate { chain_spec_path, .. } => chain_spec_path.as_path(),
		}
	}
}

fn genesis_constructor(
	authority_seeds: &[String],
	nominator_accounts: &[AccountId],
	endowed_accounts: &[AccountId],
	sudo_account: &AccountId,
) -> chain_spec::RuntimeGenesisConfig {
	let authorities = authority_seeds
		.iter()
		.map(AsRef::as_ref)
		.map(chain_spec::authority_keys_from_seed)
		.collect::<Vec<_>>();

	chain_spec::testnet_genesis(
		authorities,
		nominator_accounts.to_vec(),
		sudo_account.clone(),
		Some(endowed_accounts.to_vec()),
	)
}

/// Generate the chain spec using the given seeds and accounts.
pub fn generate_chain_spec(
	authority_seeds: Vec<String>,
	nominator_accounts: Vec<String>,
	endowed_accounts: Vec<String>,
	sudo_account: String,
) -> Result<String, String> {
	let parse_account = |address: String| {
		AccountId::from_string(&address)
			.map_err(|err| format!("Failed to parse account address: {:?}", err))
	};

	let nominator_accounts = nominator_accounts
		.into_iter()
		.map(parse_account)
		.collect::<Result<Vec<_>, String>>()?;

	let endowed_accounts = endowed_accounts
		.into_iter()
		.map(parse_account)
		.collect::<Result<Vec<_>, String>>()?;

	let sudo_account = parse_account(sudo_account)?;

	let chain_spec = chain_spec::ChainSpec::from_genesis(
		"Custom",
		"custom",
		sc_chain_spec::ChainType::Live,
		move || {
			genesis_constructor(
				&authority_seeds,
				&nominator_accounts,
				&endowed_accounts,
				&sudo_account,
			)
		},
		vec![],
		None,
		None,
		None,
		None,
		Default::default(),
	);

	chain_spec.as_json(false)
}

/// Generate the authority keys and store them in the given `keystore_path`.
pub fn generate_authority_keys_and_store(
	seeds: &[String],
	keystore_path: &Path,
) -> Result<(), String> {
	for (n, seed) in seeds.iter().enumerate() {
		let keystore: KeystorePtr =
			LocalKeystore::open(keystore_path.join(format!("auth-{}", n)), None)
				.map_err(|err| err.to_string())?
				.into();

		let (_, _, grandpa, babe, im_online, authority_discovery) =
			chain_spec::authority_keys_from_seed(seed);

		let insert_key = |key_type, public| {
			keystore
				.insert(key_type, &format!("//{}", seed), public)
				.map_err(|_| format!("Failed to insert key: {}", grandpa))
		};

		insert_key(sp_core::crypto::key_types::BABE, babe.as_slice())?;

		insert_key(sp_core::crypto::key_types::GRANDPA, grandpa.as_slice())?;

		insert_key(sp_core::crypto::key_types::IM_ONLINE, im_online.as_slice())?;

		insert_key(
			sp_core::crypto::key_types::AUTHORITY_DISCOVERY,
			authority_discovery.as_slice(),
		)?;
	}

	Ok(())
}

/// Print the given seeds
pub fn print_seeds(
	authority_seeds: &[String],
	nominator_seeds: &[String],
	endowed_seeds: &[String],
	sudo_seed: &str,
) {
	let header = Style::new().bold().underline();
	let entry = Style::new().bold();

	println!("{}", header.paint("Authority seeds"));

	for (n, seed) in authority_seeds.iter().enumerate() {
		println!("{} //{}", entry.paint(format!("auth-{}:", n)), seed);
	}

	println!("{}", header.paint("Nominator seeds"));

	for (n, seed) in nominator_seeds.iter().enumerate() {
		println!("{} //{}", entry.paint(format!("nom-{}:", n)), seed);
	}

	println!();

	if !endowed_seeds.is_empty() {
		println!("{}", header.paint("Endowed seeds"));
		for (n, seed) in endowed_seeds.iter().enumerate() {
			println!("{} //{}", entry.paint(format!("endowed-{}:", n)), seed);
		}

		println!();
	}

	println!("{}", header.paint("Sudo seed"));
	println!("//{}", sudo_seed);
}
