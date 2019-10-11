// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! A utility to easily create a testnet chain spec definition with a given set
//! of authorities and endowed accounts and/or generate random accounts.

use structopt::StructOpt;

use primitives::crypto::Ss58Codec;
use node_cli::chain_spec::{self, AccountId};

#[derive(StructOpt)]
#[structopt(rename_all = "kebab-case")]
enum ChainSpecBuilder {
	/// Create a new chain spec with the given authorities, endowed and root
	/// accounts.
	New {
		/// Authority key seed.
		#[structopt(long, short, required = true)]
		authority_seeds: Vec<String>,
		/// Endowed account address (SS58 format).
		#[structopt(long, short)]
		endowed_accounts: Vec<String>,
		/// Root account address (SS58 format).
		#[structopt(long, short)]
		root_account: String,
	},
}

fn genesis_constructor(
	authority_seeds: &[String],
	endowed_accounts: &[AccountId],
	root_account: &AccountId,
) -> chain_spec::GenesisConfig {
	let authorities = authority_seeds
		.iter()
		.map(AsRef::as_ref)
		.map(chain_spec::get_authority_keys_from_seed)
		.collect::<Vec<_>>();

	let enable_println = true;

	chain_spec::testnet_genesis(
		authorities,
		root_account.clone(),
		Some(endowed_accounts.to_vec()),
		enable_println,
	)
}

fn generate_chain_spec() -> Result<String, String> {
	let builder = ChainSpecBuilder::from_args();

	let ChainSpecBuilder::New {
		authority_seeds,
		endowed_accounts,
		root_account,
		..
	} = builder;

	let parse_account = |address: &String| {
		AccountId::from_string(address)
			.map_err(|err| format!("Failed to parse account address: {:?}", err))
	};

	let endowed_accounts = endowed_accounts
		.iter()
		.map(parse_account)
		.collect::<Result<Vec<_>, String>>()?;

	let root_account = parse_account(&root_account)?;

	let chain_spec = chain_spec::ChainSpec::from_genesis(
		"Custom",
		"custom",
		move || genesis_constructor(&authority_seeds, &endowed_accounts, &root_account),
		vec![],
		None,
		None,
		None,
		Default::default(),
	);

	chain_spec.to_json(false).map_err(|err| format!("{}", err))
}

fn main() {
	let json = generate_chain_spec().unwrap();
	println!("{}", json);
}
