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

use chain_spec_builder::{
	generate_authority_keys_and_store, generate_chain_spec, print_seeds, ChainSpecBuilder,
};
use clap::Parser;
use node_cli::chain_spec;
use rand::{distributions::Alphanumeric, rngs::OsRng, Rng};
use sp_core::{crypto::Ss58Codec, sr25519};
use std::fs;

fn main() -> Result<(), String> {
	#[cfg(build_type = "debug")]
	println!(
		"The chain spec builder builds a chain specification that includes a Substrate runtime \
		 compiled as WASM. To ensure proper functioning of the included runtime compile (or run) \
		 the chain spec builder binary in `--release` mode.\n",
	);

	let builder = ChainSpecBuilder::parse();
	let chain_spec_path = builder.chain_spec_path().to_path_buf();

	let (authority_seeds, nominator_accounts, endowed_accounts, sudo_account) = match builder {
		ChainSpecBuilder::Generate { authorities, nominators, endowed, keystore_path, .. } => {
			let authorities = authorities.max(1);
			let rand_str = || -> String {
				OsRng.sample_iter(&Alphanumeric).take(32).map(char::from).collect()
			};

			let authority_seeds = (0..authorities).map(|_| rand_str()).collect::<Vec<_>>();
			let nominator_seeds = (0..nominators).map(|_| rand_str()).collect::<Vec<_>>();
			let endowed_seeds = (0..endowed).map(|_| rand_str()).collect::<Vec<_>>();
			let sudo_seed = rand_str();

			print_seeds(&authority_seeds, &nominator_seeds, &endowed_seeds, &sudo_seed);

			if let Some(keystore_path) = keystore_path {
				generate_authority_keys_and_store(&authority_seeds, &keystore_path)?;
			}

			let nominator_accounts = nominator_seeds
				.into_iter()
				.map(|seed| {
					chain_spec::get_account_id_from_seed::<sr25519::Public>(&seed).to_ss58check()
				})
				.collect();

			let endowed_accounts = endowed_seeds
				.into_iter()
				.map(|seed| {
					chain_spec::get_account_id_from_seed::<sr25519::Public>(&seed).to_ss58check()
				})
				.collect();

			let sudo_account =
				chain_spec::get_account_id_from_seed::<sr25519::Public>(&sudo_seed).to_ss58check();

			(authority_seeds, nominator_accounts, endowed_accounts, sudo_account)
		},
		ChainSpecBuilder::New {
			authority_seeds,
			nominator_accounts,
			endowed_accounts,
			sudo_account,
			..
		} => (authority_seeds, nominator_accounts, endowed_accounts, sudo_account),
	};

	let json =
		generate_chain_spec(authority_seeds, nominator_accounts, endowed_accounts, sudo_account)?;

	fs::write(chain_spec_path, json).map_err(|err| err.to_string())
}
