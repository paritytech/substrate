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
	generate_authority_keys_and_store, generate_chain_spec, generate_chain_spec_for_runtime,
	print_seeds, ChainSpecBuilder, ChainSpecBuilderCmd, EditCmd, GenerateCmd, NewCmd, VerifyCmd,
};
use clap::Parser;
use node_cli::chain_spec;
use rand::{distributions::Alphanumeric, rngs::OsRng, Rng};
use sc_chain_spec::GenericChainSpec;
use sp_core::{crypto::Ss58Codec, sr25519};
use std::fs;

fn main() -> Result<(), String> {
	sp_tracing::try_init_simple();

	let builder = ChainSpecBuilder::parse();
	#[cfg(build_type = "debug")]
	if matches!(builder.command, ChainSpecBuilderCmd::Generate(_) | ChainSpecBuilderCmd::New(_)) {
		println!(
			"The chain spec builder builds a chain specification that includes a Substrate runtime \
		 compiled as WASM. To ensure proper functioning of the included runtime compile (or run) \
		 the chain spec builder binary in `--release` mode.\n",
		 );
	}

	let chain_spec_path = builder.chain_spec_path.to_path_buf();
	let mut write_chain_spec = true;

	let chain_spec_json = match builder.command {
		ChainSpecBuilderCmd::Generate(GenerateCmd {
			authorities,
			nominators,
			endowed,
			keystore_path,
		}) => {
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

			generate_chain_spec(authority_seeds, nominator_accounts, endowed_accounts, sudo_account)
		},
		ChainSpecBuilderCmd::New(NewCmd {
			authority_seeds,
			nominator_accounts,
			endowed_accounts,
			sudo_account,
		}) =>
			generate_chain_spec(authority_seeds, nominator_accounts, endowed_accounts, sudo_account),
		ChainSpecBuilderCmd::Runtime(cmd) => generate_chain_spec_for_runtime(&cmd),
		ChainSpecBuilderCmd::Edit(EditCmd {
			ref input_chain_spec,
			ref runtime_wasm_path,
			convert_to_raw,
		}) => {
			let mut chain_spec = GenericChainSpec::<()>::from_json_file(input_chain_spec.clone())?;
			runtime_wasm_path.clone().and_then(|path| {
				chain_spec
					.set_code(&fs::read(path.as_path()).expect("wasm blob file is readable")[..])
					.into()
			});

			chain_spec.as_json(convert_to_raw)
		},
		ChainSpecBuilderCmd::Verify(VerifyCmd { ref input_chain_spec, ref runtime_wasm_path }) => {
			write_chain_spec = false;
			let mut chain_spec = GenericChainSpec::<()>::from_json_file(input_chain_spec.clone())?;
			runtime_wasm_path.clone().and_then(|path| {
				chain_spec
					.set_code(&fs::read(path.as_path()).expect("wasm blob file is readable")[..])
					.into()
			});
			chain_spec.as_json(true)
		},
	}?;

	if write_chain_spec {
		fs::write(chain_spec_path, chain_spec_json).map_err(|err| err.to_string())
	} else {
		Ok(())
	}
}
