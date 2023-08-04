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

use std::{
	fs,
	path::{Path, PathBuf},
};

use ansi_term::Style;
use clap::{Parser, Subcommand};
use sc_chain_spec::GenesisConfigBuilderRuntimeCaller;

use node_cli::chain_spec::{self, AccountId};
use sc_keystore::LocalKeystore;
use serde_json::Value;
use sp_core::crypto::{ByteArray, Ss58Codec};
use sp_keystore::KeystorePtr;

/// A utility to easily create a testnet chain spec definition with a given set
/// of authorities and endowed accounts and/or generate random accounts.
#[derive(Debug, Parser)]
#[command(rename_all = "kebab-case")]
pub struct ChainSpecBuilder {
	#[command(subcommand)]
	pub command: ChainSpecBuilderCmd,
	/// The path where the chain spec should be saved.
	#[arg(long, short, default_value = "./chain_spec.json")]
	pub chain_spec_path: PathBuf,
}

#[derive(Debug, Subcommand)]
#[command(rename_all = "kebab-case")]
pub enum ChainSpecBuilderCmd {
	New(NewCmd),
	Generate(GenerateCmd),
	Runtime(RuntimeCmd),
	Edit(EditCmd),
	Verify(VerifyCmd),
}

/// Create a new chain spec with the given authorities, endowed and sudo
/// accounts. Only works for kitchen-sink runtime
#[derive(Parser, Debug)]
#[command(rename_all = "kebab-case")]
pub struct NewCmd {
	/// Authority key seed.
	#[arg(long, short, required = true)]
	pub authority_seeds: Vec<String>,
	/// Active nominators (SS58 format), each backing a random subset of the aforementioned
	/// authorities.
	#[arg(long, short, default_value = "0")]
	pub nominator_accounts: Vec<String>,
	/// Endowed account address (SS58 format).
	#[arg(long, short)]
	pub endowed_accounts: Vec<String>,
	/// Sudo account address (SS58 format).
	#[arg(long, short)]
	pub sudo_account: String,
}

/// Create a new chain spec with the given number of authorities and endowed
/// accounts. Random keys will be generated as required.
#[derive(Parser, Debug)]
pub struct GenerateCmd {
	/// The number of authorities.
	#[arg(long, short)]
	pub authorities: usize,
	/// The number of nominators backing the aforementioned authorities.
	///
	/// Will nominate a random subset of `authorities`.
	#[arg(long, short, default_value_t = 0)]
	pub nominators: usize,
	/// The number of endowed accounts.
	#[arg(long, short, default_value_t = 0)]
	pub endowed: usize,
	/// Path to use when saving generated keystores for each authority.
	///
	/// At this path, a new folder will be created for each authority's
	/// keystore named `auth-$i` where `i` is the authority index, i.e.
	/// `auth-0`, `auth-1`, etc.
	#[arg(long, short)]
	pub keystore_path: Option<PathBuf>,
}

/// Create a new chain spec by interacting with the provided runtime wasm blob.
#[derive(Parser, Debug)]
pub struct RuntimeCmd {
	/// The name of chain
	#[arg(long, short = 'n', default_value = "Custom")]
	chain_name: String,
	/// The chain id
	#[arg(long, short = 'i', default_value = "custom")]
	chain_id: String,
	/// The path to runtime wasm blob
	#[arg(long, short)]
	runtime_wasm_path: PathBuf,
	/// Export chainspec as raw storage
	#[arg(long, short = 's')]
	raw_storage: bool,
	/// Verify the genesis config. This silently generates the raw storage from genesis config. Any
	/// errors will be reported.
	#[arg(long, short = 'v')]
	verify: bool,
	#[command(subcommand)]
	action: GenesisBuildAction,
}

#[derive(Subcommand, Debug, Clone)]
enum GenesisBuildAction {
	Patch(PatchCmd),
	Full(FullCmd),
	Default(DefaultCmd),
}

/// Patches the runtime's default genesis config with provided patch.
#[derive(Parser, Debug, Clone)]
struct PatchCmd {
	/// The path to the runtime genesis config patch.
	#[arg(long, short)]
	patch_path: PathBuf,
}

/// Build the genesis config for runtime using provided json file. No defaults will be used.
#[derive(Parser, Debug, Clone)]
struct FullCmd {
	/// The path to the full runtime genesis config json file.
	#[arg(long, short)]
	config_path: PathBuf,
}

/// Gets the default genesis config for the runtime and uses it in ChainSpec. Please note that
/// default genesis config may not be valid. For some runtimes initial values should be added there
/// (e.g. session keys, babe epoch).
#[derive(Parser, Debug, Clone)]
struct DefaultCmd {
	#[arg(long, short)]
	/// If provided stores the default genesis config json file at given path (in addition to
	/// chain-spec).
	default_config_path: Option<PathBuf>,
}

/// Edits provided input chain spec. Input can be converted into raw storage chain-spec. The code
/// can be updated with the runtime provided in the command line.
#[derive(Parser, Debug, Clone)]
pub struct EditCmd {
	#[arg(long, short)]
	/// Chain spec to be edited
	pub input_chain_spec: PathBuf,
	/// The path to new runtime wasm blob to be stored into chain-spec
	#[arg(long, short = 'r')]
	pub runtime_wasm_path: Option<PathBuf>,
	/// Convert genesis spec to raw format
	#[arg(long, short = 's')]
	pub convert_to_raw: bool,
}

/// Verifies provided input chain spec. If the runtime is provided verification is performed against
/// new runtime.
#[derive(Parser, Debug, Clone)]
pub struct VerifyCmd {
	#[arg(long, short)]
	/// Chain spec to be edited
	pub input_chain_spec: PathBuf,
	/// The path to new runtime wasm blob to be stored into chain-spec
	#[arg(long, short = 'r')]
	pub runtime_wasm_path: Option<PathBuf>,
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

	let authorities = authority_seeds
		.iter()
		.map(AsRef::as_ref)
		.map(chain_spec::authority_keys_from_seed)
		.collect::<Vec<_>>();

	chain_spec::ChainSpec::builder()
		.with_name("Custom")
		.with_id("custom")
		.with_chain_type(sc_chain_spec::ChainType::Live)
		.with_genesis_config_patch(chain_spec::testnet_genesis(
			authorities,
			nominator_accounts,
			sudo_account,
			Some(endowed_accounts),
		))
		.with_extensions(Default::default())
		.with_code(kitchensink_runtime::wasm_binary_unwrap())
		.build()
		.as_json(false)
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

/// Processes `RuntimeCmd` and returns JSON version of `ChainSpec`
pub fn generate_chain_spec_for_runtime(cmd: &RuntimeCmd) -> Result<String, String> {
	let code = fs::read(cmd.runtime_wasm_path.as_path()).expect("wasm blob file is readable");

	let builder = chain_spec::ChainSpec::builder()
		.with_name(&cmd.chain_name[..])
		.with_id(&cmd.chain_id[..])
		.with_chain_type(sc_chain_spec::ChainType::Live)
		.with_extensions(Default::default())
		.with_code(&code[..]);

	let builder = match cmd.action {
		GenesisBuildAction::Patch(PatchCmd { ref patch_path }) => {
			let patch = fs::read(patch_path.as_path())
				.map_err(|e| format!("patch file {patch_path:?} shall be readable: {e}"))?;
			builder.with_genesis_config_patch(serde_json::from_slice::<Value>(&patch[..]).map_err(
				|e| format!("patch file {patch_path:?} shall contain a valid json: {e}"),
			)?)
		},
		GenesisBuildAction::Full(FullCmd { ref config_path }) => {
			let config = fs::read(config_path.as_path())
				.map_err(|e| format!("config file {config_path:?} shall be readable: {e}"))?;
			builder.with_genesis_config(serde_json::from_slice::<Value>(&config[..]).map_err(
				|e| format!("config file {config_path:?} shall contain a valid json: {e}"),
			)?)
		},
		GenesisBuildAction::Default(DefaultCmd { ref default_config_path }) => {
			let caller = GenesisConfigBuilderRuntimeCaller::new(&code[..]);
			let default_config = caller
				.get_default_config()
				.expect("getting default config from runtime should work");
			default_config_path.clone().map(|path| {
				fs::write(path.as_path(), serde_json::to_string_pretty(&default_config).unwrap())
					.map_err(|err| err.to_string())
			});
			builder.with_genesis_config(default_config)
		},
	};

	let chain_spec = builder.build();

	match (cmd.verify, cmd.raw_storage) {
		(_, true) => chain_spec.as_json(true),
		(true, false) => {
			chain_spec.as_json(true)?;
			println!("Genesis config verification: OK");
			chain_spec.as_json(false)
		},
		(false, false) => chain_spec.as_json(false),
	}
}
