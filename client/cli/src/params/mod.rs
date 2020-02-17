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

use std::{
	str::FromStr, path::PathBuf, convert::TryInto,
};
use hex_literal::hex;
use structopt::{StructOpt, clap::arg_enum};
use std::fmt::Debug;
use std::io::{Read, Seek};
use sp_core::{
	crypto::{Ss58AddressFormat, Ss58Codec},
	Pair, Public, hexdisplay::HexDisplay,
};
use sp_runtime::traits::{Verify, IdentifyAccount};
use serde_json::json;
use crate::error::{Error, self};

mod import_blocks;
mod export_blocks;
mod check_block;
mod build_spec;
mod benchmark;
mod revert;
mod run;
mod subcommand;
mod purge_chain;
mod generate;
mod generate_node_key;
mod inspect;
mod sign;
mod sign_transaction;

pub use import_blocks::*;
pub use export_blocks::*;
pub use benchmark::*;
pub use build_spec::*;
pub use check_block::*;
pub use revert::*;
pub use run::*;
pub use subcommand::*;
pub use purge_chain::*;
pub use generate::*;
pub use generate_node_key::*;
pub use inspect::*;
pub use sign::*;
pub use sign_transaction::*;

pub use crate::execution_strategy::ExecutionStrategy;
use sp_runtime::MultiSignature;

impl Into<sc_client_api::ExecutionStrategy> for ExecutionStrategy {
	fn into(self) -> sc_client_api::ExecutionStrategy {
		match self {
			ExecutionStrategy::Native => sc_client_api::ExecutionStrategy::NativeWhenPossible,
			ExecutionStrategy::Wasm => sc_client_api::ExecutionStrategy::AlwaysWasm,
			ExecutionStrategy::Both => sc_client_api::ExecutionStrategy::Both,
			ExecutionStrategy::NativeElseWasm => sc_client_api::ExecutionStrategy::NativeElseWasm,
		}
	}
}

arg_enum! {
	/// How to execute Wasm runtime code
	#[allow(missing_docs)]
	#[derive(Debug, Clone, Copy)]
	pub enum WasmExecutionMethod {
		// Uses an interpreter.
		Interpreted,
		// Uses a compiled runtime.
		Compiled,
	}
}

impl WasmExecutionMethod {
	/// Returns list of variants that are not disabled by feature flags.
	fn enabled_variants() -> Vec<&'static str> {
		Self::variants()
			.iter()
			.cloned()
			.filter(|&name| cfg!(feature = "wasmtime") || name != "Compiled")
			.collect()
	}
}

impl Into<sc_service::config::WasmExecutionMethod> for WasmExecutionMethod {
	fn into(self) -> sc_service::config::WasmExecutionMethod {
		match self {
			WasmExecutionMethod::Interpreted => sc_service::config::WasmExecutionMethod::Interpreted,
			#[cfg(feature = "wasmtime")]
			WasmExecutionMethod::Compiled => sc_service::config::WasmExecutionMethod::Compiled,
			#[cfg(not(feature = "wasmtime"))]
			WasmExecutionMethod::Compiled => panic!(
				"Substrate must be compiled with \"wasmtime\" feature for compiled Wasm execution"
			),
		}
	}
}

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, StructOpt, Clone)]
#[structopt(rename_all = "kebab-case")]
pub struct SharedParams {
	/// Specify the chain specification (one of dev, local or staging).
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain.
	#[structopt(long)]
	pub dev: bool,

	/// Specify custom base path.
	#[structopt(long, short = "d", value_name = "PATH", parse(from_os_str))]
	pub base_path: Option<PathBuf>,

	/// Sets a custom logging filter.
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	pub log: Option<String>,

	/// output type
	#[structopt(
		long,
		value_name = "OUTPUT_TYPE",
		possible_values = &OutputType::variants(),
		case_insensitive = true,
		default_value = "Text"
	)]
	pub output_type: OutputType,

	/// network format
	#[structopt(
		long,
		value_name = "NETWORK",
		parse(try_from_str = parse_network),
	)]
	pub network: Option<Ss58AddressFormat>,
}

fn parse_network(network: &str) -> Result<Ss58AddressFormat, Error> {
	network.try_into()
		.map_err(|_| Error::Input("Invalid network name. See --help for available networks.".into()))
}

/// Wrapper type of `String` which holds an arbitary sized unsigned integer formatted as decimal.
#[derive(Debug, Clone)]
pub struct BlockNumber(String);

impl FromStr for BlockNumber {
	type Err = String;

	fn from_str(block_number: &str) -> Result<Self, Self::Err> {
		if block_number.chars().any(|d| !d.is_digit(10)) {
			Err(format!(
				"Invalid block number: {}, expected decimal formatted unsigned integer",
				block_number
			))
		} else {
			Ok(Self(block_number.to_owned()))
		}
	}
}

impl BlockNumber {
	/// Wrapper on top of `std::str::parse<N>` but with `Error` as a `String`
	///
	/// See `https://doc.rust-lang.org/std/primitive.str.html#method.parse` for more elaborate
	/// documentation.
	pub fn parse<N>(&self) -> Result<N, String>
		where
			N: FromStr,
			N::Err: std::fmt::Debug,
	{
		self.0
			.parse()
			.map_err(|e| format!("BlockNumber: {} parsing failed because of {:?}", self.0, e))
	}
}

#[derive(Debug, StructOpt, Clone)]
pub struct VerifyCmd {
	/// ...
	#[structopt(long)]
	uri: String,

	#[structopt(long)]
	hex: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

#[derive(Debug, StructOpt, Clone)]
pub struct InsertCmd {
	/// ...
	#[structopt(long)]
	node_url: Option<String>,

	/// ...
	#[structopt(long)]
	suri: Option<String>,

	#[structopt(long)]
	key_type: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

#[derive(Debug, StructOpt, Clone)]
pub struct TransferCmd {
	/// ...
	#[structopt(long)]
	from: Option<String>,

	/// ...
	#[structopt(long)]
	to: Option<String>,

	/// ...
	#[structopt(long)]
	index: Option<String>,

	/// ...
	#[structopt(long)]
	genesis: Option<String>,

	/// ...
	#[structopt(long)]
	amount: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// Internal trait used to cast to a dynamic type that implements Read and Seek.
pub trait ReadPlusSeek: Read + Seek {}

impl<T: Read + Seek> ReadPlusSeek for T {}

arg_enum! {
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	pub enum OutputType {
		Json,
		Text,
	}
}

pub type SignatureOf<C> = <<C as Crypto>::Pair as Pair>::Signature;
pub type PublicOf<C> = <<C as Crypto>::Pair as Pair>::Public;
pub type SeedOf<C> = <<C as Crypto>::Pair as Pair>::Seed;
pub type AccountPublic = <MultiSignature as Verify>::Signer;

pub trait IntoRuntimePublic: Sized + AsRef<[u8]> + Ss58Codec {
	/// Converts the public key into a runtime account public key, if possible. If not possible, bombs out.
	fn into_runtime(self) -> AccountPublic {
		panic!("This cryptography isn't supported for this runtime.")
	}
}

pub trait IntoRuntimeSignature: AsRef<[u8]> + AsMut<[u8]> + Default {
	/// Converts the signature into a runtime account signature, if possible. If not possible, bombs out.
	fn into_runtime(self) -> MultiSignature {
		panic!("This cryptography isn't supported for this runtime.")
	}
}

fn format_seed<C: Crypto>(seed: SeedOf<C>) -> String {
	format!("0x{}", HexDisplay::from(&seed.as_ref()))
}

fn format_public_key<C: Crypto>(public_key: PublicOf<C>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.as_ref()))
}

fn format_account_id<C: Crypto>(public_key: PublicOf<C>) -> String where
	PublicOf<C>: IntoRuntimePublic,
{
	format!("0x{}", HexDisplay::from(&public_key.into_runtime().into_account().as_ref()))
}

pub fn read_uri(uri: Option<String>) -> error::Result<String> {
	if let Some(uri) = uri {
		let file = PathBuf::from(uri);
		if file.is_file() {
			std::fs::read_to_string(uri)?
				.trim_end()
				.into()
		} else {
			uri.into()
		}
	} else {
		rpassword::read_password_from_tty(Some("URI: "))?
	}
}

pub fn decode_hex<T: AsRef<[u8]>>(message: T) -> Result<Vec<u8>, Error> {
	hex::decode(message).map_err(|e| Error::Formatted(format!("Invalid hex ({})", e)))
}

pub fn read_pair<C: Crypto>(
	matched_suri: Option<&str>,
	password: Option<&str>,
) -> Result<<C as Crypto>::Pair, Error> where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let suri = matched_suri.ok_or(Error::Static("parameter is required; thus it can't be None; qed"))?;
	Ok(C::pair_from_suri(suri, password))
}

pub fn read_message_from_stdin(should_decode: bool) -> Result<Vec<u8>, Error> {
	let mut message = vec![];
	std::io::stdin()
		.lock()
		.read_to_end(&mut message)?;
	if should_decode {
		message = decode_hex(&message)?;
	}
	Ok(message)
}

pub fn get_password(run_cmd: &RunCmd) -> error::Result<Option<String>> {
	let password_interactive = run_cmd.password_interactive;
	let password = run_cmd.password.as_ref();

	let pass = if password_interactive {
		Some(rpassword::read_password_from_tty(Some("Key password: "))?)
	} else {
		password.map(Into::into)
	};

	Ok(pass)
}

pub fn as_str(s: &Option<String>) -> Option<&str> {
	s.as_ref().map(String::as_ref)
}


pub trait Crypto: Sized {
	type Pair: Pair<Public = Self::Public>;
	type Public: IntoRuntimePublic + Public + Ss58Codec + AsRef<[u8]> + std::hash::Hash;

	fn pair_from_suri(suri: &str, password: Option<&str>) -> Self::Pair {
		Self::Pair::from_string(suri, password).expect("Invalid phrase")
	}

	fn ss58_from_pair(pair: &Self::Pair) -> String where
		<Self::Pair as Pair>::Public: IntoRuntimePublic,
	{
		pair.public().into_runtime().into_account().to_ss58check()
	}

	fn public_from_pair(pair: &Self::Pair) -> Self::Public {
		pair.public()
	}

	fn print_from_uri(
		uri: &str,
		password: Option<&str>,
		network_override: Option<Ss58AddressFormat>,
		output: OutputType,
	) where
		<Self::Pair as Pair>::Public: IntoRuntimePublic,
	{
		if let Ok((pair, seed)) = Self::Pair::from_phrase(uri, password) {
			let public_key = Self::public_from_pair(&pair);

			match output {
				OutputType::Json => {
					let json = json!({
						"secretPhrase": uri,
						"secretSeed": format_seed::<Self>(seed),
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret phrase `{}` is account:\n  \
						Secret seed:      {}\n  \
						Public key (hex): {}\n  \
						Account ID:       {}\n  \
						SS58 Address:     {}",
					         uri,
					         format_seed::<Self>(seed),
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key),
					         Self::ss58_from_pair(&pair),
					);
				},
			}
		} else if let Ok((pair, seed)) = Self::Pair::from_string_with_seed(uri, password) {
			let public_key = Self::public_from_pair(&pair);

			match output {
				OutputType::Json => {
					let json = json!({
						"secretKeyUri": uri,
						"secretSeed": if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret Key URI `{}` is account:\n  \
						Secret seed:      {}\n  \
						Public key (hex): {}\n  \
						Account ID:       {}\n  \
						SS58 Address:     {}",
					         uri,
					         if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key),
					         Self::ss58_from_pair(&pair),
					);
				},
			}

		} else if let Ok((public_key, v)) =
		<Self::Pair as Pair>::Public::from_string_with_version(uri)
		{
			let v = network_override.unwrap_or(v);

			match output {
				OutputType::Json => {
					let json = json!({
						"publicKeyUri": uri,
						"networkId": String::from(v),
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key.clone()),
						"ss58Address": public_key.to_ss58check_with_version(v),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Public Key URI `{}` is account:\n  \
						Network ID/version: {}\n  \
						Public key (hex):   {}\n  \
						Account ID:         {}\n  \
						SS58 Address:       {}",
					         uri,
					         String::from(v),
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key.clone()),
					         public_key.to_ss58check_with_version(v),
					);
				},
			}
		} else {
			println!("Invalid phrase/URI given");
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Debug, Clone, StructOpt)]
	struct Cmd {
		#[allow(missing_docs)]
		#[structopt(subcommand)]
		pub subcommand: Option<Subcommand>,
		#[allow(missing_docs)]
		#[structopt(flatten)]
		pub run: RunCmd,
	}

	#[test]
	fn subcommand() {
		let vec = vec!["cmd", "--password", "qwerty", "generate", "--words=12", "--output-type", "Json"];
		let cmd = Cmd::from_iter(vec);
		println!("{:#?}", cmd.subcommand)
	}
}