// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Command ran by the CLI

use std::{
	fmt::Debug,
	str::FromStr,
	path::PathBuf,
};

use crate::cli::{InspectCmd, InspectSubCmd};
use crate::Inspector;
use sc_service::{
	Configuration, NativeExecutionDispatch, RuntimeGenesis, ChainSpecExtension,
	config::{DatabaseConfig, ExecutionStrategies, WasmExecutionMethod}, ChainSpec, new_full_client,
	PruningMode, Roles, TracingReceiver,
};
use sc_cli::{SubstrateCLI, Result, CliConfiguration};
use sp_runtime::traits::Block;

impl InspectCmd {
	/// Run the inspect command, passing the inspector.
	pub fn run<B, RA, EX, G, E>(
		self,
		config: Configuration<G, E>,
	) -> Result<()> where
		B: Block,
		B::Hash: FromStr,
		RA: Send + Sync + 'static,
		EX: NativeExecutionDispatch + 'static,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let client = new_full_client::<B, RA, EX, _, _>(&config)?;
		let inspect = Inspector::<B>::new(client);

		match self.command {
			InspectSubCmd::Block { input } => {
				let input = input.parse()?;
				let res = inspect.block(input)
					.map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			},
			InspectSubCmd::Extrinsic { input } => {
				let input = input.parse()?;
				let res = inspect.extrinsic(input)
					.map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			},
		}
	}
}

impl CliConfiguration for InspectCmd {
	fn is_dev(&self) -> bool {
		self.shared_params.dev
	}

	fn get_base_path(&self) -> Option<&PathBuf> {
		self.shared_params.base_path.as_ref()
	}

	fn get_database_config(&self, base_path: &PathBuf, cache_size: Option<usize>) -> DatabaseConfig
	{
		self.shared_params.get_database_config(base_path, cache_size)
	}

	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.get_chain_spec::<C, G, E>()
	}

	fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.init::<C, G, E>()
	}

	fn get_pruning(&self, is_dev: bool, roles: Roles) -> Result<PruningMode> {
		self.import_params.get_pruning(roles, is_dev)
	}

	fn get_tracing_receiver(&self) -> TracingReceiver {
		self.import_params.tracing_receiver.clone().into()
	}

	fn get_tracing_targets(&self) -> Option<String> {
		self.import_params.tracing_targets.clone().into()
	}

	fn get_state_cache_size(&self) -> usize {
		self.import_params.state_cache_size
	}

	fn get_wasm_method(&self) -> WasmExecutionMethod {
		self.import_params.get_wasm_method()
	}

	fn get_execution_strategies(&self, is_dev: bool) -> Result<ExecutionStrategies> {
		self.import_params.get_execution_strategies(is_dev)
	}

	fn get_database_cache_size(&self) -> Option<usize> {
		self.import_params.database_cache_size
	}

}

// TODO: move out all of this
/// A block to retrieve.
#[derive(Debug, Clone, PartialEq)]
pub enum BlockAddress<Hash, Number> {
	/// Get block by hash.
	Hash(Hash),
	/// Get block by number.
	Number(Number),
	/// Raw SCALE-encoded bytes.
	Bytes(Vec<u8>),
}

impl<Hash: FromStr, Number: FromStr> FromStr for BlockAddress<Hash, Number> {
	type Err = String;

	fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
		// try to parse hash first
		if let Ok(hash) = s.parse() {
			return Ok(Self::Hash(hash))
		}

		// then number
		if let Ok(number) = s.parse() {
			return Ok(Self::Number(number))
		}

		// then assume it's bytes (hex-encoded)
		sp_core::bytes::from_hex(s)
			.map(Self::Bytes)
			.map_err(|e| format!(
				"Given string does not look like hash or number. It could not be parsed as bytes either: {}",
				e
			))
	}
}

/// An extrinsic address to decode and print out.
#[derive(Debug, Clone, PartialEq)]
pub enum ExtrinsicAddress<Hash, Number> {
	/// Extrinsic as part of existing block.
	Block(BlockAddress<Hash, Number>, usize),
	/// Raw SCALE-encoded extrinsic bytes.
	Bytes(Vec<u8>),
}

impl<Hash: FromStr + Debug, Number: FromStr + Debug> FromStr for ExtrinsicAddress<Hash, Number> {
	type Err = String;

	fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
		// first try raw bytes
		if let Ok(bytes) = sp_core::bytes::from_hex(s).map(Self::Bytes) {
			return Ok(bytes)
		}

		// split by a bunch of different characters
		let mut it = s.split(|c| c == '.' || c == ':' || c == ' ');
		let block = it.next()
			.expect("First element of split iterator is never empty; qed")
			.parse()?;

		let index = it.next()
			.ok_or_else(|| format!("Extrinsic index missing: example \"5:0\""))?
			.parse()
			.map_err(|e| format!("Invalid index format: {}", e))?;

		Ok(Self::Block(block, index))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::hash::H160 as Hash;

	#[test]
	fn should_parse_block_strings() {
		type BlockAddress = super::BlockAddress<Hash, u64>;

		let b0 = BlockAddress::from_str("3BfC20f0B9aFcAcE800D73D2191166FF16540258");
		let b1 = BlockAddress::from_str("1234");
		let b2 = BlockAddress::from_str("0");
		let b3 = BlockAddress::from_str("0x0012345f");


		assert_eq!(b0, Ok(BlockAddress::Hash(
			"3BfC20f0B9aFcAcE800D73D2191166FF16540258".parse().unwrap()
		)));
		assert_eq!(b1, Ok(BlockAddress::Number(1234)));
		assert_eq!(b2, Ok(BlockAddress::Number(0)));
		assert_eq!(b3, Ok(BlockAddress::Bytes(vec![0, 0x12, 0x34, 0x5f])));
	}

	#[test]
	fn should_parse_extrinsic_address() {
		type BlockAddress = super::BlockAddress<Hash, u64>;
		type ExtrinsicAddress = super::ExtrinsicAddress<Hash, u64>;

		let e0 = ExtrinsicAddress::from_str("1234");
		let b0 = ExtrinsicAddress::from_str("3BfC20f0B9aFcAcE800D73D2191166FF16540258:5");
		let b1 = ExtrinsicAddress::from_str("1234:0");
		let b2 = ExtrinsicAddress::from_str("0 0");
		let b3 = ExtrinsicAddress::from_str("0x0012345f");


		assert_eq!(e0, Err("Extrinsic index missing: example \"5:0\"".into()));
		assert_eq!(b0, Ok(ExtrinsicAddress::Block(
			BlockAddress::Hash("3BfC20f0B9aFcAcE800D73D2191166FF16540258".parse().unwrap()),
			5
		)));
		assert_eq!(b1, Ok(ExtrinsicAddress::Block(
			BlockAddress::Number(1234),
			0
		)));
		assert_eq!(b2, Ok(ExtrinsicAddress::Block(
			BlockAddress::Number(0),
			0
		)));
		assert_eq!(b3, Ok(ExtrinsicAddress::Bytes(vec![0, 0x12, 0x34, 0x5f])));
	}
}
