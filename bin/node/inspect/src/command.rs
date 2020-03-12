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
};

use crate::cli::{InspectCmd, InspectSubCmd};
use crate::{Inspector, PrettyPrinter};

impl InspectCmd {
	/// Initialize
	pub fn init(&self, version: &sc_cli::VersionInfo) -> sc_cli::Result<()> {
		self.shared_params.init(version)
	}

	/// Parse CLI arguments and initialize given config.
	pub fn update_config(
		&self,
		mut config: &mut sc_service::config::Configuration,
		spec_factory: impl FnOnce(&str) -> Result<Box<dyn sc_service::ChainSpec>, String>,
		version: &sc_cli::VersionInfo,
	) -> sc_cli::Result<()> {
		self.shared_params.update_config(config, spec_factory, version)?;

		// make sure to configure keystore
		config.use_in_memory_keystore()?;

		// and all import params (especially pruning that has to match db meta)
		self.import_params.update_config(
			&mut config,
			sc_service::Roles::FULL,
			self.shared_params.dev,
		)?;

		Ok(())
	}

	/// Run the inspect command, passing the inspector.
	pub fn run<B, P>(
		self,
		inspect: Inspector<B, P>,
	) -> sc_cli::Result<()> where
		B: sp_runtime::traits::Block,
		B::Hash: FromStr,
		P: PrettyPrinter<B>,
	{
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

	fn from_str(s: &str) -> Result<Self, Self::Err> {
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

	fn from_str(s: &str) -> Result<Self, Self::Err> {
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
