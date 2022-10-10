// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
mod database_params;
mod import_params;
mod keystore_params;
mod network_params;
mod node_key_params;
mod offchain_worker_params;
mod pruning_params;
mod shared_params;
mod transaction_pool_params;

use crate::arg_enums::{CryptoScheme, OutputType};
use sp_core::crypto::Ss58AddressFormat;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
};
use std::{convert::TryFrom, fmt::Debug, str::FromStr};
use structopt::StructOpt;

pub use crate::params::{
	database_params::*, import_params::*, keystore_params::*, network_params::*,
	node_key_params::*, offchain_worker_params::*, pruning_params::*, shared_params::*,
	transaction_pool_params::*,
};

/// Wrapper type of `String` that holds an unsigned integer of arbitrary size, formatted as a
/// decimal.
#[derive(Debug, Clone)]
pub struct GenericNumber(String);

impl FromStr for GenericNumber {
	type Err = String;

	fn from_str(block_number: &str) -> Result<Self, Self::Err> {
		if let Some(pos) = block_number.chars().position(|d| !d.is_digit(10)) {
			Err(format!("Expected block number, found illegal digit at position: {}", pos))
		} else {
			Ok(Self(block_number.to_owned()))
		}
	}
}

impl GenericNumber {
	/// Wrapper on top of `std::str::parse<N>` but with `Error` as a `String`
	///
	/// See `https://doc.rust-lang.org/std/primitive.str.html#method.parse` for more elaborate
	/// documentation.
	pub fn parse<N>(&self) -> Result<N, String>
	where
		N: FromStr,
		N::Err: std::fmt::Debug,
	{
		FromStr::from_str(&self.0).map_err(|e| format!("Failed to parse block number: {:?}", e))
	}
}

/// Wrapper type that is either a `Hash` or the number of a `Block`.
#[derive(Debug, Clone)]
pub struct BlockNumberOrHash(String);

impl FromStr for BlockNumberOrHash {
	type Err = String;

	fn from_str(block_number: &str) -> Result<Self, Self::Err> {
		if block_number.starts_with("0x") {
			if let Some(pos) = &block_number[2..].chars().position(|c| !c.is_ascii_hexdigit()) {
				Err(format!(
					"Expected block hash, found illegal hex character at position: {}",
					2 + pos,
				))
			} else {
				Ok(Self(block_number.into()))
			}
		} else {
			GenericNumber::from_str(block_number).map(|v| Self(v.0))
		}
	}
}

impl BlockNumberOrHash {
	/// Parse the inner value as `BlockId`.
	pub fn parse<B: BlockT>(&self) -> Result<BlockId<B>, String>
	where
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: std::fmt::Debug,
		NumberFor<B>: FromStr,
		<NumberFor<B> as FromStr>::Err: std::fmt::Debug,
	{
		if self.0.starts_with("0x") {
			Ok(BlockId::Hash(
				FromStr::from_str(&self.0[2..])
					.map_err(|e| format!("Failed to parse block hash: {:?}", e))?,
			))
		} else {
			GenericNumber(self.0.clone()).parse().map(BlockId::Number)
		}
	}
}

/// Optional flag for specifying crypto algorithm
#[derive(Debug, StructOpt, Clone)]
pub struct CryptoSchemeFlag {
	/// cryptography scheme
	#[structopt(
		long,
		value_name = "SCHEME",
		possible_values = &CryptoScheme::variants(),
		case_insensitive = true,
		default_value = "Sr25519"
	)]
	pub scheme: CryptoScheme,
}

/// Optional flag for specifying output type
#[derive(Debug, StructOpt, Clone)]
pub struct OutputTypeFlag {
	/// output format
	#[structopt(
		long,
		value_name = "FORMAT",
		possible_values = &OutputType::variants(),
		case_insensitive = true,
		default_value = "Text"
	)]
	pub output_type: OutputType,
}

/// Optional flag for specifying network scheme
#[derive(Debug, StructOpt, Clone)]
pub struct NetworkSchemeFlag {
	/// network address format
	#[structopt(
		long,
		value_name = "NETWORK",
		short = "n",
		possible_values = &Ss58AddressFormat::all_names()[..],
		parse(try_from_str = Ss58AddressFormat::try_from),
		case_insensitive = true,
	)]
	pub network: Option<Ss58AddressFormat>,
}

#[cfg(test)]
mod tests {
	use super::*;

	type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
	type Block = sp_runtime::generic::Block<Header, sp_runtime::OpaqueExtrinsic>;

	#[test]
	fn parse_block_number() {
		let block_number_or_hash = BlockNumberOrHash::from_str("1234").unwrap();
		let parsed = block_number_or_hash.parse::<Block>().unwrap();
		assert_eq!(BlockId::Number(1234), parsed);
	}

	#[test]
	fn parse_block_hash() {
		let hash = sp_core::H256::default();
		let hash_str = format!("{:?}", hash);
		let block_number_or_hash = BlockNumberOrHash::from_str(&hash_str).unwrap();
		let parsed = block_number_or_hash.parse::<Block>().unwrap();
		assert_eq!(BlockId::Hash(hash), parsed);
	}

	#[test]
	fn parse_block_hash_fails() {
		assert_eq!(
			"Expected block hash, found illegal hex character at position: 2",
			BlockNumberOrHash::from_str("0xHello").unwrap_err(),
		);
	}

	#[test]
	fn parse_block_number_fails() {
		assert_eq!(
			"Expected block number, found illegal digit at position: 3",
			BlockNumberOrHash::from_str("345Hello").unwrap_err(),
		);
	}
}
