// This file is part of Substrate.
//
// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! A CLI extension for substrate node, adding sub-command to pretty print debug info
//! about blocks and extrinsics.
//!
//! The blocks and extrinsics can either be retrieved from the database (on-chain),
//! or a raw SCALE-encoding can be provided.

#![warn(missing_docs)]

pub mod cli;
pub mod command;

use codec::{Decode, Encode};
use sc_client_api::BlockBackend;
use sp_blockchain::HeaderBackend;
use sp_core::hexdisplay::HexDisplay;
use sp_runtime::{
	generic::BlockId,
	traits::{Block, Hash, HashFor, NumberFor},
};
use std::{fmt, fmt::Debug, marker::PhantomData, str::FromStr};

/// A helper type for a generic block input.
pub type BlockAddressFor<TBlock> =
	BlockAddress<<HashFor<TBlock> as Hash>::Output, NumberFor<TBlock>>;

/// A Pretty formatter implementation.
pub trait PrettyPrinter<TBlock: Block> {
	/// Nicely format block.
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result;
	/// Nicely format extrinsic.
	fn fmt_extrinsic(&self, fmt: &mut fmt::Formatter, extrinsic: &TBlock::Extrinsic)
		-> fmt::Result;
}

/// Default dummy debug printer.
#[derive(Default)]
pub struct DebugPrinter;
impl<TBlock: Block> PrettyPrinter<TBlock> for DebugPrinter {
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result {
		writeln!(fmt, "Header:")?;
		writeln!(fmt, "{:?}", block.header())?;
		writeln!(fmt, "Block bytes: {:?}", HexDisplay::from(&block.encode()))?;
		writeln!(fmt, "Extrinsics ({})", block.extrinsics().len())?;
		for (idx, ex) in block.extrinsics().iter().enumerate() {
			writeln!(fmt, "- {}:", idx)?;
			<DebugPrinter as PrettyPrinter<TBlock>>::fmt_extrinsic(self, fmt, ex)?;
		}
		Ok(())
	}

	fn fmt_extrinsic(
		&self,
		fmt: &mut fmt::Formatter,
		extrinsic: &TBlock::Extrinsic,
	) -> fmt::Result {
		writeln!(fmt, " {:#?}", extrinsic)?;
		writeln!(fmt, " Bytes: {:?}", HexDisplay::from(&extrinsic.encode()))?;
		Ok(())
	}
}

/// Aggregated error for `Inspector` operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Could not decode Block or Extrinsic.
	#[error(transparent)]
	Codec(#[from] codec::Error),
	/// Error accessing blockchain DB.
	#[error(transparent)]
	Blockchain(#[from] sp_blockchain::Error),
	/// Given block has not been found.
	#[error("{0}")]
	NotFound(String),
}

/// A helper trait to access block headers and bodies.
pub trait ChainAccess<TBlock: Block>: HeaderBackend<TBlock> + BlockBackend<TBlock> {}

impl<T, TBlock> ChainAccess<TBlock> for T
where
	TBlock: Block,
	T: sp_blockchain::HeaderBackend<TBlock> + sc_client_api::BlockBackend<TBlock>,
{
}

/// Blockchain inspector.
pub struct Inspector<TBlock: Block, TPrinter: PrettyPrinter<TBlock> = DebugPrinter> {
	printer: TPrinter,
	chain: Box<dyn ChainAccess<TBlock>>,
	_block: PhantomData<TBlock>,
}

impl<TBlock: Block, TPrinter: PrettyPrinter<TBlock>> Inspector<TBlock, TPrinter> {
	/// Create new instance of the inspector with default printer.
	pub fn new(chain: impl ChainAccess<TBlock> + 'static) -> Self
	where
		TPrinter: Default,
	{
		Self::with_printer(chain, Default::default())
	}

	/// Customize pretty-printing of the data.
	pub fn with_printer(chain: impl ChainAccess<TBlock> + 'static, printer: TPrinter) -> Self {
		Inspector { chain: Box::new(chain) as _, printer, _block: Default::default() }
	}

	/// Get a pretty-printed block.
	pub fn block(&self, input: BlockAddressFor<TBlock>) -> Result<String, Error> {
		struct BlockPrinter<'a, A, B>(A, &'a B);
		impl<'a, A: Block, B: PrettyPrinter<A>> fmt::Display for BlockPrinter<'a, A, B> {
			fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
				self.1.fmt_block(fmt, &self.0)
			}
		}

		let block = self.get_block(input)?;
		Ok(format!("{}", BlockPrinter(block, &self.printer)))
	}

	fn get_block(&self, input: BlockAddressFor<TBlock>) -> Result<TBlock, Error> {
		Ok(match input {
			BlockAddress::Bytes(bytes) => TBlock::decode(&mut &*bytes)?,
			BlockAddress::Number(number) => {
				let id = BlockId::number(number);
				let hash = self.chain.expect_block_hash_from_id(&id)?;
				let not_found = format!("Could not find block {:?}", id);
				let body = self
					.chain
					.block_body(hash)?
					.ok_or_else(|| Error::NotFound(not_found.clone()))?;
				let header =
					self.chain.header(id)?.ok_or_else(|| Error::NotFound(not_found.clone()))?;
				TBlock::new(header, body)
			},
			BlockAddress::Hash(hash) => {
				let id = BlockId::hash(hash);
				let not_found = format!("Could not find block {:?}", id);
				let body = self
					.chain
					.block_body(hash)?
					.ok_or_else(|| Error::NotFound(not_found.clone()))?;
				let header =
					self.chain.header(id)?.ok_or_else(|| Error::NotFound(not_found.clone()))?;
				TBlock::new(header, body)
			},
		})
	}

	/// Get a pretty-printed extrinsic.
	pub fn extrinsic(
		&self,
		input: ExtrinsicAddress<<HashFor<TBlock> as Hash>::Output, NumberFor<TBlock>>,
	) -> Result<String, Error> {
		struct ExtrinsicPrinter<'a, A: Block, B>(A::Extrinsic, &'a B);
		impl<'a, A: Block, B: PrettyPrinter<A>> fmt::Display for ExtrinsicPrinter<'a, A, B> {
			fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
				self.1.fmt_extrinsic(fmt, &self.0)
			}
		}

		let ext = match input {
			ExtrinsicAddress::Block(block, index) => {
				let block = self.get_block(block)?;
				block.extrinsics().get(index).cloned().ok_or_else(|| {
					Error::NotFound(format!(
						"Could not find extrinsic {} in block {:?}",
						index, block
					))
				})?
			},
			ExtrinsicAddress::Bytes(bytes) => TBlock::Extrinsic::decode(&mut &*bytes)?,
		};

		Ok(format!("{}", ExtrinsicPrinter(ext, &self.printer)))
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
		sp_core::bytes::from_hex(s).map(Self::Bytes).map_err(|e| {
			format!(
				"Given string does not look like hash or number. It could not be parsed as bytes either: {}",
				e
			)
		})
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
		let block = it
			.next()
			.expect("First element of split iterator is never empty; qed")
			.parse()?;

		let index = it
			.next()
			.ok_or("Extrinsic index missing: example \"5:0\"")?
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

		assert_eq!(
			b0,
			Ok(BlockAddress::Hash("3BfC20f0B9aFcAcE800D73D2191166FF16540258".parse().unwrap()))
		);
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

		assert_eq!(e0, Ok(ExtrinsicAddress::Bytes(vec![0x12, 0x34])));
		assert_eq!(
			b0,
			Ok(ExtrinsicAddress::Block(
				BlockAddress::Hash("3BfC20f0B9aFcAcE800D73D2191166FF16540258".parse().unwrap()),
				5
			))
		);
		assert_eq!(b1, Ok(ExtrinsicAddress::Block(BlockAddress::Number(1234), 0)));
		assert_eq!(b2, Ok(ExtrinsicAddress::Bytes(vec![0, 0])));
		assert_eq!(b3, Ok(ExtrinsicAddress::Bytes(vec![0, 0x12, 0x34, 0x5f])));
	}
}
