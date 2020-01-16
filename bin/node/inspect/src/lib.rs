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

#![warn(missing_docs)]

use std::{
	fmt,
	str::FromStr,
	marker::PhantomData
};
use codec::{Encode, Decode};
use sc_client_api::BlockBody;
use sp_blockchain::HeaderBackend;
use sp_core::hexdisplay::HexDisplay;
use sp_runtime::{
	generic::BlockId,
	traits::{Block, HashFor, NumberFor, Hash}
};

/// A block to retrieve.
pub enum BlockAddress<Hash, Number> {
	/// Get block by hash.
	Hash(Hash),
	/// Get block by number.
	Number(Number),
	/// Raw SCALE-encoded bytes.
	Bytes(Vec<u8>),
}

/// An extrinsic to retrieve.
pub enum ExtrinsicAddress<Hash, Number> {
	/// Extrinsic as part of existing block.
	Block(BlockAddress<Hash, Number>, usize),
	/// Raw SCALE-encoded extrinsic bytes.
	Bytes(Vec<u8>),
}

impl<Hash: FromStr, Number: FromStr> FromStr for BlockAddress<Hash, Number> {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		// try to parse hash first
		if let Ok(hash) = s.parse() {
			return Ok(BlockAddress::Hash(hash))
		}

		// then number
		if let Ok(number) = s.parse() {
			return Ok(BlockAddress::Number(number))
		}

		// then assume it's bytes (hex-encoded)
		sp_core::bytes::from_hex(s)
			.map(BlockAddress::Bytes)
			.map_err(|e| format!(
				"Given string does not look like hash or number. It could not be parsed as bytes either: {}",
				e
			))
	}
}

/// A helper type for a generic block input.
pub type BlockAddressFor<TBlock> = BlockAddress<
	<HashFor<TBlock> as Hash>::Output,
	NumberFor<TBlock>
>;

/// A Pretty formatter implementation.
pub trait PrettyPrinter<TBlock: Block> {
	/// Nicely format block.
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result;
	/// Nicely format extrinsic.
	fn fmt_extrinsic(&self, fmt: &mut fmt::Formatter, extrinsic: &TBlock::Extrinsic) -> fmt::Result;
}

/// Default dummy debug printer.
#[derive(Default)]
pub struct DebugPrinter;
impl<TBlock: Block> PrettyPrinter<TBlock> for DebugPrinter {
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result {
		writeln!(fmt, "Header:")?;
		writeln!(fmt, "{:?}", block.header())?;
		writeln!(fmt, "Extrinsics ({})", block.extrinsics().len())?;
		for (idx, ex) in block.extrinsics().iter().enumerate() {
			writeln!(fmt, "- {}:", idx)?;
			<DebugPrinter as PrettyPrinter<TBlock>>::fmt_extrinsic(self, fmt, ex)?;
		}
		writeln!(fmt, "Bytes: {:?}", HexDisplay::from(&block.encode()))?;
		Ok(())
	}

	fn fmt_extrinsic(&self, fmt: &mut fmt::Formatter, extrinsic: &TBlock::Extrinsic) -> fmt::Result {
		writeln!(fmt, " {:?}", extrinsic)?;
		writeln!(fmt, " Bytes: {:?}", HexDisplay::from(&extrinsic.encode()))?;
		Ok(())
	}
}

#[derive(Debug, derive_more::From, derive_more::Display)]
pub enum Error {
	Codec(codec::Error),
	Blockchain(sp_blockchain::Error),
	NotFound(String),
}
impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match *self {
			Self::Codec(ref e) => Some(e),
			Self::Blockchain(ref e) => Some(e),
			Self::NotFound(_) => None,
		}
	}
}

/// A helper trait to access block headers and bodies.
pub trait ChainAccess<TBlock: Block>:
	HeaderBackend<TBlock> +
	BlockBody<TBlock>
{}

impl<T, TBlock> ChainAccess<TBlock> for T where
	TBlock: Block,
	T: sp_blockchain::HeaderBackend<TBlock> + sc_client_api::BlockBody<TBlock>,
{}

/// Blockchain inspector.
pub struct Inspector<TBlock: Block, TPrinter: PrettyPrinter<TBlock> = DebugPrinter> {
	printer: TPrinter,
	chain: Box<dyn ChainAccess<TBlock>>,
	_block: PhantomData<TBlock>,
}

impl<TBlock: Block, TPrinter: PrettyPrinter<TBlock>> Inspector<TBlock, TPrinter> {
	/// Create new instance of the inspector with default printer.
	pub fn new(
		chain: impl ChainAccess<TBlock> + 'static,
	) -> Self where TPrinter: Default {
		Self::with_printer(chain, Default::default())
	}

	/// Customize pretty-printing of the data.
	pub fn with_printer(
		chain: impl ChainAccess<TBlock> + 'static,
		printer: TPrinter,
	) -> Self {
		Inspector {
			chain: Box::new(chain) as _,
			printer,
			_block: Default::default(),
		}
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
			BlockAddress::Bytes(bytes) => {
				TBlock::decode(&mut &*bytes)?
			},
			BlockAddress::Number(number) => {
				let id = BlockId::number(number);
				let not_found = format!("Could not find block {:?}", id);
				let body = self.chain.block_body(&id)?
					.ok_or(Error::NotFound(not_found.clone()))?;
				let header = self.chain.header(id)?
					.ok_or(Error::NotFound(not_found.clone()))?;
				TBlock::new(header, body)
			},
			BlockAddress::Hash(hash) => {
				let id = BlockId::hash(hash);
				let not_found = format!("Could not find block {:?}", id);
				let body = self.chain.block_body(&id)?
					.ok_or(Error::NotFound(not_found.clone()))?;
				let header = self.chain.header(id)?
					.ok_or(Error::NotFound(not_found.clone()))?;
				TBlock::new(header, body)
			},
		})
	}

	/// Get a pretty-printed extrinsic.
	///
	/// TODO [ToDr] Change input format to be either:
	/// (Hash, index)
	/// (Number, index)
	/// (Bytes, index)
	/// (Bytes)
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
				block.extrinsics()
					.get(index)
					.cloned()
					.ok_or_else(|| Error::NotFound(format!("Not found TODO")))?
			},
			ExtrinsicAddress::Bytes(bytes) => {
				TBlock::Extrinsic::decode(&mut &*bytes)?
			}
		};

		Ok(format!("{}", ExtrinsicPrinter(ext, &self.printer)))
	}
}
