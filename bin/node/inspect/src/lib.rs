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
use codec::Decode;
use sp_runtime::traits::{Block, HashFor, NumberFor, Hash};

pub enum Input<Hash, Number> {
	Hash(Hash),
	Number(Number),
	Bytes(Vec<u8>),
}

impl<Hash: FromStr, Number: FromStr> FromStr for Input<Hash, Number> {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		// try to parse hash first
		if let Ok(hash) = s.parse() {
			return Ok(Input::Hash(hash))
		}

		// then number
		if let Ok(number) = s.parse() {
			return Ok(Input::Number(number))
		}

		// then assume it's bytes (hex-encoded)
		sp_core::bytes::from_hex(s)
			.map(Input::Bytes)
			.map_err(|e| format!(
				"Given string does not look like hash or number. It could not be parsed as bytes either: {}",
				e
			))
	}
}

pub type InputFor<TBlock> = Input<
	<HashFor<TBlock> as Hash>::Output,
	NumberFor<TBlock>
>;

pub trait PrettyPrinter<TBlock: Block> {
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result;
	fn fmt_extrinsic(&self, fmt: &mut fmt::Formatter, extrinsic: &TBlock::Extrinsic) -> fmt::Result;
}

#[derive(Default)]
pub struct DebugPrinter;
impl<TBlock: Block> PrettyPrinter<TBlock> for DebugPrinter {
	fn fmt_block(&self, fmt: &mut fmt::Formatter, block: &TBlock) -> fmt::Result {
		fmt::Debug::fmt(block, fmt)
	}

	fn fmt_extrinsic(&self, fmt: &mut fmt::Formatter, extrinsic: &TBlock::Extrinsic) -> fmt::Result {
		fmt::Debug::fmt(extrinsic, fmt)
	}
}

pub struct Inspector<TBlock: Block, TPrinter: PrettyPrinter<TBlock> = DebugPrinter> {
	printer: TPrinter,
	chain: Box<sp_blockchain::HeaderBackend<TBlock> + sp_blockchain::Block>,
	_block: PhantomData<TBlock>,
}

impl<TBlock: Block, TPrinter: PrettyPrinter<TBlock>> Inspector<TBlock, TPrinter> {
	pub fn new<C>(
		chain: impl sp_blockchain::Backend<TBlock> + 'static,
	) -> Self where TPrinter: Default {
		Self::with_printer(chain, Default::default())
	}

	pub fn with_printer(
		chain: impl sp_blockchain::Backend<TBlock> + 'static,
		printer: TPrinter,
	) -> Self {
		Inspector {
			chain: Box::new(chain) as _,
			printer,
			_block: Default::default(),
		}
	}

	pub fn block(&self, input: InputFor<TBlock>) -> Result<String, codec::Error> {
		struct BlockPrinter<'a, A, B>(A, &'a B);
		impl<'a, A: Block, B: PrettyPrinter<A>> fmt::Display for BlockPrinter<'a, A, B> {
			fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
				self.1.fmt_block(fmt, &self.0)
			}
		}

		Ok(match input {
			Input::Bytes(bytes) => {
				let block = TBlock::decode(&mut &*bytes)?;
				format!("{}", BlockPrinter(block, &self.printer))
			},
			Input::Hash(_) | Input::Number(_) => unimplemented!(),
		})
	}

	pub fn extrinsic(&self, input: InputFor<TBlock>) -> Result<String, codec::Error> {
		struct ExtrinsicPrinter<'a, A: Block, B>(A::Extrinsic, &'a B);
		impl<'a, A: Block, B: PrettyPrinter<A>> fmt::Display for ExtrinsicPrinter<'a, A, B> {
			fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
				self.1.fmt_extrinsic(fmt, &self.0)
			}
		}

		unimplemented!()
	}
}
