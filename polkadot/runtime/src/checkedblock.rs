// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Typesafe block interaction.

use super::{Call, Block, TIMESTAMP_SET_POSITION, PARACHAINS_SET_POSITION};
use timestamp::Call as TimestampCall;
use parachains::Call as ParachainsCall;
use primitives::parachain::CandidateReceipt;

/// Provides a type-safe wrapper around a structurally valid block.
pub struct CheckedBlock {
	inner: Block,
	file_line: Option<(&'static str, u32)>,
}

impl CheckedBlock {
	/// Create a new checked block. Fails if the block is not structurally valid.
	pub fn new(block: Block) -> Result<Self, Block> {
		let has_timestamp = block.extrinsics.get(TIMESTAMP_SET_POSITION as usize).map_or(false, |xt| {
			!xt.is_signed() && match xt.extrinsic.function {
				Call::Timestamp(TimestampCall::set(_)) => true,
				_ => false,
			}
		});

		if !has_timestamp { return Err(block) }

		let has_heads = block.extrinsics.get(PARACHAINS_SET_POSITION as usize).map_or(false, |xt| {
			!xt.is_signed() && match xt.extrinsic.function {
				Call::Parachains(ParachainsCall::set_heads(_)) => true,
				_ => false,
			}
		});

		if !has_heads { return Err(block) }
		Ok(CheckedBlock {
			inner: block,
			file_line: None,
		})
	}

	// Creates a new checked block, asserting that it is valid.
	#[doc(hidden)]
	pub fn new_unchecked(block: Block, file: &'static str, line: u32) -> Self {
		CheckedBlock {
			inner: block,
			file_line: Some((file, line)),
		}
	}

	/// Extract the timestamp from the block.
	pub fn timestamp(&self) -> ::primitives::Timestamp {
		let x = self.inner.extrinsics.get(TIMESTAMP_SET_POSITION as usize).and_then(|xt| match xt.extrinsic.function {
			Call::Timestamp(TimestampCall::set(x)) => Some(x),
			_ => None
		});

		match x {
			Some(x) => x,
			None => panic!("Invalid polkadot block asserted at {:?}", self.file_line),
		}
	}

	/// Extract the parachain heads from the block.
	pub fn parachain_heads(&self) -> &[CandidateReceipt] {
		let x = self.inner.extrinsics.get(PARACHAINS_SET_POSITION as usize).and_then(|xt| match xt.extrinsic.function {
			Call::Parachains(ParachainsCall::set_heads(ref x)) => Some(&x[..]),
			_ => None
		});

		match x {
			Some(x) => x,
			None => panic!("Invalid polkadot block asserted at {:?}", self.file_line),
		}
	}

	/// Convert into inner block.
	pub fn into_inner(self) -> Block { self.inner }
}

impl ::std::ops::Deref for CheckedBlock {
	type Target = Block;

	fn deref(&self) -> &Block { &self.inner }
}

/// Assert that a block is structurally valid. May lead to panic in the future
/// in case it isn't.
#[macro_export]
macro_rules! assert_polkadot_block {
	($block: expr) => {
		$crate::CheckedBlock::new_unchecked($block, file!(), line!())
	}
}
