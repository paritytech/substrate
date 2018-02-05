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

//! Block header type.

use runtime_std::prelude::*;
use codec::{StreamReader, Joiner, Slicable, NonTrivialSlicable};
use runtime_std::mem;
use primitives::{BlockNumber, Hash, Digest};

#[derive(Clone)]
#[cfg_attr(feature = "with-std", derive(PartialEq, Debug))]
/// The header for a block.
pub struct Header {
	/// The parent block's "hash" (actually the Blake2-256 hash of its serialised header).
	pub parent_hash: Hash,
	/// The block's number (how many ancestors does it have?).
	pub number: BlockNumber,
	/// The root of the trie that represents this block's final storage map.
	pub state_root: Hash,
	/// The root of the trie that represents this block's transactions, indexed by a 32-bit integer.
	pub transaction_root: Hash,
	/// The digest for this block.
	pub digest: Digest,
}

impl Header {
	/// Create a new instance with default fields except `number`, which is given as an argument.
	pub fn from_block_number(number: BlockNumber) -> Self {
		Header {
			parent_hash: Default::default(),
			number,
			state_root: Default::default(),
			transaction_root: Default::default(),
			digest: Default::default(),
		}
	}
}

impl Slicable for Header {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Header {
			parent_hash: reader.read()?,
			number: reader.read()?,
			state_root: reader.read()?,
			transaction_root: reader.read()?,
			digest: Digest { logs: reader.read()?, },
		})
	}

	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(_fill_slice: &F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.parent_hash)
			.join(&self.number)
			.join(&self.state_root)
			.join(&self.transaction_root)
			.join(&self.digest.logs)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = mem::size_of::<Hash>() + mem::size_of::<BlockNumber>() + mem::size_of::<Hash>() + mem::size_of::<Hash>();
		let second_part = <Vec<Vec<u8>>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Header {}
