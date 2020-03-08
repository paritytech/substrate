// Copyright 2015-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! The node header.

use crate::trie_constants;
use codec::{Encode, Decode, Input, Output};
use sp_std::iter::once;

/// A node header
#[derive(Copy, Clone, PartialEq, Eq)]
#[derive(sp_core::RuntimeDebug)]
pub(crate) enum NodeHeader {
	Null,
	Branch(bool, usize),
	Leaf(usize),
}

/// NodeHeader without content
pub(crate) enum NodeKind {
	Leaf,
	BranchNoValue,
	BranchWithValue,
}

impl Encode for NodeHeader {
	fn encode_to<T: Output>(&self, output: &mut T) {
		match self {
			NodeHeader::Null => output.push_byte(trie_constants::EMPTY_TRIE),
			NodeHeader::Branch(true, nibble_count)	=>
				encode_size_and_prefix(*nibble_count, trie_constants::BRANCH_WITH_MASK, output),
			NodeHeader::Branch(false, nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::BRANCH_WITHOUT_MASK, output),
			NodeHeader::Leaf(nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::LEAF_PREFIX_MASK, output),
		}
	}
}

impl codec::EncodeLike for NodeHeader {}

impl Decode for NodeHeader {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		let i = input.read_byte()?;
		if i == trie_constants::EMPTY_TRIE {
			return Ok(NodeHeader::Null);
		}
		match i & (0b11 << 6) {
			trie_constants::LEAF_PREFIX_MASK => Ok(NodeHeader::Leaf(decode_size(i, input)?)),
			trie_constants::BRANCH_WITHOUT_MASK => Ok(NodeHeader::Branch(false, decode_size(i, input)?)),
			trie_constants::BRANCH_WITH_MASK => Ok(NodeHeader::Branch(true, decode_size(i, input)?)),
			// do not allow any special encoding
			_ => Err("Unallowed encoding".into()),
		}
	}
}

/// Returns an iterator over encoded bytes for node header and size.
/// Size encoding allows unlimited, length inefficient, representation, but
/// is bounded to 16 bit maximum value to avoid possible DOS.
pub(crate) fn size_and_prefix_iterator(size: usize, prefix: u8) -> impl Iterator<Item = u8> {
	let size = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, size);

	let l1 = sp_std::cmp::min(62, size);
	let (first_byte, mut rem) = if size == l1 {
		(once(prefix + l1 as u8), 0)
	} else {
		(once(prefix + 63), size - l1)
	};
	let next_bytes = move || {
		if rem > 0 {
			if rem < 256 {
				let result = rem - 1;
				rem = 0;
				Some(result as u8)
			} else {
				rem = rem.saturating_sub(255);
				Some(255)
			}
		} else {
			None
		}
	};
	first_byte.chain(sp_std::iter::from_fn(next_bytes))
}

/// Encodes size and prefix to a stream output.
fn encode_size_and_prefix(size: usize, prefix: u8, out: &mut impl Output) {
	for b in size_and_prefix_iterator(size, prefix) {
		out.push_byte(b)
	}
}

/// Decode size only from stream input and header byte.
fn decode_size(first: u8, input: &mut impl Input) -> Result<usize, codec::Error> {
	let mut result = (first & 255u8 >> 2) as usize;
	if result < 63 {
		return Ok(result);
	}
	result -= 1;
	while result <= trie_constants::NIBBLE_SIZE_BOUND {
		let n = input.read_byte()? as usize;
		if n < 255 {
			return Ok(result + n + 1);
		}
		result += 255;
	}
	Ok(trie_constants::NIBBLE_SIZE_BOUND)
}
