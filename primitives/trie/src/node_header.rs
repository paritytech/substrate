// This file is part of Substrate.

// Copyright (C) 2015-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The node header.

use crate::trie_constants;
use codec::{Decode, Encode, Input, Output};
use sp_std::iter::once;

/// A node header
#[derive(Copy, Clone, PartialEq, Eq, sp_core::RuntimeDebug)]
pub(crate) enum NodeHeader {
	Null,
	// contains wether there is a value and nibble count
	Branch(bool, usize),
	// contains nibble count
	Leaf(usize),
	// contains nibble count.
	HashedValueBranch(usize),
	// contains nibble count.
	HashedValueLeaf(usize),
}

impl NodeHeader {
	pub(crate) fn contains_hash_of_value(&self) -> bool {
		matches!(self, NodeHeader::HashedValueBranch(_) | NodeHeader::HashedValueLeaf(_))
	}
}

/// NodeHeader without content
pub(crate) enum NodeKind {
	Leaf,
	BranchNoValue,
	BranchWithValue,
	HashedValueLeaf,
	HashedValueBranch,
}

impl Encode for NodeHeader {
	fn encode_to<T: Output + ?Sized>(&self, output: &mut T) {
		match self {
			NodeHeader::Null => output.push_byte(trie_constants::EMPTY_TRIE),
			NodeHeader::Branch(true, nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::BRANCH_WITH_MASK, 2, output),
			NodeHeader::Branch(false, nibble_count) => encode_size_and_prefix(
				*nibble_count,
				trie_constants::BRANCH_WITHOUT_MASK,
				2,
				output,
			),
			NodeHeader::Leaf(nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::LEAF_PREFIX_MASK, 2, output),
			NodeHeader::HashedValueBranch(nibble_count) => encode_size_and_prefix(
				*nibble_count,
				trie_constants::ALT_HASHING_BRANCH_WITH_MASK,
				4,
				output,
			),
			NodeHeader::HashedValueLeaf(nibble_count) => encode_size_and_prefix(
				*nibble_count,
				trie_constants::ALT_HASHING_LEAF_PREFIX_MASK,
				3,
				output,
			),
		}
	}
}

impl codec::EncodeLike for NodeHeader {}

impl Decode for NodeHeader {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		let i = input.read_byte()?;
		if i == trie_constants::EMPTY_TRIE {
			return Ok(NodeHeader::Null)
		}
		match i & (0b11 << 6) {
			trie_constants::LEAF_PREFIX_MASK => Ok(NodeHeader::Leaf(decode_size(i, input, 2)?)),
			trie_constants::BRANCH_WITH_MASK =>
				Ok(NodeHeader::Branch(true, decode_size(i, input, 2)?)),
			trie_constants::BRANCH_WITHOUT_MASK =>
				Ok(NodeHeader::Branch(false, decode_size(i, input, 2)?)),
			trie_constants::EMPTY_TRIE => {
				if i & (0b111 << 5) == trie_constants::ALT_HASHING_LEAF_PREFIX_MASK {
					Ok(NodeHeader::HashedValueLeaf(decode_size(i, input, 3)?))
				} else if i & (0b1111 << 4) == trie_constants::ALT_HASHING_BRANCH_WITH_MASK {
					Ok(NodeHeader::HashedValueBranch(decode_size(i, input, 4)?))
				} else {
					// do not allow any special encoding
					Err("Unallowed encoding".into())
				}
			},
			_ => unreachable!(),
		}
	}
}

/// Returns an iterator over encoded bytes for node header and size.
/// Size encoding allows unlimited, length inefficient, representation, but
/// is bounded to 16 bit maximum value to avoid possible DOS.
pub(crate) fn size_and_prefix_iterator(
	size: usize,
	prefix: u8,
	prefix_mask: usize,
) -> impl Iterator<Item = u8> {
	let size = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, size);

	let max_value = 255u8 >> prefix_mask;
	let l1 = sp_std::cmp::min((max_value as usize).saturating_sub(1), size);
	let (first_byte, mut rem) = if size == l1 {
		(once(prefix + l1 as u8), 0)
	} else {
		(once(prefix + max_value as u8), size - l1)
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
fn encode_size_and_prefix<W>(size: usize, prefix: u8, prefix_mask: usize, out: &mut W)
where
	W: Output + ?Sized,
{
	for b in size_and_prefix_iterator(size, prefix, prefix_mask) {
		out.push_byte(b)
	}
}

/// Decode size only from stream input and header byte.
fn decode_size(
	first: u8,
	input: &mut impl Input,
	prefix_mask: usize,
) -> Result<usize, codec::Error> {
	let max_value = 255u8 >> prefix_mask;
	let mut result = (first & max_value) as usize;
	if result < max_value as usize {
		return Ok(result)
	}
	result -= 1;
	while result <= trie_constants::NIBBLE_SIZE_BOUND {
		let n = input.read_byte()? as usize;
		if n < 255 {
			return Ok(result + n + 1)
		}
		result += 255;
	}
	Ok(trie_constants::NIBBLE_SIZE_BOUND)
}
