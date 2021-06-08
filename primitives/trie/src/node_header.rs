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
use codec::{Encode, Decode, Input, Output};
use sp_std::iter::once;

/// A node header
#[derive(Copy, Clone, PartialEq, Eq)]
#[derive(sp_core::RuntimeDebug)]
pub(crate) enum NodeHeader {
	Null,
	Branch(bool, usize),
	Leaf(usize),
	AltHashBranch(bool, usize),
	AltHashLeaf(usize),
}

/// NodeHeader without content
pub(crate) enum NodeKind {
	Leaf,
	BranchNoValue,
	BranchWithValue,
	AltHashLeaf,
	AltHashBranchNoValue,
	AltHashBranchWithValue,
}

impl Encode for NodeHeader {
	fn encode_to<T: Output + ?Sized>(&self, output: &mut T) {
		match self {
			NodeHeader::Null => output.push_byte(trie_constants::EMPTY_TRIE),
			NodeHeader::Branch(true, nibble_count)	=>
				encode_size_and_prefix(*nibble_count, trie_constants::BRANCH_WITH_MASK, output),
			NodeHeader::Branch(false, nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::BRANCH_WITHOUT_MASK, output),
			NodeHeader::Leaf(nibble_count) =>
				encode_size_and_prefix(*nibble_count, trie_constants::LEAF_PREFIX_MASK, output),
			NodeHeader::AltHashBranch(true, nibble_count)	=>
				encode_size_and_prefix_alt(*nibble_count, trie_constants::ALT_HASIHNG_BRANCH_WITH_MASK, output),
			NodeHeader::AltHashBranch(false, nibble_count) =>
				encode_size_and_prefix_alt(*nibble_count, trie_constants::ALT_HASHING_BRANCH_WITHOUT_MASK, output),
			NodeHeader::AltHashLeaf(nibble_count) =>
				encode_size_and_prefix_alt(*nibble_count, trie_constants::ALT_HASHING_LEAF_PREFIX_MASK, output),
		}
	}
}

impl NodeHeader {
	/// Is this header using alternate hashing scheme.
	pub(crate) alt_hashing() -> bool {
		match self {
			NodeHeader::Null
			| NodeHeader::Leaf(..)
			| NodeHeader::Branch(..)	=> false,
			NodeHeader::AltHashBranch(..)
			| NodeHeader::AltHashLeaf(..) => true,
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
			trie_constants::LEAF_PREFIX_MASK => Ok(NodeHeader::Leaf(decode_size(i, input, 2)?)),
			trie_constants::BRANCH_WITH_MASK => Ok(NodeHeader::Branch(true, decode_size(i, input, 2)?)),
			trie_constants::BRANCH_WITHOUT_MASK => Ok(NodeHeader::Branch(false, decode_size(i, input, 2)?)),
			trie_constants::EMPTY_TRIE => match i & (0b1111 << 4) {
				trie_constants::ALT_HASHING_LEAF_PREFIX_MASK => Ok(NodeHeader::AltHashLeaf(decode_size(i, input, 4)?)),
				trie_constants::ALT_HASHING_BRANCH_WITH_MASK => Ok(NodeHeader::AltHashBranch(true, decode_size(i, input, 4)?)),
				trie_constants::ALT_HASHING_BRANCH_WITHOUT_MASK => Ok(NodeHeader::AltHashBranch(false, decode_size(i, input, 4)?)),
				// do not allow any special encoding
				_ => Err("Unallowed encoding".into()),
			},
		}
	}
}

/// Returns an iterator over encoded bytes for node header and size.
/// Size encoding allows unlimited, length inefficient, representation, but
/// is bounded to 16 bit maximum value to avoid possible DOS.
pub(crate) fn size_and_prefix_iterator(size: usize, prefix: u8, prefix_mask: usize) -> impl Iterator<Item = u8> {
	let size = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, size);

	let max_value = 255 >> prefix_mask;
	let l1 = sp_std::cmp::min(max_value - 1, size);
	let (first_byte, mut rem) = if size == l1 {
		(once(prefix + l1 as u8), 0)
	} else {
		(once(prefix + max_value), size - l1)
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

/// Encodes size and prefix to a stream output (prefix on 2 first bit only).
fn encode_size_and_prefix<W: Output + ?Sized>(size: usize, prefix: u8, out: &mut W) {
	for b in size_and_prefix_iterator(size, prefix, 2) {
		out.push_byte(b)
	}
}

/// Encodes size and prefix to a stream output with prefix (prefix on 4 first bit only). 
fn encode_size_and_prefix_alt<W: Output + ?Sized>(size: usize, prefix: u8, out: &mut W) {
	for b in size_and_prefix_iterator(size, prefix, 4) {
		out.push_byte(b)
	}
}

/// Decode size only from stream input and header byte.
fn decode_size(first: u8, input: &mut impl Input, prefix_mask: usize) -> Result<usize, codec::Error> {
	let max_value = 255u8 >> prefix_mask;
	let mut result = (first & max_value) as usize;
	if result < max_value {
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
