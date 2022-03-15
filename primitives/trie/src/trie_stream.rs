// This file is part of Substrate.

// Copyright (C) 2015-2022 Parity Technologies (UK) Ltd.
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

//! `TrieStream` implementation for Substrate's trie format.

use crate::{
	node_header::{size_and_prefix_iterator, NodeKind},
	trie_constants,
};
use codec::{Compact, Encode};
use hash_db::Hasher;
use sp_std::vec::Vec;
use trie_root;

/// Codec-flavored TrieStream.
#[derive(Default, Clone)]
pub struct TrieStream {
	/// Current node buffer.
	buffer: Vec<u8>,
}

impl TrieStream {
	// useful for debugging but not used otherwise
	pub fn as_raw(&self) -> &[u8] {
		&self.buffer
	}
}

fn branch_node_bit_mask(has_children: impl Iterator<Item = bool>) -> (u8, u8) {
	let mut bitmap: u16 = 0;
	let mut cursor: u16 = 1;
	for v in has_children {
		if v {
			bitmap |= cursor
		}
		cursor <<= 1;
	}
	((bitmap % 256) as u8, (bitmap / 256) as u8)
}

/// Create a leaf/branch node, encoding a number of nibbles.
fn fuse_nibbles_node<'a>(nibbles: &'a [u8], kind: NodeKind) -> impl Iterator<Item = u8> + 'a {
	let size = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, nibbles.len());

	let iter_start = match kind {
		NodeKind::Leaf => size_and_prefix_iterator(size, trie_constants::LEAF_PREFIX_MASK, 2),
		NodeKind::BranchNoValue =>
			size_and_prefix_iterator(size, trie_constants::BRANCH_WITHOUT_MASK, 2),
		NodeKind::BranchWithValue =>
			size_and_prefix_iterator(size, trie_constants::BRANCH_WITH_MASK, 2),
		NodeKind::HashedValueLeaf =>
			size_and_prefix_iterator(size, trie_constants::ALT_HASHING_LEAF_PREFIX_MASK, 3),
		NodeKind::HashedValueBranch =>
			size_and_prefix_iterator(size, trie_constants::ALT_HASHING_BRANCH_WITH_MASK, 4),
	};
	iter_start
		.chain(if nibbles.len() % 2 == 1 { Some(nibbles[0]) } else { None })
		.chain(nibbles[nibbles.len() % 2..].chunks(2).map(|ch| ch[0] << 4 | ch[1]))
}

use trie_root::Value as TrieStreamValue;
impl trie_root::TrieStream for TrieStream {
	fn new() -> Self {
		Self { buffer: Vec::new() }
	}

	fn append_empty_data(&mut self) {
		self.buffer.push(trie_constants::EMPTY_TRIE);
	}

	fn append_leaf(&mut self, key: &[u8], value: TrieStreamValue) {
		let kind = match &value {
			TrieStreamValue::Inline(..) => NodeKind::Leaf,
			TrieStreamValue::Node(..) => NodeKind::HashedValueLeaf,
		};
		self.buffer.extend(fuse_nibbles_node(key, kind));
		match &value {
			TrieStreamValue::Inline(value) => {
				Compact(value.len() as u32).encode_to(&mut self.buffer);
				self.buffer.extend_from_slice(value);
			},
			TrieStreamValue::Node(hash) => {
				self.buffer.extend_from_slice(hash.as_slice());
			},
		};
	}

	fn begin_branch(
		&mut self,
		maybe_partial: Option<&[u8]>,
		maybe_value: Option<TrieStreamValue>,
		has_children: impl Iterator<Item = bool>,
	) {
		if let Some(partial) = maybe_partial {
			let kind = match &maybe_value {
				None => NodeKind::BranchNoValue,
				Some(TrieStreamValue::Inline(..)) => NodeKind::BranchWithValue,
				Some(TrieStreamValue::Node(..)) => NodeKind::HashedValueBranch,
			};

			self.buffer.extend(fuse_nibbles_node(partial, kind));
			let bm = branch_node_bit_mask(has_children);
			self.buffer.extend([bm.0, bm.1].iter());
		} else {
			unreachable!("trie stream codec only for no extension trie");
		}
		match maybe_value {
			None => (),
			Some(TrieStreamValue::Inline(value)) => {
				Compact(value.len() as u32).encode_to(&mut self.buffer);
				self.buffer.extend_from_slice(value);
			},
			Some(TrieStreamValue::Node(hash)) => {
				self.buffer.extend_from_slice(hash.as_slice());
			},
		}
	}

	fn append_extension(&mut self, _key: &[u8]) {
		debug_assert!(false, "trie stream codec only for no extension trie");
	}

	fn append_substream<H: Hasher>(&mut self, other: Self) {
		let data = other.out();
		match data.len() {
			0..=31 => data.encode_to(&mut self.buffer),
			_ => H::hash(&data).as_ref().encode_to(&mut self.buffer),
		}
	}

	fn out(self) -> Vec<u8> {
		self.buffer
	}
}
