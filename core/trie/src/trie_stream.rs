// Copyright 2015-2019 Parity Technologies (UK) Ltd.
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

//! `TrieStream` implementation for Substrate's trie format. 

use hash_db::Hasher;
use trie_root;
use codec::Encode;
use rstd::vec::Vec;
use crate::s_cst;
use crate::node_header::{NodeKind, s_size_and_prefix_iter};
use crate::node_codec::BitMap16;
use trie_db::ChildBitmap;

const BRANCH_NODE_NO_VALUE: u8 = 254;
const BRANCH_NODE_WITH_VALUE: u8 = 255;

#[derive(Default, Clone)]
/// Codec-flavored TrieStream
pub struct TrieStream {
	buffer: Vec<u8>,
}

impl TrieStream {
	// useful for debugging but not used otherwise
	pub fn as_raw(&self) -> &[u8] { &self.buffer }
}

fn branch_node_bit_mask(has_children: impl Iterator<Item = bool>) -> (u8, u8) {
	let mut bitmap: u16 = 0;
	let mut cursor: u16 = 1;
	for v in has_children {
		if v { bitmap |= cursor }
		cursor <<= 1;
	}
	((bitmap % 256 ) as u8, (bitmap / 256 ) as u8)
}


/// Create a leaf/branch node, encoding a number of nibbles.
fn fuse_nibbles_node<'a>(nibbles: &'a [u8], kind: NodeKind) -> impl Iterator<Item = u8> + 'a {
	let size = rstd::cmp::min(s_cst::NIBBLE_SIZE_BOUND, nibbles.len());

	let iter_start = match kind {
		NodeKind::Leaf => s_size_and_prefix_iter(size, s_cst::LEAF_PREFIX_MASK),
		NodeKind::BranchNoValue => s_size_and_prefix_iter(size, s_cst::BRANCH_WITHOUT_MASK),
		NodeKind::BranchWithValue => s_size_and_prefix_iter(size, s_cst::BRANCH_WITH_MASK),
	};
	iter_start
		.chain(if nibbles.len() % 2 == 1 { Some(nibbles[0]) } else { None })
		.chain(nibbles[nibbles.len() % 2..].chunks(2).map(|ch| ch[0] << 4 | ch[1]))
}


impl trie_root::TrieStream for TrieStream {

	fn new() -> Self {
		TrieStream {
			buffer: Vec::new()
		}
	}

	fn append_empty_data(&mut self) {
		self.buffer.push(s_cst::EMPTY_TRIE);
	}

	fn append_leaf(&mut self, key: &[u8], value: &[u8]) {
		self.buffer.extend(fuse_nibbles_node(key, NodeKind::Leaf));
		value.encode_to(&mut self.buffer);
	}

	fn begin_branch(&mut self, maybe_key: Option<&[u8]>, maybe_value: Option<&[u8]>, has_children: impl Iterator<Item = bool>) {
		if let Some(partial) = maybe_key {
			if maybe_value.is_some() {
				self.buffer.extend(fuse_nibbles_node(partial, NodeKind::BranchWithValue));
			} else {
				self.buffer.extend(fuse_nibbles_node(partial, NodeKind::BranchNoValue));
			}
			let bm = branch_node_bit_mask(has_children);
			self.buffer.extend([bm.0,bm.1].iter());
		} else {
			// should not happen
			self.buffer.extend(&branch_node(maybe_value.is_some(), has_children));
		}
		if let Some(value) = maybe_value {
			value.encode_to(&mut self.buffer);
		}
	}

	fn append_extension(&mut self, _key: &[u8]) {
		// should not happen
	}

	fn append_substream<H: Hasher>(&mut self, other: Self) {
		let data = other.out();
		match data.len() {
			0...31 => data.encode_to(&mut self.buffer),
			_ => H::hash(&data).as_ref().encode_to(&mut self.buffer),
		}
	}

	fn out(self) -> Vec<u8> { self.buffer }
}

fn branch_node(has_value: bool, has_children: impl Iterator<Item = bool>) -> [u8; 3] {
	let mut res = [0, 0, 0];
	branch_node_buf::<BitMap16, _>(has_value, has_children, &mut res[..]);
	res
}

fn branch_node_buf<BM: ChildBitmap, I: Iterator<Item = bool>>(has_value: bool, has_children: I, dest: &mut[u8]) {
	let first = if has_value {
		BRANCH_NODE_WITH_VALUE
	} else {
		BRANCH_NODE_NO_VALUE
	};
	dest[0] = first;
	BM::encode(has_children, &mut dest[1..]);
}
