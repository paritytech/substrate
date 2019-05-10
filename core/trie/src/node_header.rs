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

//! The node header.

use crate::s_cst;
use codec::{Encode, Decode, Input, Output};
use rstd::iter::once;

/// A node header
#[derive(Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
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
			NodeHeader::Null => output.push_byte(s_cst::EMPTY_TRIE),
			NodeHeader::Branch(true, nibble_count)	=>
				s_encode_size_and_prefix(*nibble_count, s_cst::BRANCH_WITH_MASK, output),
			NodeHeader::Branch(false, nibble_count) =>
				s_encode_size_and_prefix(*nibble_count, s_cst::BRANCH_WITHOUT_MASK, output),
			NodeHeader::Leaf(nibble_count) =>
				s_encode_size_and_prefix(*nibble_count, s_cst::LEAF_PREFIX_MASK, output),
		}
	}
}

impl Decode for NodeHeader {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let i = input.read_byte()?;
		if i == s_cst::EMPTY_TRIE {
			return Some(NodeHeader::Null);
		}
		match i & (0b11 << 6) {
			s_cst::LEAF_PREFIX_MASK => Some(NodeHeader::Leaf(s_decode_size(i, input)?)),
			s_cst::BRANCH_WITHOUT_MASK => Some(NodeHeader::Branch(false, s_decode_size(i, input)?)),
			s_cst::BRANCH_WITH_MASK => Some(NodeHeader::Branch(true, s_decode_size(i, input)?)),
			// do not allow any special encoding
			_ => None,
		}
	}
}


pub(crate) fn s_size_and_prefix_iter(size: usize, prefix: u8) -> impl Iterator<Item = u8> {
	let size = rstd::cmp::min(s_cst::NIBBLE_SIZE_BOUND, size);

	let l1 = rstd::cmp::min(62, size);
	let (first_byte, mut rem) = if size == l1 {
		(once(prefix + l1 as u8), 0)
	} else {
		(once(prefix + 63), size - l1)
	};
	let next_bytes = move || {
		if rem > 0 {
			if rem < 256 {
				let res = rem - 1;
				rem = 0;
				Some(res as u8)
			} else {
				rem = rem.saturating_sub(255);
				Some(255)
			}
		} else {
			None
		}
	};
	first_byte.chain(rstd::iter::from_fn(next_bytes))
}

/// bounding size to storage in a u16 variable to avoid dos
fn s_encode_size_and_prefix(size: usize, prefix: u8, out: &mut impl Output) {
	for b in s_size_and_prefix_iter(size, prefix) {
		out.push_byte(b)
	}
}

fn s_decode_size<I: Input>(first: u8, input: &mut I) -> Option<usize> {
	let mut result = (first & 255u8 >> 2) as usize;
	if result < 63 {
		return Some(result);
	}
	result -= 1;
	while result <= s_cst::NIBBLE_SIZE_BOUND {
		let n = input.read_byte()? as usize;
		if n < 255 {
			return Some(result + n + 1);
		}
		result += 255;
	}
	Some(s_cst::NIBBLE_SIZE_BOUND)
}
