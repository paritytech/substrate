// Copyright 2019-2019 Parity Technologies (UK) Ltd.
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

//! Legacy trie code match substrate version 1.0 implementation

pub mod trie_stream; 
pub mod node_codec; 
pub mod node_header;


mod util {
	use trie_db::{NibbleOps, Partial, ChildBitmap};
	#[cfg(not(feature = "std"))]
	use rstd::prelude::{vec, Vec};

	// Utilities (not exported):

	pub const EMPTY_TRIE: u8 = 0;
	pub const LEAF_NODE_OFFSET: u8 = 1;
	pub const LEAF_NODE_BIG: u8 = 127;
	pub const EXTENSION_NODE_OFFSET: u8 = 128;
	pub const EXTENSION_NODE_BIG: u8 = 253;
	pub const BRANCH_NODE_NO_VALUE: u8 = 254;
	pub const BRANCH_NODE_WITH_VALUE: u8 = 255;
	pub const LEAF_NODE_OVER: u8 = EXTENSION_NODE_OFFSET - LEAF_NODE_OFFSET;
	pub const EXTENSION_NODE_OVER: u8 = BRANCH_NODE_NO_VALUE - EXTENSION_NODE_OFFSET;
	pub const LEAF_NODE_THRESHOLD: u8 = LEAF_NODE_BIG - LEAF_NODE_OFFSET;
	pub const EXTENSION_NODE_THRESHOLD: u8 = EXTENSION_NODE_BIG - EXTENSION_NODE_OFFSET;	//125
	pub const LEAF_NODE_SMALL_MAX: u8 = LEAF_NODE_BIG - 1;
	pub const EXTENSION_NODE_SMALL_MAX: u8 = EXTENSION_NODE_BIG - 1;

	pub fn take<'a>(input: &mut &'a[u8], count: usize) -> Option<&'a[u8]> {
		if input.len() < count {
			return None
		}
		let r = &(*input)[..count];
		*input = &(*input)[count..];
		Some(r)
	}

	pub fn partial_to_key<N: NibbleOps>(partial: Partial, offset: u8, over: u8) -> Vec<u8> {
		let nb_nibble_hpe = (partial.0).0 as usize;
		let nibble_count = partial.1.len() * N::NIBBLE_PER_BYTE + nb_nibble_hpe;
		assert!(nibble_count < over as usize);
		let mut output = vec![offset + nibble_count as u8];
		if nb_nibble_hpe > 0 {
			output.push(N::masked_right(nb_nibble_hpe as u8, (partial.0).1));
		}
		output.extend_from_slice(&partial.1[..]);
		output
	}


	pub fn partial_to_key_it<N: NibbleOps, I: Iterator<Item = u8>>(partial: I, nibble_count: usize, offset: u8, over: u8) -> Vec<u8> {
		assert!(nibble_count < over as usize);
		let mut output = Vec::with_capacity(1 + (nibble_count / N::NIBBLE_PER_BYTE));
		output.push(offset + nibble_count as u8);
		output.extend(partial);
		output
	}

	pub fn branch_node_buf<BM: ChildBitmap, I: Iterator<Item = bool>>(has_value: bool, has_children: I, dest: &mut[u8]) {
		let first = if has_value {
			BRANCH_NODE_WITH_VALUE
		} else {
			BRANCH_NODE_NO_VALUE
		};
		dest[0] = first;
		BM::encode(has_children, &mut dest[1..]);
	}
}


