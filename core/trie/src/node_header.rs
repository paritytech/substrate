// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! The node header.

use codec::{Encode, Decode, Input, Output};
use super::{EMPTY_TRIE, LEAF_NODE_OFFSET, LEAF_NODE_BIG, EXTENSION_NODE_OFFSET,
	EXTENSION_NODE_BIG, BRANCH_NODE_NO_VALUE, BRANCH_NODE_WITH_VALUE, LEAF_NODE_THRESHOLD,
	EXTENSION_NODE_THRESHOLD, LEAF_NODE_SMALL_MAX, EXTENSION_NODE_SMALL_MAX};

/// A node header.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum NodeHeader {
	Null,
	Branch(bool),
	Extension(usize),
	Leaf(usize),
}

impl Encode for NodeHeader {
	fn encode_to<T: Output>(&self, output: &mut T) {
		match self {
			NodeHeader::Null => output.push_byte(EMPTY_TRIE),

			NodeHeader::Branch(true) => output.push_byte(BRANCH_NODE_WITH_VALUE),
			NodeHeader::Branch(false) => output.push_byte(BRANCH_NODE_NO_VALUE),

			NodeHeader::Leaf(nibble_count) if *nibble_count < LEAF_NODE_THRESHOLD as usize =>
				output.push_byte(LEAF_NODE_OFFSET + *nibble_count as u8),
			NodeHeader::Leaf(nibble_count) => {
				output.push_byte(LEAF_NODE_BIG);
				output.push_byte((*nibble_count - LEAF_NODE_THRESHOLD as usize) as u8);
			}

			NodeHeader::Extension(nibble_count) if *nibble_count < EXTENSION_NODE_THRESHOLD as usize =>
				output.push_byte(EXTENSION_NODE_OFFSET + *nibble_count as u8),
			NodeHeader::Extension(nibble_count) => {
				output.push_byte(EXTENSION_NODE_BIG);
				output.push_byte((*nibble_count - EXTENSION_NODE_THRESHOLD as usize) as u8);
			}
		}
	}
}

impl Decode for NodeHeader {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(match input.read_byte()? {
			EMPTY_TRIE => NodeHeader::Null,							// 0

			i @ LEAF_NODE_OFFSET ... LEAF_NODE_SMALL_MAX =>			// 1 ... (127 - 1)
				NodeHeader::Leaf((i - LEAF_NODE_OFFSET) as usize),
			LEAF_NODE_BIG =>										// 127
				NodeHeader::Leaf(input.read_byte()? as usize + LEAF_NODE_THRESHOLD as usize),

			i @ EXTENSION_NODE_OFFSET ... EXTENSION_NODE_SMALL_MAX =>// 128 ... (253 - 1)
				NodeHeader::Extension((i - EXTENSION_NODE_OFFSET) as usize),
			EXTENSION_NODE_BIG =>									// 253
				NodeHeader::Extension(input.read_byte()? as usize + EXTENSION_NODE_THRESHOLD as usize),

			BRANCH_NODE_NO_VALUE => NodeHeader::Branch(false),		// 254
			BRANCH_NODE_WITH_VALUE => NodeHeader::Branch(true),		// 255
		})
	}
}
