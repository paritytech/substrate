// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Child trie related struct

use parity_codec::{Encode, Decode};
use rstd::prelude::*;
#[cfg(feature = "std")]
use serde_derive::{Serialize, Deserialize};

#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;

/// keyspace type.
pub type KeySpace = Vec<u8>;


/// key of subtrie in parent trie.
pub type ParentTrie = Vec<u8>;

// TODO consider memorydb change trait to avoid those allocations eg : move prefix encoding to 
// KeyFunction implementation (and put keyspace in key function instance).
/// temp function to keyspace data above the db level
pub fn keyspace_in_prefix(ks: &KeySpace, prefix: &[u8], dst: &mut[u8]) {
	assert!(dst.len() == keyspace_prefixed_expected_len(ks, prefix));
	dst[..ks.len()].copy_from_slice(&ks);
	dst[ks.len()..].copy_from_slice(prefix);
}

/// len of targeted prefix with keyspace
pub fn keyspace_prefixed_expected_len(ks: &KeySpace, prefix: &[u8]) -> usize {
	ks.len() + prefix.len()
}

/// keyspace and prefix with allocation
pub fn keyspace_as_prefix_alloc(ks: &KeySpace, prefix: &[u8]) -> Vec<u8> {
	let mut res = rstd::vec![0;keyspace_prefixed_expected_len(ks, prefix)];
	keyspace_in_prefix(ks, prefix, res.as_mut());
	res
}

/// child trie stored definition
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord))]
pub struct SubTrieNode {
	/// subtrie unique keyspace
	#[cfg_attr(feature = "std", serde(with="bytes"))]
	pub keyspace: KeySpace,
	/// subtrie current root hash
	#[cfg_attr(feature = "std", serde(with="bytes"))]
	root: Vec<u8>,
}

/// `SubTrieNode` using reference for encoding without copy
#[derive(Encode)]
struct SubTrieNodeRef<'a> {
	pub keyspace: &'a KeySpace,
	pub root: &'a [u8],
}


/// child trie infos
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
pub struct SubTrie {
	/// subtrie last node info
	node: SubTrieNode,
	/// subtrie path: at this point it is only address of subtrie in root
  /// (only one level of subtrie)
	parent: ParentTrie,
}
impl SubTrie {
  /// map parent key to some isolated space
  pub fn prefix_parent_key(parent: &[u8]) -> Vec<u8> {
		let mut key_full = crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX.to_vec();
		parity_codec::Encode::encode_to(parent, &mut key_full);
    key_full
  }
	/// instantiate new subtrie without root value
	pub fn new(keyspace: KeySpace, parent: &[u8]) -> Self {
    let parent = Self::prefix_parent_key(parent);
		SubTrie {
			node: SubTrieNode {
				keyspace,
				root: Default::default(),
			},
			parent,
		}
	}
	/// instantiate subtrie from a read node value
	pub fn decode_node(encoded_node: &[u8], parent: &[u8]) -> Option<Self> {
		parity_codec::Decode::decode(&mut &encoded_node[..]).map(|node| {
      let parent = Self::prefix_parent_key(parent);
			SubTrie {
				node,
				parent,
			}
		})
	}
	/// instantiate subtrie from a read node value, parent node is prefixed
	pub fn decode_node_prefixed_parent(encoded_node: &[u8], parent: Vec<u8>) -> Option<Self> {
		parity_codec::Decode::decode(&mut &encoded_node[..]).map(|node|
			SubTrie {
				node,
				parent,
		})
	}
	/// encoded parent trie node content
	pub fn encoded_node(&self) -> Vec<u8> {
		parity_codec::Encode::encode(&self.node)
	}
	/// parent trie key with prefix
	pub fn parent_prefixed_key(&self) -> &Vec<u8> {
		&self.parent
	}
	/// parent trie key
	pub fn parent_key(&self) -> &[u8] {
		&self.parent[crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX.len()..]
	}
	/// access to root value (as it was on build)
	pub fn root_initial_value(&self) -> &Vec<u8> {
		&self.node.root
	}
	/// access to keyspace
	pub fn keyspace(&self) -> &Vec<u8> {
		&self.node.keyspace
	}
	/// encdode with an updated root
	pub fn encoded_with_root(&self, new_root: &[u8]) -> Vec<u8> {
		parity_codec::Encode::encode(&SubTrieNodeRef{
			keyspace: &self.node.keyspace,
			root: new_root,
		})
	}
}
