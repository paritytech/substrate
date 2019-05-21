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
use crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;

/// keyspace type.
pub type KeySpace = Vec<u8>;


/// info related to parent trie.
/// Full key of child trie storage location
/// and size of the prefix of this location.
pub type ParentTrie = (Vec<u8>, usize);

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

/// `SubTrieReadRef` used for non changing state query
/// so it is safe to build
#[derive(Clone)]
pub struct SubTrieReadRef<'a> {
	/// subtrie unique keyspace
	pub keyspace: &'a KeySpace,
	/// subtrie root hash
	pub root: Option<&'a [u8]>,
}

impl<'a> SubTrieReadRef<'a> {
	/// create a SubTrieReadRef
	pub fn new(keyspace: &'a KeySpace, root: Option<&'a[u8]>) -> Self {
		SubTrieReadRef {keyspace, root}
	}
	// should not be public as it produce incomplete content
	fn enc(&self) -> Option<SubTrieReadEncode> {
		self.root.map(|r| SubTrieReadEncode {keyspace: self.keyspace, root: r})
	}
}

/// `SubTrieNode` encoder internal implementation
/// shall never be exposed
#[derive(Encode, Clone)]
struct SubTrieReadEncode<'a> {
	/// subtrie unique keyspace
	pub keyspace: &'a KeySpace,
	/// subtrie root hash
	pub root: &'a [u8],
}

#[derive(PartialEq, Eq, Clone, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
/// Subtrie node info for query (with a valid root)
pub struct SubTrieRead {
	/// subtrie unique keyspace
	pub keyspace: KeySpace,
	/// subtrie root hash
	pub root: Vec<u8>,
}
impl SubTrieRead {
	/// get node ref for read only query
	pub fn node_ref(&self) -> SubTrieReadRef {
		debug_assert!(self.root.len() > 0);
		SubTrieReadRef::new(&self.keyspace, Some(&self.root[..]))
	}
}

impl parity_codec::Encode for SubTrieRead {
	fn encode(&self) -> Vec<u8> {
		SubTrieReadEncode {
			keyspace: &self.keyspace,
			root: &self.root[..]
		}.encode()
	}
}

/// child trie infos
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
pub struct SubTrie {
	/// subtrie unique keyspace
	keyspace: KeySpace,
	/// subtrie current root hash
	root: Option<Vec<u8>>,
	/// subtrie path: at this point it is only address of subtrie in root
	/// (only one level of subtrie)
	parent: ParentTrie,
	/// extension: for subtrie containing additional data
	extension: Vec<u8>,
}
impl SubTrie {
	/// map parent key to some isolated space
	pub fn prefix_parent_key(prefix: &[u8], parent: &[u8]) -> ParentTrie {
		let mut key_full = CHILD_STORAGE_KEY_PREFIX.to_vec();
		key_full.extend_from_slice(prefix);
		key_full.extend_from_slice(parent);
		(key_full, CHILD_STORAGE_KEY_PREFIX.len() + prefix.len())
	}
	/// get parent key with prefix
	/// will move to `ParentTrie` if ParentTrie become its own struct
	/// in the future.
	pub fn prefix_parent_key_slice(p: &ParentTrie) -> &[u8] {
		&p.0[CHILD_STORAGE_KEY_PREFIX.len()..]
	}
	/// get full parent key
	/// will move to `ParentTrie` if ParentTrie become its own struct
	/// in the future.
	pub fn raw_parent_key_vec(p: &ParentTrie) -> &Vec<u8> {
		&p.0
	}

	/// instantiate new subtrie without root value
	pub fn new(keyspace_builder: &mut impl KeySpaceGenerator, prefix: &[u8], parent: &[u8]) -> Self {
		let parent = Self::prefix_parent_key(prefix, parent);
		SubTrie {
			keyspace: keyspace_builder.generate_keyspace(),
			root: Default::default(),
			parent,
			extension: Default::default(),
		}
	}
	/// node ref of subtrie
	pub fn node_ref(&self) -> SubTrieReadRef {
		SubTrieReadRef::new(&self.keyspace, self.root.as_ref().map(|r|&r[..]))
	}
	/// instantiate subtrie from a read node value
	pub fn decode_node(encoded_node: &[u8], prefix: &[u8], parent: &[u8]) -> Option<Self> {
		let parent = Self::prefix_parent_key(prefix, parent);
		Self::decode_node_with_parent(encoded_node, parent)
	}
	/// instantiate subtrie from a read node value
	pub fn decode_node_with_parent(encoded_node: &[u8], parent: ParentTrie) -> Option<Self> {
		let input = &mut &encoded_node[..];
		SubTrieRead::decode(input).map(|SubTrieRead { keyspace, root }|
			SubTrie {
				keyspace,
				root: Some(root),
				parent,
				extension: (*input).to_vec(),
		})
	}
	/// test if it already exist
	pub fn is_new(&self) -> bool {
		self.root.is_some()
	}
	/// encoded parent trie node content
	pub fn encoded_node(&self) -> Option<Vec<u8>> {
		self.node_ref().enc().map(|n|{
			let mut enc = parity_codec::Encode::encode(&n);
			enc.extend_from_slice(&self.extension[..]);
			enc
		})
	}

	/// parent trie key with full prefix
	pub fn raw_parent_key(&self) -> &Vec<u8> {
		Self::raw_parent_key_vec(&self.parent)
	}
	/// parent trie key with prefix
	pub fn parent_and_prefix_slice(&self) -> &[u8] {
		Self::prefix_parent_key_slice(&self.parent)
	}

	/// parent trie key with prefix
	pub fn parent_and_prefix(&self) -> (&[u8], &[u8]) {
		(
			&self.parent.0[CHILD_STORAGE_KEY_PREFIX.len()..self.parent.1],
			&self.parent.0[self.parent.1..],
		)
	}

	/// parent trie key
	pub fn parent_key(&self) -> &[u8] {
		&self.parent.0[self.parent.1..]
	}
	/// access to root value (as it was on build)
	pub fn root_initial_value(&self) -> &Option<Vec<u8>> {
		&self.root
	}
	/// access to keyspace
	pub fn keyspace(&self) -> &Vec<u8> {
		&self.keyspace
	}
	/// encdode with an updated root
	pub fn encoded_with_root(&self, new_root: &[u8]) -> Vec<u8> {
		let mut enc = parity_codec::Encode::encode(&SubTrieReadEncode{
			keyspace: &self.keyspace,
			root: new_root,
		});
		enc.extend_from_slice(&self.extension[..]);
		enc
	}
}

impl AsRef<SubTrie> for SubTrie {
	fn as_ref(&self) -> &SubTrie {
		self
	}
}
/// Builder for keyspace (keyspace must be unique and collision resistant depending upon
/// its context). (keyspace shall either be created through builder and be unique or accessed
/// through deserializetion from state)
/// Keyspace should be unique, ideally a uuid that can be use unprefixed or unique for a given
/// prefix (user shall ensure the prefix is used only with this builder instance).
pub trait KeySpaceGenerator {
	/// generate a new keyspace
	fn generate_keyspace(&mut self) -> KeySpace;
}

/// test keyspace generator (simply use sequential values)
pub struct TestKeySpaceGenerator(u32);

impl TestKeySpaceGenerator {
	/// intitialize a new keyspace builder: only for testing
	pub fn new() -> Self { TestKeySpaceGenerator(0) }
}

impl KeySpaceGenerator for TestKeySpaceGenerator {
	fn generate_keyspace(&mut self) -> KeySpace {
		self.0 += 1;
		parity_codec::Encode::encode(&self.0)
	}
}
