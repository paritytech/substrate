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

/// `KeySpace` type contains a unique identifier to use for accessing
/// child trie node in a underlying key value database.
/// From a `TrieDB` perspective, accessing a child trie content requires
/// both the child trie root, but also the `KeySpace` used to store
/// this child trie.
/// The `KeySpace` of a child trie must be unique in order to avoid
/// key collision at a key value database level.
/// Therefore `KeySpace` should only be the result of a call to
/// `KeySpaceGenerator` trait `generate_keyspace` method.
/// The uniqueness property allows to move child trie between trie node
/// by only changing child trie root and `KeySpace` in the child trie
/// encoded information.
pub type KeySpace = Vec<u8>;


/// Parent trie origin. This type contains all information
/// needed to access a parent trie.
/// Currently only a single depth is supported for child trie,
/// so it only contains the top trie key to the child trie.
/// Internally this contains a full path key (with
/// `well_known_keys::CHILD_STORAGE_KEY_PREFIX`).
pub type ParentTrie = Vec<u8>;

/// Utility function used for merging `KeySpace` data and `prefix` data
/// before calling key value database primitives.
/// Note that it currently does a costy append operation resulting in bigger
/// key length but possibly allowing prefix related operation at lower level.
pub fn keyspace_as_prefix_alloc(ks: &KeySpace, prefix: &[u8]) -> Vec<u8> {
	let mut res = rstd::vec![0; ks.len() + prefix.len()];
	res[..ks.len()].copy_from_slice(&ks);
	res[ks.len()..].copy_from_slice(prefix);
	res
}

/// `ChildTrieReadRef` contains a reference to information
/// needed to access a child trie content.
/// Generally this should not be build directly but accessed
/// through a `node_ref` function call.
/// The struct can be build directly with invalid data, so
/// its usage is limited to read only querying.
#[derive(Clone)]
pub struct ChildTrieReadRef<'a> {
	/// Subtrie unique keyspace, see [`KeySpace`] for details.
	pub keyspace: &'a KeySpace,
	/// Subtrie root hash.
	/// This is optional for the case where a child trie is pending creation.
	pub root: Option<&'a [u8]>,
}

/// Current codec version of a child trie definition.
const LAST_SUBTRIE_CODEC_VERSION: u16 = 1u16;

/// `ChildTrieNode` encoder internal implementation,
/// it shall not be public.
#[derive(Encode, Clone)]
struct ChildTrieReadEncode<'a> {
	/// Current codec version
	#[codec(compact)]
	version: u16,
	/// Child trie unique keyspace
	keyspace: &'a KeySpace,
	/// Child trie root hash
	root: &'a [u8],
}

#[derive(Decode)]
struct ChildTrieReadDecode {
	#[codec(compact)]
	version: u16,
	keyspace: KeySpace,
	root: Vec<u8>,
}

impl Into<ChildTrieRead> for ChildTrieReadDecode {
	fn into(self) -> ChildTrieRead {
		let ChildTrieReadDecode { keyspace, root, .. } = self;
		ChildTrieRead { keyspace, root }
	}
}

#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
/// This struct contains information needed to access a child trie.
/// This is semantically similar to `ChildTrieReadRef` but with owned values.
pub struct ChildTrieRead {
	/// Child trie unique keyspace, see [`KeySpace`] for details.
	pub keyspace: KeySpace,
	/// Child trie root hash
	pub root: Vec<u8>,
}

impl ChildTrieRead {
	/// Use `ChildTrieRead` as a `ChildTrieReadRef`,
	/// forcing root field to an existing value.
	pub fn node_ref(&self) -> ChildTrieReadRef {
		debug_assert!(self.root.len() > 0);
		ChildTrieReadRef {
			keyspace: &self.keyspace,
			root: Some(&self.root[..]),
		}
	}
}

impl parity_codec::Encode for ChildTrieRead {
	fn encode(&self) -> Vec<u8> {
		ChildTrieReadEncode {
			version: LAST_SUBTRIE_CODEC_VERSION,
			keyspace: &self.keyspace,
			root: &self.root[..]
		}.encode()
	}
}

impl parity_codec::Decode for ChildTrieRead {
	fn decode<I: parity_codec::Input>(i: &mut I) -> Option<Self> {
		ChildTrieReadDecode::decode(i)
			.and_then(|v| if v.version == LAST_SUBTRIE_CODEC_VERSION {
				Some(v.into())
			} else {
				None
			}
		)
	}
}

/// Information related to a child trie.
/// This contains information needed to access a child trie
/// content but also information needed to manage child trie
/// from its parent trie (removal, move, update of root).
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
pub struct ChildTrie {
	/// `KeySpace` for this child trie, see [`KeySpace`] for details.
	keyspace: KeySpace,
	/// Child trie current root, in case of modification
	/// this is not updated.
	root: Option<Vec<u8>>,
	/// Current position of this child trie, see [`ParentTrie`] for details.
	parent: ParentTrie,
	/// Extension contains additional encoded data related to this child trie
	/// node. A trait over the content could be use,
	/// but for simplicity the encoded value is use here.
	/// Direct operation on the child trie node are doable without
	/// having to know the type of the extension content.
	extension: Vec<u8>,
}

impl ChildTrie {
	/// Primitive to build a `ParentTrie` from its
	/// key.
	pub fn prefix_parent_key(parent: &[u8]) -> ParentTrie {
		let mut key_full = CHILD_STORAGE_KEY_PREFIX.to_vec();
		key_full.extend_from_slice(parent);
		key_full
	}
	/// Function to access the current key to a child trie.
	/// This does not include `well_known_keys::CHILD_STORAGE_KEY_PREFIX`.
	pub fn parent_key_slice(p: &ParentTrie) -> &[u8] {
		&p[CHILD_STORAGE_KEY_PREFIX.len()..]
	}
	/// Constructor to use for building a new child trie.
	///
	/// By using a `KeySpaceGenerator` it does not allow setting an existing `KeySpace`.
	/// If a new trie is created (see `is_new` method), the trie is not commited and
	/// another call to this method will create a new trie.
	///
	/// This can be quite unsafe for user, so use with care (write new trie information
	/// as soon as possible).
	pub fn fetch_or_new(
		keyspace_builder: &mut impl KeySpaceGenerator,
		parent_fetcher: impl FnOnce(&[u8]) -> Option<Self>,
		parent: &[u8],
	) -> Self {
		parent_fetcher(parent).unwrap_or_else(|| {
			let parent = Self::prefix_parent_key(parent);
			ChildTrie {
				keyspace: keyspace_builder.generate_keyspace(),
				root: Default::default(),
				parent,
				extension: Default::default(),
			}
		})
	}
	/// Get a reference to the child trie information
	/// needed for a read only query.
	pub fn node_ref(&self) -> ChildTrieReadRef {
		ChildTrieReadRef {
			keyspace: &self.keyspace,
			root: self.root.as_ref().map(|r| &r[..]),
		}
	}
	/// Instantiate child trie from its encoded value and location.
	/// Please do not use this function with encoded content
	/// which is not fetch from an existing child trie.
	pub fn decode_node_with_parent(encoded_node: &[u8], parent: ParentTrie) -> Option<Self> {
		let input = &mut &encoded_node[..];
		ChildTrieRead::decode(input).map(|ChildTrieRead { keyspace, root }|
			ChildTrie {
				keyspace,
				root: Some(root),
				parent,
				extension: (*input).to_vec(),
		})
	}
	/// Return true when the child trie is new and does not contain a root.
	pub fn is_new(&self) -> bool {
		self.root.is_some()
	}
	/// See [`parent_key_slice`].
	pub fn parent_slice(&self) -> &[u8] {
		Self::parent_key_slice(&self.parent)
	}
	/// Function to access the full key buffer pointing to
	/// a child trie. This contains technical information
	/// and should only be used for backend implementation.
	pub fn parent_trie(&self) -> &ParentTrie {
		&self.parent
	}
	/// Getter function to the original root value of this
	/// child trie.
	pub fn root_initial_value(&self) -> &Option<Vec<u8>> {
		&self.root
	}
	/// Getter function for the `KeySpace` of this child trie.
	pub fn keyspace(&self) -> &KeySpace {
		&self.keyspace
	}
	/// Encoder for the child trie, with a new root value.
	/// The child trie current root value is not updated (if
	/// content is commited the child trie will need to be fetch
	/// again for update).
	pub fn encoded_with_root(&self, new_root: &[u8]) -> Vec<u8> {
		let mut enc = parity_codec::Encode::encode(&ChildTrieReadEncode{
			version: LAST_SUBTRIE_CODEC_VERSION,
			keyspace: &self.keyspace,
			root: new_root,
		});
		enc.extend_from_slice(&self.extension[..]);
		enc
	}
}

impl AsRef<ChildTrie> for ChildTrie {
	fn as_ref(&self) -> &ChildTrie {
		self
	}
}
/// Builder for `KeySpace`.
/// Implementation of this trait must ensure unicity of generated `KeySpace` over the whole runtime context.
/// In the context of deterministic generation this can be difficult, so
/// using a fixed module specific prefix over a module counter is considered fine (prefix should be
/// long enought to avoid collision).
pub trait KeySpaceGenerator {
	/// generate a new keyspace
	fn generate_keyspace(&mut self) -> KeySpace;
}

/// Test keyspace generator, it is a simple in memory counter, only for test usage.
pub struct TestKeySpaceGenerator(u32);

impl TestKeySpaceGenerator {
	/// Intitialize a new keyspace builder with first id being 1.
	/// This does not verify the unique id asumption of `KeySpace`
	/// and should only be use in tests.
	pub fn new() -> Self { TestKeySpaceGenerator(0) }
}

impl KeySpaceGenerator for TestKeySpaceGenerator {
	fn generate_keyspace(&mut self) -> KeySpace {
		self.0 += 1;
		parity_codec::Encode::encode(&self.0)
	}
}
