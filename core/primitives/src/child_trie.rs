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

use parity_codec::{Encode, Decode, Compact};
use rstd::prelude::*;
use rstd::ptr;
use crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;
use hash_db::Hasher;

/// `KeySpace` type contains a unique identifier to use for accessing
/// child trie node in a underlying key value database.
/// From a `TrieDB` perspective, accessing a child trie content requires
/// both the child trie root, but also the `KeySpace` used to store
/// this child trie.
/// The `KeySpace` of a child trie must be unique for the canonical chain
/// in order to avoid key collision at a key value database level.
/// This id is unique is currently build from a simple counter in state.
pub type KeySpace = Vec<u8>;


#[cfg(not(feature = "legacy-trie"))]
/// Keyspace to use for the parent trie key.
pub const NO_CHILD_KEYSPACE: [u8;1] = [0];
#[cfg(feature = "legacy-trie")]
// Keyspace to use for the parent trie key.
const NO_CHILD_KEYSPACE: [u8;0] = [];


/// Generate a new keyspace for a child trie.
pub fn generate_keyspace(child_counter: u128) -> Vec<u8> {
	// using 8 for block number and additional encoding targeting ~u64
	let mut result = Vec::with_capacity(8);
	parity_codec::Encode::encode_to(&Compact(child_counter), &mut result);
	result
}

// see FIXME #2741 for removal of this allocation on every operation.
// Simplest would be to put an additional optional field in prefix.
/// Utility function used for merging `KeySpace` data and `prefix` data
/// before calling key value database primitives.
/// Note that it currently does a costly append operation resulting in bigger
/// key length but possibly allowing prefix related operation at lower level.
pub fn keyspace_as_prefix_alloc(ks: Option<&KeySpace>, prefix: &[u8]) -> Vec<u8> {
	let ks = ks.map(|ks| ks.as_slice()).unwrap_or(&NO_CHILD_KEYSPACE[..]);
	let mut res = rstd::vec![0; ks.len() + prefix.len()];
	res[..ks.len()].copy_from_slice(ks);
	res[ks.len()..].copy_from_slice(prefix);
	res
}

/// Make database key from hash and prefix.
/// (here prefix already contains optional keyspace).
pub fn prefixed_key<H: Hasher>(key: &H::Out, prefix: &[u8]) -> Vec<u8> {
	let mut res = Vec::with_capacity(prefix.len() + key.as_ref().len());
	res.extend_from_slice(prefix);
	res.extend_from_slice(key.as_ref());
	res
}

/// Parent trie origin. This type contains all information
/// needed to access a parent trie.
/// Currently only a single depth is supported for child trie,
/// so it only contains the top trie key to the child trie.
/// Internally this contains a full path key (with
/// `well_known_keys::CHILD_STORAGE_KEY_PREFIX`).
pub type ParentTrie = Vec<u8>;

/// `ChildTrieReadRef` contains a reference to information
/// needed to access a child trie content.
/// Generally this should not be build directly but accessed
/// through a `node_ref` function call.
/// The struct can be build directly with invalid data, so
/// its usage is limited to read only querying.
#[derive(Clone)]
pub enum ChildTrieReadRef<'a> {
	/// Subtrie path for new trie, see [`ParentTrie`] for details.
	New(&'a KeySpace),
	/// Subtrie root hash and keyspace for existing child trie.
	Existing(&'a [u8], &'a KeySpace),
}

impl<'a> ChildTrieReadRef<'a> {
	/// Keyspace accessor for the enum.
	pub fn keyspace(&self) -> &KeySpace {
		match self {
			ChildTrieReadRef::New(k) => k,
			ChildTrieReadRef::Existing(_, k) => k,
		}
	}
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

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
/// This struct contains information needed to access a child trie.
/// When doing a remote query.
pub struct ChildTrieRead {
	/// Child trie parent key.
	pub parent: ParentTrie,
	/// Child trie root hash
	pub root: Vec<u8>,
}

impl ChildTrieRead {
	/// Use `ChildTrieRead` as a `ChildTrieReadRef`,
	/// forcing root field to an existing value.
	pub fn node_ref<'a>(&'a self, keyspace: &'a KeySpace) -> ChildTrieReadRef<'a> {
		debug_assert!(self.root.len() > 0);
		ChildTrieReadRef::Existing(&self.root[..], keyspace)
	}
}

/// Information related to a child trie.
/// This contains information needed to access a child trie
/// content but also information needed to manage child trie
/// from its parent trie (removal, move, update of root).
///
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

	/// Method for fetching or initiating a new child trie.
	///
	/// Note that call back could do nothing, which will allow unspecified behavior,
	/// but can be useful in case we create a child trie at a known unused location,
	/// or for performance purpose (later write).
	///
	/// We also provide an encodable value specific to the creation state (block number).
	pub fn fetch_or_new(
		parent_fetcher: impl FnOnce(&[u8]) -> Option<Self>,
		child_trie_update: impl FnOnce(ChildTrie),
		parent: &[u8],
		child_trie_counter: u128,
	) -> Self {
		parent_fetcher(parent)
			.unwrap_or_else(|| {
			let parent = Self::prefix_parent_key(parent);
			let ct = ChildTrie {
				keyspace: generate_keyspace(child_trie_counter),
				root: Default::default(),
				parent,
				extension: Default::default(),
			};
			child_trie_update(ct.clone());
			ct
		})
	}
	/// Get a reference to the child trie information
	/// needed for a read only query.
	pub fn node_ref(&self) -> ChildTrieReadRef {
		if let Some(root) = self.root.as_ref() {
			ChildTrieReadRef::Existing(&root[..], &self.keyspace)
		} else {
			ChildTrieReadRef::New(&self.keyspace)
		}
	}
	/// Instantiate child trie from its encoded value and location.
	/// Please do not use this function with encoded content
	/// which is not fetch from an existing child trie.
	pub fn decode_node_with_parent(
		encoded_node: &[u8],
		parent: ParentTrie,
	) -> Option<Self> {
		let input = &mut &encoded_node[..];
		ChildTrieReadDecode::decode(input).map(|ChildTrieReadDecode { version, keyspace, root }| {
			debug_assert!(version == LAST_SUBTRIE_CODEC_VERSION);
			ChildTrie {
				keyspace,
				root: Some(root),
				parent,
				extension: (*input).to_vec(),
		}})
	}
	/// Return true when the child trie is new and does not contain a root.
	pub fn is_new(&self) -> bool {
		self.root.is_none()
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
	/// Getter function for extension content of child trie.
	pub fn extension(&self) -> &[u8] {
		&self.extension[..]
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

	/// Function accessing all child trie fields and returning
	/// tuple of pointer and size from them.
	pub fn ptr_child_trie(&self) -> PtrChildTrie {
		(
			self.keyspace.as_ptr(),
			self.keyspace.len() as u32,
			self.root.as_ref().map(|r| r.as_ptr()).unwrap_or(ptr::null()),
			self.root.as_ref().map(|r| r.len() as u32).unwrap_or(u32::max_value()),
			self.parent.as_ptr(),
			self.parent.len() as u32,
			self.extension.as_ptr(),
			self.extension.len() as u32,
		)
	}
	/// Function to access all child trie fields.
	pub fn to_ptr_vec(&self) -> (&[u8], Option<&[u8]>, &[u8], &[u8]) {
		(
			self.keyspace.as_ref(),
			self.root.as_ref().map(|r| r.as_ref()),
			self.parent.as_ref(),
			self.extension.as_ref(),
		)
	}

	/// Function to rebuild child trie accessed from.
	/// This is unsafe to use because it allows to build invalid
	/// child trie object: duplicate keyspace or invalid root.
	pub fn unsafe_from_ptr_child_trie(
		keyspace: *mut u8,
		kl: u32,
		root: *mut u8,
		rl: u32,
		parent: *mut u8,
		pl: u32,
		extension: *mut u8,
		el: u32,
	) -> Self {
		unsafe {
			let keyspace = from_raw_parts(keyspace, kl).expect("non optional; qed");
			let root = from_raw_parts(root, rl);
			let parent = from_raw_parts(parent, pl).expect("non optional; qed");
			let extension = from_raw_parts(extension, el).expect("non optional; qed");
			ChildTrie { keyspace, root, parent, extension }
		}
	}

	/// Function to rebuild child trie accessed from mem copied field.
	/// This is unsafe to use because it allows to build invalid
	/// child trie object: duplicate keyspace or invalid root.
	pub fn unsafe_from_ptr_vecs(
		keyspace: Vec<u8>,
		root: Option<Vec<u8>>,
		parent: Vec<u8>,
		extension: Vec<u8>,
	) -> Self {
		ChildTrie { keyspace, root, parent, extension }
	}

}

unsafe fn from_raw_parts(ptr: *mut u8, len: u32) -> Option<Vec<u8>> {
	if len == u32::max_value() {
		None
	} else {
		Some(<Vec<u8>>::from_raw_parts(ptr, len as usize, len as usize))
	}
}

/// Pointers repersentation of ChildTrie
type PtrChildTrie = (
	*const u8,
	u32,
	*const u8,
	u32,
	*const u8,
	u32,
	*const u8,
	u32,
);

impl AsRef<ChildTrie> for ChildTrie {
	fn as_ref(&self) -> &ChildTrie {
		self
	}
}


#[test]
fn encode_empty_prefix() {
	let empt = generate_keyspace(0);

	// this ensure root trie can be move to be a child trie
	assert_eq!(&NO_CHILD_KEYSPACE[..], &empt[..]);
}
