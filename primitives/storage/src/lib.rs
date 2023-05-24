// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Primitive types for storage related stuff.

#![cfg_attr(not(feature = "std"), no_std)]

use core::fmt::Display;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use sp_debug_derive::RuntimeDebug;

use codec::{Decode, Encode};
use ref_cast::RefCast;
use sp_std::{
	ops::{Deref, DerefMut},
	vec::Vec,
};

/// Storage key.
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(
	feature = "serde",
	derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone, Encode, Decode)
)]
pub struct StorageKey(
	#[cfg_attr(feature = "serde", serde(with = "impl_serde::serialize"))] pub Vec<u8>,
);

impl AsRef<[u8]> for StorageKey {
	fn as_ref(&self) -> &[u8] {
		self.0.as_ref()
	}
}

/// Storage key with read/write tracking information.
#[derive(
	PartialEq, Eq, Ord, PartialOrd, sp_std::hash::Hash, RuntimeDebug, Clone, Encode, Decode,
)]
pub struct TrackedStorageKey {
	pub key: Vec<u8>,
	pub reads: u32,
	pub writes: u32,
	pub whitelisted: bool,
}

impl TrackedStorageKey {
	/// Create a default `TrackedStorageKey`
	pub fn new(key: Vec<u8>) -> Self {
		Self { key, reads: 0, writes: 0, whitelisted: false }
	}
	/// Check if this key has been "read", i.e. it exists in the memory overlay.
	///
	/// Can be true if the key has been read, has been written to, or has been
	/// whitelisted.
	pub fn has_been_read(&self) -> bool {
		self.whitelisted || self.reads > 0u32 || self.has_been_written()
	}
	/// Check if this key has been "written", i.e. a new value will be committed to the database.
	///
	/// Can be true if the key has been written to, or has been whitelisted.
	pub fn has_been_written(&self) -> bool {
		self.whitelisted || self.writes > 0u32
	}
	/// Add a storage read to this key.
	pub fn add_read(&mut self) {
		self.reads += 1;
	}
	/// Add a storage write to this key.
	pub fn add_write(&mut self) {
		self.writes += 1;
	}
	/// Whitelist this key.
	pub fn whitelist(&mut self) {
		self.whitelisted = true;
	}
}

// Easily convert a key to a `TrackedStorageKey` that has been whitelisted.
impl From<Vec<u8>> for TrackedStorageKey {
	fn from(key: Vec<u8>) -> Self {
		Self { key, reads: 0, writes: 0, whitelisted: true }
	}
}

/// Storage key of a child trie, it contains the prefix to the key.
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
#[repr(transparent)]
#[derive(RefCast)]
pub struct PrefixedStorageKey(
	#[cfg_attr(feature = "serde", serde(with = "impl_serde::serialize"))] Vec<u8>,
);

impl Deref for PrefixedStorageKey {
	type Target = Vec<u8>;

	fn deref(&self) -> &Vec<u8> {
		&self.0
	}
}

impl DerefMut for PrefixedStorageKey {
	fn deref_mut(&mut self) -> &mut Vec<u8> {
		&mut self.0
	}
}

impl PrefixedStorageKey {
	/// Create a prefixed storage key from its byte array representation.
	pub fn new(inner: Vec<u8>) -> Self {
		PrefixedStorageKey(inner)
	}

	/// Create a prefixed storage key reference.
	pub fn new_ref(inner: &Vec<u8>) -> &Self {
		PrefixedStorageKey::ref_cast(inner)
	}

	/// Get inner key, this should only be needed when writing into parent trie to avoid an
	/// allocation.
	pub fn into_inner(self) -> Vec<u8> {
		self.0
	}
}

/// Storage data associated to a [`StorageKey`].
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(
	feature = "serde",
	derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone, Encode, Decode, Default)
)]
pub struct StorageData(
	#[cfg_attr(feature = "serde", serde(with = "impl_serde::serialize"))] pub Vec<u8>,
);

/// Map of data to use in a storage, it is a collection of
/// byte key and values.
#[cfg(feature = "std")]
pub type StorageMap = std::collections::BTreeMap<Vec<u8>, Vec<u8>>;

/// Child trie storage data.
#[cfg(feature = "std")]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StorageChild {
	/// Child data for storage.
	pub data: StorageMap,
	/// Associated child info for a child
	/// trie.
	pub child_info: ChildInfo,
}

/// Struct containing data needed for a storage.
#[cfg(feature = "std")]
#[derive(Default, Debug, Clone)]
pub struct Storage {
	/// Top trie storage data.
	pub top: StorageMap,
	/// Children trie storage data. Key does not include prefix, only for the `default` trie kind,
	/// of `ChildType::ParentKeyId` type.
	pub children_default: std::collections::HashMap<Vec<u8>, StorageChild>,
}

/// Storage change set
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize, PartialEq, Eq))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct StorageChangeSet<Hash> {
	/// Block hash
	pub block: Hash,
	/// A list of changes
	pub changes: Vec<(StorageKey, Option<StorageData>)>,
}

/// List of all well known keys and prefixes in storage.
pub mod well_known_keys {
	/// Wasm code of the runtime.
	///
	/// Stored as a raw byte vector. Required by substrate.
	pub const CODE: &[u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &[u8] = b":heappages";

	/// Current extrinsic index (u32) is stored under this key.
	///
	/// Encodes to `0x3a65787472696e7369635f696e646578`.
	pub const EXTRINSIC_INDEX: &[u8] = b":extrinsic_index";

	/// Current intra-block entropy (a universally unique `[u8; 32]` value) is stored here.
	pub const INTRABLOCK_ENTROPY: &[u8] = b":intrablock_entropy";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &[u8] = b":child_storage:";

	/// Prefix of the default child storage keys in the top trie.
	pub const DEFAULT_CHILD_STORAGE_KEY_PREFIX: &[u8] = b":child_storage:default:";

	/// Whether a key is a default child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `DEFAULT_CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_default_child_storage_key(key: &[u8]) -> bool {
		key.starts_with(DEFAULT_CHILD_STORAGE_KEY_PREFIX)
	}

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}

	/// Returns if the given `key` starts with [`CHILD_STORAGE_KEY_PREFIX`] or collides with it.
	pub fn starts_with_child_storage_key(key: &[u8]) -> bool {
		if key.len() > CHILD_STORAGE_KEY_PREFIX.len() {
			key.starts_with(CHILD_STORAGE_KEY_PREFIX)
		} else {
			CHILD_STORAGE_KEY_PREFIX.starts_with(key)
		}
	}
}

/// Threshold size to start using trie value nodes in state.
pub const TRIE_VALUE_NODE_THRESHOLD: u32 = 33;

/// Information related to a child state.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(PartialEq, Eq, Hash, PartialOrd, Ord, Encode, Decode))]
pub enum ChildInfo {
	/// This is the one used by default.
	ParentKeyId(ChildTrieParentKeyId),
}

impl ChildInfo {
	/// Instantiates child information for a default child trie
	/// of kind `ChildType::ParentKeyId`, using an unprefixed parent
	/// storage key.
	pub fn new_default(storage_key: &[u8]) -> Self {
		let data = storage_key.to_vec();
		ChildInfo::ParentKeyId(ChildTrieParentKeyId { data })
	}

	/// Same as `new_default` but with `Vec<u8>` as input.
	pub fn new_default_from_vec(storage_key: Vec<u8>) -> Self {
		ChildInfo::ParentKeyId(ChildTrieParentKeyId { data: storage_key })
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: &ChildInfo) -> bool {
		match self {
			ChildInfo::ParentKeyId(child_trie) => child_trie.try_update(other),
		}
	}

	/// Returns byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	#[inline]
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(..) => self.storage_key(),
		}
	}

	/// Returns a reference to the location in the direct parent of
	/// this trie but without the common prefix for this kind of
	/// child trie.
	pub fn storage_key(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId { data }) => &data[..],
		}
	}

	/// Return a the full location in the direct parent of
	/// this trie.
	pub fn prefixed_storage_key(&self) -> PrefixedStorageKey {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId { data }) =>
				ChildType::ParentKeyId.new_prefixed_key(data.as_slice()),
		}
	}

	/// Returns a the full location in the direct parent of
	/// this trie.
	pub fn into_prefixed_storage_key(self) -> PrefixedStorageKey {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId { mut data }) => {
				ChildType::ParentKeyId.do_prefix_key(&mut data);
				PrefixedStorageKey(data)
			},
		}
	}

	/// Returns the type for this child info.
	pub fn child_type(&self) -> ChildType {
		match self {
			ChildInfo::ParentKeyId(..) => ChildType::ParentKeyId,
		}
	}
}

/// Type of child.
/// It does not strictly define different child type, it can also
/// be related to technical consideration or api variant.
#[repr(u32)]
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum ChildType {
	/// If runtime module ensures that the child key is a unique id that will
	/// only be used once, its parent key is used as a child trie unique id.
	ParentKeyId = 1,
}

impl ChildType {
	/// Try to get a child type from its `u32` representation.
	pub fn new(repr: u32) -> Option<ChildType> {
		Some(match repr {
			r if r == ChildType::ParentKeyId as u32 => ChildType::ParentKeyId,
			_ => return None,
		})
	}

	/// Transform a prefixed key into a tuple of the child type
	/// and the unprefixed representation of the key.
	pub fn from_prefixed_key<'a>(storage_key: &'a PrefixedStorageKey) -> Option<(Self, &'a [u8])> {
		let match_type = |storage_key: &'a [u8], child_type: ChildType| {
			let prefix = child_type.parent_prefix();
			if storage_key.starts_with(prefix) {
				Some((child_type, &storage_key[prefix.len()..]))
			} else {
				None
			}
		};
		match_type(storage_key, ChildType::ParentKeyId)
	}

	/// Produce a prefixed key for a given child type.
	fn new_prefixed_key(&self, key: &[u8]) -> PrefixedStorageKey {
		let parent_prefix = self.parent_prefix();
		let mut result = Vec::with_capacity(parent_prefix.len() + key.len());
		result.extend_from_slice(parent_prefix);
		result.extend_from_slice(key);
		PrefixedStorageKey(result)
	}

	/// Prefixes a vec with the prefix for this child type.
	fn do_prefix_key(&self, key: &mut Vec<u8>) {
		let parent_prefix = self.parent_prefix();
		let key_len = key.len();
		if !parent_prefix.is_empty() {
			key.resize(key_len + parent_prefix.len(), 0);
			key.copy_within(..key_len, parent_prefix.len());
			key[..parent_prefix.len()].copy_from_slice(parent_prefix);
		}
	}

	/// Returns the location reserved for this child trie in their parent trie if there
	/// is one.
	pub fn parent_prefix(&self) -> &'static [u8] {
		match self {
			&ChildType::ParentKeyId => well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX,
		}
	}
}

/// A child trie of default type.
///
/// It uses the same default implementation as the top trie, top trie being a child trie with no
/// keyspace and no storage key. Its keyspace is the variable (unprefixed) part of its storage key.
/// It shares its trie nodes backend storage with every other child trie, so its storage key needs
/// to be a unique id that will be use only once. Those unique id also required to be long enough to
/// avoid any unique id to be prefixed by an other unique id.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(PartialEq, Eq, Hash, PartialOrd, Ord, Encode, Decode))]
pub struct ChildTrieParentKeyId {
	/// Data is the storage key without prefix.
	data: Vec<u8>,
}

impl ChildTrieParentKeyId {
	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	fn try_update(&mut self, other: &ChildInfo) -> bool {
		match other {
			ChildInfo::ParentKeyId(other) => self.data[..] == other.data[..],
		}
	}
}

/// Different possible state version.
///
/// V0 and V1 uses a same trie implementation, but V1 will write external value node in the trie for
/// value with size at least `TRIE_VALUE_NODE_THRESHOLD`.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Encode, Decode))]
pub enum StateVersion {
	/// Old state version, no value nodes.
	V0 = 0,
	/// New state version can use value nodes.
	V1 = 1,
}

impl Display for StateVersion {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			StateVersion::V0 => f.write_str("0"),
			StateVersion::V1 => f.write_str("1"),
		}
	}
}

impl Default for StateVersion {
	fn default() -> Self {
		StateVersion::V1
	}
}

impl From<StateVersion> for u8 {
	fn from(version: StateVersion) -> u8 {
		version as u8
	}
}

impl TryFrom<u8> for StateVersion {
	type Error = ();
	fn try_from(val: u8) -> sp_std::result::Result<StateVersion, ()> {
		match val {
			0 => Ok(StateVersion::V0),
			1 => Ok(StateVersion::V1),
			_ => Err(()),
		}
	}
}

impl StateVersion {
	/// If defined, values in state of size bigger or equal
	/// to this threshold will use a separate trie node.
	/// Otherwhise, value will be inlined in branch or leaf
	/// node.
	pub fn state_value_threshold(&self) -> Option<u32> {
		match self {
			StateVersion::V0 => None,
			StateVersion::V1 => Some(TRIE_VALUE_NODE_THRESHOLD),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_prefix_default_child_info() {
		let child_info = ChildInfo::new_default(b"any key");
		let prefix = child_info.child_type().parent_prefix();
		assert!(prefix.starts_with(well_known_keys::CHILD_STORAGE_KEY_PREFIX));
		assert!(prefix.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX));
	}
}
