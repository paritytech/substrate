// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Primitive types for storage related stuff.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use sp_debug_derive::RuntimeDebug;

use sp_std::vec::Vec;

/// Storage key.
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageKey(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// Storage data associated to a [`StorageKey`].
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageData(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// Map of data to use in a storage, it is a collection of
/// byte key and values.
#[cfg(feature = "std")]
pub type StorageMap = std::collections::BTreeMap<Vec<u8>, Vec<u8>>;

#[cfg(feature = "std")]
#[derive(Debug, PartialEq, Eq, Clone)]
/// Child trie storage data.
pub struct StorageChild {
	/// Child data for storage.
	pub data: StorageMap,
	/// Associated child info for a child
	/// trie.
	pub child_info: ChildInfo,
}

#[cfg(feature = "std")]
#[derive(Default, Debug, Clone)]
/// Struct containing data needed for a storage.
pub struct Storage {
	/// Top trie storage data.
	pub top: StorageMap,
	/// Children trie storage data.
	/// The key does not including prefix, for the `default`
	/// trie kind, so this is exclusively for the `ChildType::ParentKeyId`
	/// tries.
	pub children_default: std::collections::HashMap<Vec<u8>, StorageChild>,
}

/// Storage change set
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
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
	pub const CODE: &'static [u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &'static [u8] = b":heappages";

	/// Current extrinsic index (u32) is stored under this key.
	pub const EXTRINSIC_INDEX: &'static [u8] = b":extrinsic_index";

	/// Changes trie configuration is stored under this key.
	pub const CHANGES_TRIE_CONFIG: &'static [u8] = b":changes_trie";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &'static [u8] = b":child_storage:";

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}

	/// Determine whether a child trie key is valid.
	///
	/// For now, the only valid child trie keys are those starting with `:child_storage:default:`.
	///
	/// `child_trie_root` and `child_delta_trie_root` can panic if invalid value is provided to them.
	pub fn is_child_trie_key_valid(storage_key: &[u8]) -> bool {
		let has_right_prefix = storage_key.starts_with(super::DEFAULT_CHILD_TYPE_PARENT_PREFIX);
		if has_right_prefix {
			// This is an attempt to catch a change of `is_child_storage_key`, which
			// just checks if the key has prefix `:child_storage:` at the moment of writing.
			debug_assert!(
				is_child_storage_key(&storage_key),
				"`is_child_trie_key_valid` is a subset of `is_child_storage_key`",
			);
		}
		has_right_prefix
	}
}

/// Information related to a child state.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
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
		ChildInfo::ParentKeyId(ChildTrieParentKeyId {
			data: storage_key,
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: &ChildInfo) -> bool {
		match self {
			ChildInfo::ParentKeyId(child_trie) => child_trie.try_update(other),
		}
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, info: &[u8]) -> Option<Self> {
		match ChildType::new(child_type) {
			Some(ChildType::ParentKeyId) => {
				debug_assert!(
					info.starts_with(ChildType::ParentKeyId.parent_prefix())
				);
				Some(Self::new_default(info))
			},
			None => None,
		}
	}

	/// Returns a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Owned variant of `info`.
	pub fn into_info(self) -> (Vec<u8>, u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Returns byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
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
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => &data[..],
		}
	}

	/// Return a the full location in the direct parent of
	/// this trie.
	pub fn prefixed_storage_key(&self) -> Vec<u8> {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => ChildType::ParentKeyId.new_prefixed_key(data.as_slice()),
		}
	}

	/// Returns a the full location in the direct parent of
	/// this trie.
	pub fn into_prefixed_storage_key(self) -> Vec<u8> {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				mut data,
			}) => {
				ChildType::ParentKeyId.do_prefix_key(&mut data);
				data
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
	fn new(repr: u32) -> Option<ChildType> {
		Some(match repr {
			r if r == ChildType::ParentKeyId as u32 => ChildType::ParentKeyId,
			_ => return None,
		})
	}

	/// Produce a prefixed key for a given child type.
	fn new_prefixed_key(&self, key: &[u8]) -> Vec<u8> {
		let parent_prefix = self.parent_prefix();
		let mut result = Vec::with_capacity(parent_prefix.len() + key.len());
		result.extend_from_slice(parent_prefix);
		result.extend_from_slice(key);
		result
	}

	/// Prefixes a vec with the prefix for this child type.
	fn do_prefix_key(&self, key: &mut Vec<u8>) {
		let parent_prefix = self.parent_prefix();
		let key_len = key.len();
		if parent_prefix.len() > 0 {
			key.resize(key_len + parent_prefix.len(), 0);
			key.copy_within(..key_len, parent_prefix.len());
			key[..parent_prefix.len()].copy_from_slice(parent_prefix);
		}
	}

	/// Returns the location reserved for this child trie in their parent trie if there
	/// is one.
	fn parent_prefix(&self) -> &'static [u8] {
		match self {
			&ChildType::ParentKeyId => DEFAULT_CHILD_TYPE_PARENT_PREFIX,
		}
	}
}

/// A child trie of default type.
/// It uses the same default implementation as the top trie,
/// top trie being a child trie with no keyspace and no storage key.
/// Its keyspace is the variable (unprefixed) part of its storage key.
/// It shares its trie nodes backend storage with every other
/// child trie, so its storage key needs to be a unique id
/// that will be use only once.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub struct ChildTrieParentKeyId {
	/// Data is the full prefixed storage key.
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

const DEFAULT_CHILD_TYPE_PARENT_PREFIX: &'static [u8] = b":child_storage:default:";

#[test]
fn test_prefix_default_child_info() {
	let child_info = ChildInfo::new_default(b"any key");
	let prefix = child_info.child_type().parent_prefix();
	assert!(prefix.starts_with(well_known_keys::CHILD_STORAGE_KEY_PREFIX));
	assert!(prefix.starts_with(DEFAULT_CHILD_TYPE_PARENT_PREFIX));
}
