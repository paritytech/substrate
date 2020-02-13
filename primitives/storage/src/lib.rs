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

use codec::{Encode, Decode};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use sp_std::collections::btree_map::BTreeMap;
use sp_debug_derive::RuntimeDebug;

use sp_std::{vec::Vec, borrow::Cow};

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
pub type StorageMap = BTreeMap<Vec<u8>, Vec<u8>>;

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
	/// Children trie storage data by storage key.
	pub children: std::collections::HashMap<Vec<u8>, StorageChild>,
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
	/// `trie_root` can panic if invalid value is provided to them.
	pub fn is_child_trie_key_valid(storage_key: &[u8]) -> bool {
		let has_right_prefix = storage_key.starts_with(b":child_storage:default:");
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

	/// Return true if the variable part of the key is empty.
	pub fn is_child_trie_key_empty(storage_key: &[u8]) -> bool {
		storage_key.len() == b":child_storage:default:".len()
	}
}

/// A wrapper around a child storage key.
///
/// This wrapper ensures that the child storage key is correct and properly used. It is
/// impossible to create an instance of this struct without providing a correct `storage_key`.
pub struct ChildStorageKey<'a> {
	storage_key: Cow<'a, [u8]>,
}

impl<'a> ChildStorageKey<'a> {
	/// Create new instance of `Self`.
	fn new(storage_key: Cow<'a, [u8]>) -> Option<Self> {
		if well_known_keys::is_child_trie_key_valid(&storage_key) {
			Some(ChildStorageKey { storage_key })
		} else {
			None
		}
	}

	/// Create a new `ChildStorageKey` from a vector.
	///
	/// `storage_key` need to start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_vec(key: Vec<u8>) -> Option<Self> {
		Self::new(Cow::Owned(key))
	}

	/// Create a new `ChildStorageKey` from a slice.
	///
	/// `storage_key` need to start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_slice(key: &'a [u8]) -> Option<Self> {
		Self::new(Cow::Borrowed(key))
	}

	/// Get access to the byte representation of the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn as_ref(&self) -> &[u8] {
		&*self.storage_key
	}

	/// Destruct this instance into an owned vector that represents the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn into_owned(self) -> Vec<u8> {
		self.storage_key.into_owned()
	}

	/// Return true if the variable part of the key is empty.
	pub fn is_empty(&self) -> bool {
		well_known_keys::is_child_trie_key_empty(&*self.storage_key)
	}

}


/// Information related to a child state.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encode, Decode)]
pub enum ChildInfo {
	Default(ChildTrie),
}

impl ChildInfo {
	/// Create a new child trie information for default
	/// child type.
	pub fn new_default(unique_id: &[u8]) -> Self {
		ChildInfo::Default(ChildTrie {
			data: unique_id.to_vec(),
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: &ChildInfo) -> bool {
		match self {
			ChildInfo::Default(child_trie) => child_trie.try_update(other),
		}
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, data: &[u8]) -> Option<Self> {
		match ChildType::new(child_type) {
			Some(ChildType::CryptoUniqueId) => Some(ChildInfo::new_default(data)),
			None => None,
		}
	}

	/// Top trie defined as the unique crypto id trie with
	/// 0 length unique id.
	pub fn top_trie() -> Self {
		Self::new_default(&[])
	}

	/// Top trie defined as the unique crypto id trie with
	/// 0 length unique id.
	pub fn is_top_trie(&self) -> bool {
		match self {
			ChildInfo::Default(ChildTrie { data }) => data.len() == 0
		}
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::Default(ChildTrie {
				data,
			}) => (data, ChildType::CryptoUniqueId as u32),
		}
	}

	/// Return byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::Default(ChildTrie {
				data,
			}) => &data[..],
		}
	}

	/// Return type for child trie.
	pub fn child_type(&self) -> ChildType {
		match self {
			ChildInfo::Default(..) => ChildType::CryptoUniqueId,
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
	/// Default, it uses a cryptographic strong unique id as input.
	CryptoUniqueId = 1,
}

impl ChildType {
	fn new(repr: u32) -> Option<ChildType> {
		Some(match repr {
			r if r == ChildType::CryptoUniqueId as u32 => ChildType::CryptoUniqueId,
			_ => return None,
		})
	}
}
/// A child trie of default type.
/// Default is the same implementation as the top trie.
/// It share its trie node storage with any kind of key,
/// and its unique id needs to be collision free (eg strong
/// crypto hash).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encode, Decode)]
pub struct ChildTrie {
	/// Data containing unique id.
	/// Unique id must but unique and free of any possible key collision
	/// (depending on its storage behavior).
	data: Vec<u8>,
}

impl ChildTrie {
	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	fn try_update(&mut self, other: &ChildInfo) -> bool {
		match other {
			ChildInfo::Default(other) => self.data[..] == other.data[..],
		}
	}
}

#[cfg(feature = "std")]
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
/// Type for storing a map of child trie related information.
/// A few utilities methods are defined.
pub struct ChildrenMap<T>(pub BTreeMap<ChildInfo, T>);

/// Type alias for storage of children related content. 
pub type ChildrenVec<T> = Vec<(ChildInfo, T)>;

/// Type alias for storage of children related content. 
pub type ChildrenSlice<'a, T> = &'a [(ChildInfo, T)];

#[cfg(feature = "std")]
impl<T> sp_std::ops::Deref for ChildrenMap<T> {
	type Target = BTreeMap<ChildInfo, T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[cfg(feature = "std")]
impl<T> sp_std::ops::DerefMut for ChildrenMap<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

#[cfg(feature = "std")]
impl<T> sp_std::default::Default for ChildrenMap<T> {
	fn default() -> Self {
		ChildrenMap(BTreeMap::new())
	}
}

#[cfg(feature = "std")]
impl<T> ChildrenMap<T> {
	/// Extend for `ChildrenMap` is usually about merging entries,
	/// this method extends two maps, by applying a merge function
	/// on each of its entries.
	pub fn extend_with(
		&mut self,
		other: impl Iterator<Item = (ChildInfo, T)>,
		merge: impl Fn(&mut T, T),
	) {
		use sp_std::collections::btree_map::Entry;
		for (child_info, child_content) in other {
			match self.0.entry(child_info) {
				Entry::Occupied(mut entry) => {
					merge(entry.get_mut(), child_content)
				},
				Entry::Vacant(entry) => {
					entry.insert(child_content);
				},
			}
		}
	}

	/// Extends two maps, by extending entries with the same key.
	pub fn extend_replace(
		&mut self,
		other: impl Iterator<Item = (ChildInfo, T)>,
	) {
		self.0.extend(other)
	}

	/// Retains only the elements specified by the predicate.
	pub fn retain(&mut self, mut f: impl FnMut(&ChildInfo, &mut T) -> bool) {
		let mut to_del = Vec::new();
		for (k, v) in self.0.iter_mut() {
			if !f(k, v) {
				// this clone can be avoid with unsafe code
				to_del.push(k.clone());
			}
		}
		for k in to_del {
			self.0.remove(&k);
		}
	}
}

#[cfg(feature = "std")]
impl<T> IntoIterator for ChildrenMap<T> {
	type Item = (ChildInfo, T);
	type IntoIter = sp_std::collections::btree_map::IntoIter<ChildInfo, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}
