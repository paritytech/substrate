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
pub type StorageMap = std::collections::BTreeMap<Vec<u8>, Vec<u8>>;

#[cfg(feature = "std")]
#[derive(Debug, PartialEq, Eq, Clone)]
/// Child trie storage data.
pub struct StorageChild {
	/// Child data for storage.
	pub data: StorageMap,
	/// Associated child info for a child
	/// trie.
	pub child_info: OwnedChildInfo,
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
	/// `child_trie_root` and `child_delta_trie_root` can panic if invalid value is provided to them.
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
}

#[derive(Clone, Copy)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
/// Information related to a child state.
pub enum ChildInfo<'a> {
	Default(ChildTrie<'a>),
	DefaultWithRoot(ChildTrie<'a>, &'a [u8]),
}

/// Owned version of `ChildInfo`.
/// To be use in persistence layers.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum OwnedChildInfo {
	Default(OwnedChildTrie),
	// TODO put root as option in childinfo and put also a calc_next:
	// - current_root
	// - cached_next_root
	// then method get_root hitting cached_root
	// & method apply_cache that replace current.
	// Also remove the `DefaultWithRoot` variant from owned.
	// keep not owned as is
	DefaultWithRoot(OwnedChildTrie, Vec<u8>),
}

impl<'a> ChildInfo<'a> {
	/// Instantiates information for a default child trie.
	pub const fn new_default(unique_id: &'a[u8]) -> Self {
		ChildInfo::Default(ChildTrie {
			data: unique_id,
		})
	}

	/// Instantiates a owned version of this child info.
	pub fn to_owned(&self) -> OwnedChildInfo {
		match self {
			ChildInfo::Default(ChildTrie { data })
				=> OwnedChildInfo::Default(OwnedChildTrie {
					data: data.to_vec(),
				}),
			ChildInfo::DefaultWithRoot(ChildTrie { data }, root)
							=> OwnedChildInfo::DefaultWithRoot(OwnedChildTrie {
					data: data.to_vec(),
				}, root.to_vec()),
		}
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, data: &'a[u8]) -> Option<Self> {
		match child_type {
			x if x == ChildType::CryptoUniqueId as u32 => Some(ChildInfo::new_default(data)),
			_ => None,
		}
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::DefaultWithRoot(ChildTrie {
				data,
			}, ..)
			| ChildInfo::Default(ChildTrie {
				data,
			}) => (data, ChildType::CryptoUniqueId as u32),
		}
	}

	/// Return byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::DefaultWithRoot(ChildTrie {
				data,
			}, ..)
			| ChildInfo::Default(ChildTrie {
				data,
			}) => &data[..],
		}
	}

	/// Return true if it is possible to add a root from cache
	/// here.
	pub fn can_set_root(&self) -> bool {
		match self {
			ChildInfo::Default(..) => true,
			ChildInfo::DefaultWithRoot(..) => true,
		}
	}

	/// Associate root to child info, to avoid querying twice.
	pub fn set_root(&'a mut self, new_root: &'a [u8]) {
		match self {
			ChildInfo::Default(data) => {
				*self = ChildInfo::DefaultWithRoot(*data, new_root);
			},
			ChildInfo::DefaultWithRoot(_child_trie, root) => {
				*root = new_root;
			},
		}
	}

	/// Return stored root if there is one.
	pub fn root(&self) -> Option<&[u8]> {
		match self {
			ChildInfo::Default( .. ) => None,
			ChildInfo::DefaultWithRoot(_child_trie, root) => Some(root),
		}
	}

	#[cfg(feature = "std")]
	/// Check if this is compatible with an existing
	/// child trie.
	pub fn valid_as(&self, other: &Self) -> bool {
		match self {
			ChildInfo::Default(data) => {
				match other {
					ChildInfo::DefaultWithRoot(other_data, _)
					| ChildInfo::Default(other_data) => data == other_data,
				}
			},
			ChildInfo::DefaultWithRoot(data, root) => {
				match other {
					ChildInfo::Default(other_data) => data == other_data,
					ChildInfo::DefaultWithRoot(other_data, other_root) => {
						other_data == data && other_root == root
					},
				}
			},
		}
	}
}

/// Type of child.
/// It does not strictly define different child type, it can also
/// be related to technical consideration or api variant.
#[repr(u32)]
pub enum ChildType {
	/// Default, it uses a cryptographic strong unique id as input.
	CryptoUniqueId = 1,
}

impl OwnedChildInfo {
	/// Instantiates info for a default child trie.
	pub fn new_default(unique_id: Vec<u8>) -> Self {
		OwnedChildInfo::Default(OwnedChildTrie {
			data: unique_id,
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: ChildInfo) -> bool {
		match self {
			OwnedChildInfo::DefaultWithRoot(owned_child_trie, _root) => {
				if owned_child_trie.try_update(other) {
					if let Some(root) = other.root() {
						self.set_root(root);
					}
					true
				} else {
					false
				}
			}
			OwnedChildInfo::Default(owned_child_trie) => owned_child_trie.try_update(other),
		}
	}

	/// Get `ChildInfo` reference to this owned child info.
	pub fn as_ref(&self) -> ChildInfo {
		match self {
			OwnedChildInfo::DefaultWithRoot(OwnedChildTrie { data }, root)
				=> ChildInfo::DefaultWithRoot(ChildTrie {
					data: data.as_slice(),
				}, root.as_slice()),
			OwnedChildInfo::Default(OwnedChildTrie { data })
				=> ChildInfo::Default(ChildTrie {
					data: data.as_slice(),
				}),
		}
	}

	/// Associate root to child info, to avoid querying twice.
	pub fn set_root(&mut self, new_root: &[u8]) {
		match self {
			OwnedChildInfo::Default(data) => {
				let data = sp_std::mem::replace(data, Default::default());
				*self = OwnedChildInfo::DefaultWithRoot(data, new_root.to_vec());
			},
			OwnedChildInfo::DefaultWithRoot(_child_trie, root) => {
				if root.as_slice() != new_root {
					*root = new_root.to_vec();
				}
			},
		}
	}
}

/// A child trie of default type.
/// Default is the same implementation as the top trie.
/// It share its trie node storage with any kind of key,
/// and its unique id needs to be collision free (eg strong
/// crypto hash).
#[derive(Clone, Copy)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub struct ChildTrie<'a> {
	/// Data containing unique id.
	/// Unique id must but unique and free of any possible key collision
	/// (depending on its storage behavior).
	data: &'a[u8],
}

/// Owned version of default child trie `ChildTrie`.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub struct OwnedChildTrie {
	/// See `ChildTrie` reference field documentation.
	data: Vec<u8>,
}

impl OwnedChildTrie {
	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	fn try_update(&mut self, other: ChildInfo) -> bool {
		match other {
			ChildInfo::DefaultWithRoot(other, ..)
			| ChildInfo::Default(other) => self.data[..] == other.data[..],
		}
	}

	/// Evaluate occupied memory for this struct.
	/// It does not account for allocated memory or
	/// small struct related overhead.
	pub fn len(&self) -> usize {
		self.data.len()
	}
}

impl OwnedChildInfo {
	/// Evaluate occupied memory for this struct.
	/// It does not account for allocated memory or
	/// small struct related overhead.
	pub fn len(&self) -> usize {
		match self {
			OwnedChildInfo::Default(ct) => ct.len(),
			OwnedChildInfo::DefaultWithRoot(ct, r) => ct.len() + r.len(),
		}
	}
}
