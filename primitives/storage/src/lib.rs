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
	pub child_info: OwnedChildInfo,
}

#[cfg(feature = "std")]
#[derive(Default, Debug, Clone)]
/// Struct containing data needed for a storage.
pub struct Storage {
	/// Top trie storage data.
	pub top: StorageMap,
	/// Children trie storage data by storage key.
	/// Note that the key is not including child prefix, this will
	/// not be possible if a different kind of trie than `default`
	/// get in use.
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

#[derive(Clone, Copy)]
/// Information related to a child state.
pub enum ChildInfo<'a> {
	ParentKeyId(ChildTrie<'a>),
	Default(ChildTrie<'a>),
}

/// Owned version of `ChildInfo`.
/// To be use in persistence layers.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum OwnedChildInfo {
	ParentKeyId(OwnedChildTrie),
	Default(OwnedChildTrie),
}

impl<'a> ChildInfo<'a> {
	/// Instantiates information for a default child trie.
	pub const fn new_uid_parent_key(storage_key: &'a[u8]) -> Self {
		ChildInfo::ParentKeyId(ChildTrie {
			data: storage_key,
		})
	}

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
			ChildInfo::ParentKeyId(ChildTrie { data })
				=> OwnedChildInfo::ParentKeyId(OwnedChildTrie {
					data: data.to_vec(),
				}),
		}
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, data: &'a[u8], storage_key: &'a[u8]) -> Option<Self> {
		match child_type {
			x if x == ChildType::ParentKeyId as u32 => {
				if !data.len() == 0 {
					// do not allow anything for additional data.
					return None;
				}
				Some(ChildInfo::new_uid_parent_key(storage_key))
			},
			x if x == ChildType::CryptoUniqueId as u32 => Some(ChildInfo::new_default(data)),
			_ => None,
		}
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrie {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
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
			ChildInfo::ParentKeyId(ChildTrie {
				data,
			}) => &data[..],
			ChildInfo::Default(ChildTrie {
				data,
			}) => &data[..],
		}
	}

	/// Return the location reserved for this child trie in their parent trie if there
	/// is one.
	pub fn parent_prefix(&self, _parent: Option<&'a ChildInfo>) -> &'a [u8] {
		match self {
			ChildInfo::ParentKeyId(..)
			| ChildInfo::Default(..) => DEFAULT_CHILD_TYPE_PARENT_PREFIX,
		}
	}

	/// Change a key to get prefixed with the parent prefix.
	pub fn do_prefix_key(&self, key: &mut Vec<u8>, parent: Option<&ChildInfo>) {
		let parent_prefix = self.parent_prefix(parent);
		let key_len = key.len();
		if parent_prefix.len() > 0 {
			key.resize(key_len + parent_prefix.len(), 0);
			key.copy_within(..key_len, parent_prefix.len());
			key[..parent_prefix.len()].copy_from_slice(parent_prefix);
		}
	}
}

/// Type of child.
/// It does not strictly define different child type, it can also
/// be related to technical consideration or api variant.
#[repr(u32)]
pub enum ChildType {
	/// If runtime module ensures that the child key is a unique id that will
	/// only be used once, this parent key is used as a child trie unique id.
	ParentKeyId = 0,
	/// Default, this uses a cryptographic strong unique id as input, this id
	/// is used as a unique child trie identifier.
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
			OwnedChildInfo::Default(owned_child_trie) => owned_child_trie.try_update(other),
			OwnedChildInfo::ParentKeyId(owned_child_trie) => owned_child_trie.try_update(other),
		}
	}

	/// Get `ChildInfo` reference to this owned child info.
	pub fn as_ref(&self) -> ChildInfo {
		match self {
			OwnedChildInfo::Default(OwnedChildTrie { data })
				=> ChildInfo::Default(ChildTrie {
					data: data.as_slice(),
				}),
			OwnedChildInfo::ParentKeyId(OwnedChildTrie { data })
				=> ChildInfo::ParentKeyId(ChildTrie {
					data: data.as_slice(),
				}),

		}
	}
}

/// A child trie of default type.
/// Default is the same implementation as the top trie.
/// It share its trie node storage with any kind of key,
/// and its unique id needs to be collision free (eg strong
/// crypto hash).
#[derive(Clone, Copy)]
pub struct ChildTrie<'a> {
	/// Data containing unique id.
	/// Unique id must but unique and free of any possible key collision
	/// (depending on its storage behavior).
	data: &'a[u8],
}

/// Owned version of default child trie `ChildTrie`.
#[derive(Debug, Clone)]
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
			ChildInfo::Default(other) => self.data[..] == other.data[..],
			ChildInfo::ParentKeyId(other) => self.data[..] == other.data[..],
		}
	}
}

const DEFAULT_CHILD_TYPE_PARENT_PREFIX: &'static [u8] = b":child_storage:default:";

#[test]
fn assert_default_trie_in_child_trie() {
	let child_info = ChildInfo::new_default(b"any key");
	let prefix = child_info.parent_prefix(None);
	assert!(prefix.starts_with(well_known_keys::CHILD_STORAGE_KEY_PREFIX));
}

#[test]
fn test_do_prefix() {
	let child_info = ChildInfo::new_default(b"any key");
	let mut prefixed_1 = b"key".to_vec();
	child_info.do_prefix_key(&mut prefixed_1, None);
	let mut prefixed_2 = DEFAULT_CHILD_TYPE_PARENT_PREFIX.to_vec();
	prefixed_2.extend_from_slice(b"key");
	assert_eq!(prefixed_1, prefixed_2);
}
