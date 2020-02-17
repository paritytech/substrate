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
	/// Children trie storage data.
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
}

/// Owned version of `ChildInfo`.
/// To be use in persistence layers.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum OwnedChildInfo {
	ParentKeyId(OwnedChildTrie),
}

impl<'a> ChildInfo<'a> {
	/// Instantiates information for a default child trie.
	/// This is a rather unsafe method and requires to be
	/// use from a valid payload such as:
	/// ```
	/// use sp_storage::{ChildInfo, ChildType, OwnedChildInfo};
	///
	/// let info1 = ChildInfo::default_unchecked(
	///		b":child_storage:default:stor_key",
	///	);
	/// let info2 = OwnedChildInfo::new_default(
	///		b"stor_key".to_vec(),
	///	);
	///
	/// assert!(info1.info() == info2.as_ref().info());
	/// ```
	pub const fn default_unchecked(encoded: &'a[u8]) -> Self {
		ChildInfo::ParentKeyId(ChildTrie {
			data: encoded,
		})
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, info: &'a [u8]) -> Option<Self> {
		match child_type {
			x if x == ChildType::ParentKeyId as u32 => {
				debug_assert!(
					info.starts_with(ChildType::ParentKeyId.parent_prefix())
				);
				Some(Self::default_unchecked(info))
			},
			_ => None,
		}
	}

	/// Instantiates a owned version of this child info.
	pub fn to_owned(&self) -> OwnedChildInfo {
		match self {
			ChildInfo::ParentKeyId(ChildTrie { data })
				=> OwnedChildInfo::ParentKeyId(OwnedChildTrie {
					data: data.to_vec(),
				}),
		}
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrie {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Return byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(..) => self.unprefixed_storage_key(),
		}
	}

	/// Return a reference to the full location in the direct parent of
	/// this trie.
	///	If the trie got no parent this returns the empty slice,
	/// so by nature an empty slice is not a valid parent location.
	/// This does not include child type related prefix.
	pub fn storage_key(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(ChildTrie {
				data,
			}) => &data[..],
		}
	}

	/// Return a reference to the location in the direct parent of
	/// this trie.
	/// The static part of the storage key is omitted.
	pub fn unprefixed_storage_key(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(ChildTrie {
				data,
			}) => if data.len() != 0 {
				&data[ChildType::ParentKeyId.parent_prefix().len()..]
			} else {
				&[]
			},
		}
	}

	/// Return the type for this child info.
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
pub enum ChildType {
	/// If runtime module ensures that the child key is a unique id that will
	/// only be used once, this parent key is used as a child trie unique id.
	ParentKeyId = 1,
}

impl ChildType {
	/// Change a key to get prefixed with the parent prefix.
	/// TODO try to make this method non public
	pub fn do_prefix_key(&self, key: &mut Vec<u8>) {
		let parent_prefix = self.parent_prefix();
		let key_len = key.len();
		if parent_prefix.len() > 0 {
			key.resize(key_len + parent_prefix.len(), 0);
			key.copy_within(..key_len, parent_prefix.len());
			key[..parent_prefix.len()].copy_from_slice(parent_prefix);
		}
	}

	/// Return the location reserved for this child trie in their parent trie if there
	/// is one.
	fn parent_prefix(&self) -> &'static [u8] {
		match self {
			&ChildType::ParentKeyId => DEFAULT_CHILD_TYPE_PARENT_PREFIX,
		}
	}
}

impl OwnedChildInfo {
	/// Instantiates info for a default child trie with a default parent.
	pub fn new_default(mut storage_key: Vec<u8>) -> Self {
		ChildType::ParentKeyId.do_prefix_key(&mut storage_key);
		OwnedChildInfo::ParentKeyId(OwnedChildTrie {
			data: storage_key,
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: ChildInfo) -> bool {
		match self {
			OwnedChildInfo::ParentKeyId(owned_child_trie) => owned_child_trie.try_update(other),
		}
	}

	/// Owned variant of `info`.
	pub fn owned_info(self) -> (Vec<u8>, u32) {
		match self {
			OwnedChildInfo::ParentKeyId(OwnedChildTrie {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Return a reference to the full location in the direct parent of
	/// this trie.
	pub fn storage_key(self) -> Vec<u8> {
		match self {
			OwnedChildInfo::ParentKeyId(OwnedChildTrie {
				data,
			}) => data,
		}
	}

	/// Get `ChildInfo` reference to this owned child info.
	pub fn as_ref(&self) -> ChildInfo {
		match self {
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
			ChildInfo::ParentKeyId(other) => self.data[..] == other.data[..],
		}
	}
}

const DEFAULT_CHILD_TYPE_PARENT_PREFIX: &'static [u8] = b":child_storage:default:";

#[test]
fn assert_default_trie_in_child_trie() {
	let child_info = OwnedChildInfo::new_default(b"any key".to_vec());
	let child_info = child_info.as_ref();
	let prefix = child_info.child_type().parent_prefix();
	assert!(prefix.starts_with(well_known_keys::CHILD_STORAGE_KEY_PREFIX));
}
