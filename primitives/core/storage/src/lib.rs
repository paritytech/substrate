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

//! Primitive types for storage related stuff.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use substrate_debug_derive::RuntimeDebug;

use rstd::{vec::Vec, borrow::Cow};
use codec::{Encode, Decode, Compact};

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

/// A set of key value pairs for storage.
#[cfg(feature = "std")]
pub type StorageOverlay = std::collections::HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
#[cfg(feature = "std")]
pub type ChildrenStorageOverlay = std::collections::HashMap<
	Vec<u8>,
	(StorageOverlay, OwnedChildInfo),
>;

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
/// Information related to a child state.
pub enum ChildInfo<'a> {
	Default(ChildTrie<'a>),
}

/// Owned version of `ChildInfo`.
/// To be use in persistence layers.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum OwnedChildInfo {
	Default(OwnedChildTrie),
}

impl<'a> ChildInfo<'a> {
	/// Instantiates information for a default child trie.
	pub const fn new_default(unique_id: &'a[u8]) -> Self {
		ChildInfo::Default(ChildTrie {
			offset: 0,
			root_end: 0,
			data: unique_id,
		})
	}

	/// Instantiates a owned version of this child info.
	pub fn to_owned(&self) -> OwnedChildInfo {
		match self {
			ChildInfo::Default(ChildTrie { data, root_end, offset })
				=> OwnedChildInfo::Default(OwnedChildTrie {
					offset: *offset,
					root_end: *root_end,
					data: data.to_vec(),
				}),
		}
	}

	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(child_type: u32, data: &'a[u8]) -> Option<Self> {
		match child_type {
			x if x == ChildType::CryptoUniqueId as u32 => Some(ChildInfo::new_default(data)),
			x if x == ChildType::CryptoUniqueIdRootApi as u32 => {
				let data_cursor = &mut &data[..];
				// u32 is considered enough for a root size.
				let number = match Compact::<u32>::decode(data_cursor) {
					Ok(number) => number.0,
					Err(_) => return None,
				};
				let offset = data.len() - data_cursor.len();
				if data.len() >= number as usize {
					Some(ChildInfo::Default(ChildTrie {
						offset,
						root_end: number as usize + offset,
						data,
					}))
				} else { None }
			},
			_ => None,
		}
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::Default(ChildTrie {
				root_end,
				data,
				..
			}) => {
				if *root_end > 0 {
					return (data, ChildType::CryptoUniqueIdRootApi as u32);
				}
				(data, ChildType::CryptoUniqueId as u32)
			},
		}
	}

	/// Return byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::Default(ChildTrie {
				root_end,
				data,
				..
			}) => &data[*root_end..],
		}
	}

	/// Return the child reference to state if it is already known.
	/// If it returns `None` the information will need to be fetch by
	/// the caller.
	/// For a child trie it is its root.
	pub fn root(&self) -> Option<&[u8]> {
		match self {
			ChildInfo::Default(ChildTrie {
				root_end,
				data,
				offset,
			}) => if *root_end > 0 {
				Some(&data[*offset..*root_end])
			} else {
				None
			}
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
	/// Default, but with a root registerd to skip root fetch when querying.
	/// Root is variable length, its length is SCALE encoded at the start.
	CryptoUniqueIdRootApi = 2,
}

impl OwnedChildInfo {
	/// Instantiates info for a default child trie.
	pub fn new_default(mut unique_id: Vec<u8>, root: Option<Vec<u8>>) -> Self {
		let (offset, root_end, encoded) = if let Some(mut root) = root {
			let mut encoded = Encode::encode(&Compact(root.len() as u32));

			let offset = encoded.len();
			encoded.append(&mut root);
			(offset, encoded.len(), Some(encoded)) 
		} else {
			(0, 0, None)
		};
		OwnedChildInfo::Default(OwnedChildTrie {
			root_end,
			offset,
			data: if let Some(mut encoded) = encoded {
				encoded.append(&mut unique_id);
				encoded
			} else {
				unique_id
			}
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&mut self, other: ChildInfo) -> bool {
		match self {
			OwnedChildInfo::Default(owned_child_trie) => owned_child_trie.try_update(other),
		}
	}

	/// Get `ChildInfo` reference to this owned child info.
	pub fn as_ref(&self) -> ChildInfo {
		match self {
			OwnedChildInfo::Default(OwnedChildTrie { data, root_end, offset })
				=> ChildInfo::Default(ChildTrie {
					data: data.as_slice(),
					root_end: *root_end,
					offset: *offset,
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
	/// Encoded data offset (correspond to size of encoded size of root if any). 
	offset: usize,
	/// If root was fetch it can be memoïzed as first part of
	/// the encoded data to avoid querying it explicitly.
	/// This field keep trace of the position of the end of root.
	root_end: usize,

	/// Data containing unique id.
	/// Unique id must but unique and free of any possible key collision
	/// (depending on its storage behavior).
	/// Data can also contain root in first position.
	data: &'a[u8],
}

/// Owned version of default child trie `ChildTrie`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub struct OwnedChildTrie {
	/// See `ChildTrie` reference field documentation.
	offset: usize,

	/// See `ChildTrie` reference field documentation.
	root_end: usize,

	/// See `ChildTrie` reference field documentation.
	data: Vec<u8>,
}

impl OwnedChildTrie {
	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	fn try_update(&mut self, other: ChildInfo) -> bool {
		match other {
			ChildInfo::Default(other) => {
				if self.data[self.root_end..] != other.data[other.root_end..] {
					return false;
				}
				if self.root_end == 0 {
					self.root_end = other.root_end;
					self.data = other.data.to_vec();
				} else {
					debug_assert!(self.data[..self.root_end] == other.data[..other.root_end]);
				}
			},
		}
		true
	}
}

#[test]
fn test_encode() {
	let root = vec![1; 297];
	let unique_id = vec![2; 16];
	let owned_child = OwnedChildInfo::new_default(unique_id.clone(), Some(root.clone()));
	let child = owned_child.as_ref(); 
	let (child_info, child_type) = child.info();
	let child_info = child_info.to_vec();
	assert_eq!(child.keyspace(), &unique_id[..]);
	assert_eq!(child.root(), Some(&root[..]));

	let child = ChildInfo::resolve_child_info(child_type, &child_info[..]).unwrap();
	assert_eq!(child.keyspace(), &unique_id[..]);
	assert_eq!(child.root(), Some(&root[..]));

	let owned_child = OwnedChildInfo::new_default(unique_id.clone(), None);
	let child = owned_child.as_ref(); 
	let (child_info, child_type) = child.info();
	let child_info = child_info.to_vec();
	assert_eq!(child.keyspace(), &unique_id[..]);
	assert_eq!(child.root(), None);

	let child = ChildInfo::resolve_child_info(child_type, &child_info[..]).unwrap();
	assert_eq!(child.keyspace(), &unique_id[..]);
	assert_eq!(child.root(), None);

	let child = ChildInfo::new_default(&unique_id[..]);
	assert_eq!(child.keyspace(), &unique_id[..]);
	assert_eq!(child.root(), None);

}
