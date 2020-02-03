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

use codec::{Decode, Encode, Output};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use sp_debug_derive::RuntimeDebug;
use ref_cast::RefCast;

use sp_std::{vec, vec::Vec, borrow::Cow, borrow::Borrow,
	borrow::ToOwned, convert::TryInto, ops::Deref};

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

#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, RefCast)]
/// Information related to a child state.
pub struct ChildInfo([u8]);

impl Encode for ChildInfo {
	fn encode_to<T: Output>(&self, output: &mut T) {
		self.0.encode_to(output)
	}
}

/// Owned version of `ChildInfo`.
/// To be use in persistence layers.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encode, Decode)]
#[repr(transparent)]
pub struct OwnedChildInfo(Vec<u8>);

impl ToOwned for ChildInfo {
	type Owned = OwnedChildInfo;

	fn to_owned(&self) -> Self::Owned {
		OwnedChildInfo(self.0.to_owned())
	}
}

impl Borrow<ChildInfo> for OwnedChildInfo {
	#[inline]
	fn borrow(&self) -> &ChildInfo {
		let data: &[u8] = self.0.borrow();
		ChildInfo::ref_cast(data)
	}
}

impl Deref for OwnedChildInfo {
	type Target = ChildInfo;

	#[inline]
	fn deref(&self) -> &ChildInfo {
		self.borrow()
	}
}

impl ChildInfo {
	/// Create child info from a linear byte packed value and a given type. 
	pub fn resolve_child_info(data: &[u8]) -> Option<&Self> {
		match ChildType::read_type(data) {
			Some(x) if x == ChildType::CryptoUniqueId => Some(
				ChildInfo::ref_cast(data)
			),
			_ => None,
		}
	}

	/// Instantiates information for a child trie.
	/// No check is done on consistency.
	pub fn new_unchecked(data: &[u8]) -> &Self {
		ChildInfo::ref_cast(data)
	}

	/// Top trie defined as the unique crypto id trie with
	/// 0 length unique id.
	pub fn top_trie() -> &'static Self {
		Self::new_unchecked(b"\x01\x00\x00\x00")
	}

	/// Return a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		let child_type = ChildType::read_type_unchecked(&self.0);
		(&self.0, child_type as u32)
	}

	/// Return byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match ChildType::read_type_unchecked(&self.0) {
			ChildType::CryptoUniqueId => &self.0[4..],
		}
	}

	fn child_type(&self) -> ChildType {
		ChildType::read_type_unchecked(&self.0[..])
	}
}

/// Type of child, it is encoded in the four first byte of the
/// encoded child info (LE u32).
/// It does not strictly define different child type, it can also
/// be related to technical consideration or api variant.
#[repr(u32)]
#[derive(Clone, Copy, PartialEq)]
pub enum ChildType {
	/// Default, it uses a cryptographic strong unique id as input.
	/// All bytes following the type in encoded form are this unique
	/// id.
	/// If the trie got a unique id of length 0 it is considered
	/// as a top child trie.
	CryptoUniqueId = 1,
}

impl ChildType {
	fn new(repr: u32) -> Option<ChildType> {
		Some(match repr {
			r if r == ChildType::CryptoUniqueId as u32 => ChildType::CryptoUniqueId,
			_ => return None,
		})
	}

	/// Try to read type from child definition.
	pub fn read_type(slice: &[u8]) -> Option<Self> {
		if slice.len() < 4 {
			return None;
		}
		slice[..4].try_into().ok()
			.map(|b| u32::from_le_bytes(b))
			.and_then(|b| ChildType::new(b))
	}

	fn read_type_unchecked(slice: &[u8]) -> Self {
		slice[..4].try_into().ok()
			.map(|b| u32::from_le_bytes(b))
			.and_then(|b| ChildType::new(b))
			.expect("This function is only called on initialized child info.")
	}
}

impl OwnedChildInfo {
	/// Create a new child trie information for default
	/// child type.
	pub fn new_default(unique_id: &[u8]) -> Self {
		let mut vec = vec![0; unique_id.len() + 4];
		vec[..4].copy_from_slice(&(ChildType::CryptoUniqueId as u32).to_le_bytes()[..]);
		vec[4..].copy_from_slice(unique_id);
		OwnedChildInfo(vec)
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	pub fn try_update(&self, other: &ChildInfo) -> bool {
		match self.child_type() {
			ChildType::CryptoUniqueId => {
				match other.child_type() {
					ChildType::CryptoUniqueId => self.deref() == other,
				}
			},
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_top_trie() {
		let top_trie = ChildInfo::top_trie();
		assert!(top_trie.child_type() == ChildType::CryptoUniqueId);
		assert_eq!(top_trie.encode(), top_trie.to_owned().encode());
		// 16 compact enc 4 and le 1 u32
		assert!(top_trie.encode() == vec![16, 1, 0, 0, 0]);
		assert_eq!(top_trie.keyspace(), &[]);
	}
}
