// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Shareable Substrate traits.

#[cfg(feature = "std")]
use crate::{crypto::KeyTypeId, ed25519, sr25519, child_storage_key::ChildStorageKey};
#[cfg(feature = "std")]
use std::{fmt::{Debug, Display}, panic::UnwindSafe};
#[cfg(feature = "std")]
use hash_db::Hasher;

/// Something that generates, stores and provides access to keys.
#[cfg(feature = "std")]
pub trait BareCryptoStore: Send + Sync {
	/// Returns all sr25519 public keys for the given key type.
	fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public>;
	/// Generate a new sr25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn sr25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, String>;
	/// Returns the sr25519 key pair for the given key type and public key combination.
	fn sr25519_key_pair(&self, id: KeyTypeId, pub_key: &sr25519::Public) -> Option<sr25519::Pair>;

	/// Returns all ed25519 public keys for the given key type.
	fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public>;
	/// Generate a new ed25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn ed25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, String>;

	/// Returns the ed25519 key pair for the given key type and public key combination.
	fn ed25519_key_pair(&self, id: KeyTypeId, pub_key: &ed25519::Public) -> Option<ed25519::Pair>;

	/// Insert a new key. This doesn't require any known of the crypto; but a public key must be
	/// manually provided.
	///
	/// Places it into the file system store.
	///
	/// `Err` if there's some sort of weird filesystem error, but should generally be `Ok`.
	fn insert_unknown(&mut self, _key_type: KeyTypeId, _suri: &str, _public: &[u8]) -> Result<(), ()>;

	/// Get the password for this store.
	fn password(&self) -> Option<&str>;
}

/// A pointer to the key store.
#[cfg(feature = "std")]
pub type BareCryptoStorePtr = std::sync::Arc<parking_lot::RwLock<dyn BareCryptoStore>>;

/// Externalities: pinned to specific active address.
#[cfg(feature = "std")]
pub trait Externalities<H: Hasher> {
	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash. This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		self.storage(key).map(|v| H::hash(&v))
	}

	/// Get child storage value hash. This may be optimized for large values.
	fn child_storage_hash(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<H::Out> {
		self.child_storage(storage_key, key).map(|v| H::hash(&v))
	}

	/// Read original runtime storage, ignoring any overlayed changes.
	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Read original runtime child storage, ignoring any overlayed changes.
	fn original_child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>>;

	/// Get original storage value hash, ignoring any overlayed changes.
	/// This may be optimized for large values.
	fn original_storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		self.original_storage(key).map(|v| H::hash(&v))
	}

	/// Get original child storage value hash, ignoring any overlayed changes.
	/// This may be optimized for large values.
	fn original_child_storage_hash(
		&self,
		storage_key: ChildStorageKey,
		key: &[u8],
	) -> Option<H::Out> {
		self.original_child_storage(storage_key, key).map(|v| H::hash(&v))
	}

	/// Read child runtime storage.
	fn child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(&mut self, storage_key: ChildStorageKey, key: Vec<u8>, value: Vec<u8>) {
		self.place_child_storage(storage_key, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(&mut self, storage_key: ChildStorageKey, key: &[u8]) {
		self.place_child_storage(storage_key, key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> bool {
		self.child_storage(storage_key, key).is_some()
	}

	/// Clear an entire child storage.
	fn kill_child_storage(&mut self, storage_key: ChildStorageKey);

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Clear child storage entries which keys are start with the given prefix.
	fn clear_child_prefix(&mut self, storage_key: ChildStorageKey, prefix: &[u8]);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry. Return whether the operation succeeds.
	fn place_child_storage(&mut self, storage_key: ChildStorageKey, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map. This will also update all child storage keys
	/// in the top-level storage map.
	fn storage_root(&mut self) -> H::Out where H::Out: Ord;

	/// Get the trie root of a child storage map. This will also update the value of the child
	/// storage keys in the top-level storage map.
	/// If the storage root equals the default hash as defined by the trie, the key in the top-level
	/// storage map will be removed.
	fn child_storage_root(&mut self, storage_key: ChildStorageKey) -> Vec<u8>;

	/// Get the change trie root of the current storage overlay at a block with given parent.
	fn storage_changes_root(&mut self, parent: H::Out) -> Result<Option<H::Out>, ()> where H::Out: Ord;

	/// Returns offchain externalities extension if present.
	fn offchain(&mut self) -> Option<&mut dyn crate::offchain::Externalities>;

	/// Returns the keystore.
	fn keystore(&self) -> Option<BareCryptoStorePtr>;
}

/// Code execution engine.
#[cfg(feature = "std")]
pub trait CodeExecutor<H: Hasher>: Sized + Send + Sync {
	/// Externalities error type.
	type Error: Display + Debug + Send + 'static;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<
		E: Externalities<H>,
		R: codec::Codec + PartialEq,
		NC: FnOnce() -> Result<R, String> + UnwindSafe,
	>(
		&self,
		ext: &mut E,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<crate::NativeOrEncoded<R>, Self::Error>, bool);
}
