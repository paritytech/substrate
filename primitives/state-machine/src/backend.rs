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

//! State machine backends. These manage the code and storage of contracts.

use log::warn;
use hash_db::Hasher;
use codec::Encode;

use sp_core::storage::{ChildInfo, OwnedChildInfo};
use sp_trie::{TrieMut, MemoryDB, trie_types::TrieDBMut};

use crate::{
	trie_backend::TrieBackend,
	trie_backend_essence::TrieBackendStorage,
	UsageInfo, StorageKey, StorageValue, StorageCollection,
};

/// A state backend is used to read state data and can have changes committed
/// to it.
///
/// The clone operation (if implemented) should be cheap.
pub trait Backend<H: Hasher>: std::fmt::Debug {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Storage changes to be applied if committing
	type Transaction: Consolidate + Default + Send;

	/// Type of trie backend storage.
	type TrieBackendStorage: TrieBackendStorage<H>;

	/// Get keyed storage or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error>;

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		self.storage(key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// Get keyed child storage or None if there is nothing associated.
	fn child_storage(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>, Self::Error>;

	/// Get child keyed storage value hash or None if there is nothing associated.
	fn child_storage_hash(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<H::Out>, Self::Error> {
		self.child_storage(storage_key, child_info, key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		Ok(self.child_storage(storage_key, child_info, key)?.is_some())
	}

	/// Return the next key in storage in lexicographic order or `None` if there is no value.
	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error>;

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8]
	) -> Result<Option<StorageKey>, Self::Error>;

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		f: F,
	);

	/// Retrieve all entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.for_key_values_with_prefix(prefix, |k, _v| f(k))
	}

	/// Retrieve all entries keys and values of which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F);


	/// Retrieve all child entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
		f: F,
	);

	/// Calculate the storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit.
	/// Does not include child storage updates.
	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		H::Out: Ord;

	/// Calculate the child storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit. The second argument
	/// is true if child storage root equals default storage root.
	fn child_storage_root<I>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		delta: I,
	) -> (H::Out, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		H::Out: Ord;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(StorageKey, StorageValue)>;

	/// Get all keys with given prefix
	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let mut all = Vec::new();
		self.for_keys_with_prefix(prefix, |k| all.push(k.to_vec()));
		all
	}

	/// Get all keys of child storage with given prefix
	fn child_keys(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
	) -> Vec<StorageKey> {
		let mut all = Vec::new();
		self.for_child_keys_with_prefix(storage_key, child_info, prefix, |k| all.push(k.to_vec()));
		all
	}

	/// Try convert into trie backend.
	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		None
	}

	/// Calculate the storage root, with given delta over what is already stored
	/// in the backend, and produce a "transaction" that can be used to commit.
	/// Does include child storage updates.
	fn full_storage_root<I1, I2i, I2>(
		&self,
		delta: I1,
		child_deltas: I2)
	-> (H::Out, Self::Transaction)
	where
		I1: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		I2i: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		I2: IntoIterator<Item=(StorageKey, I2i, OwnedChildInfo)>,
		H::Out: Ord + Encode,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (storage_key, child_delta, child_info) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(&storage_key[..], child_info.as_ref(), child_delta);
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((storage_key, None));
			} else {
				child_roots.push((storage_key, Some(child_root.encode())));
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta.into_iter().chain(child_roots.into_iter())
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

	/// Query backend usage statistics (i/o, memory)
	///
	/// Not all implementations are expected to be able to do this. In the
	/// case when thay don't, empty statistics is returned.
	fn usage_info(&self) -> UsageInfo {
		UsageInfo::empty()
	}

	/// Wipe the state database.
	fn wipe(&self) -> Result<(), Self::Error> {
		unimplemented!()
	}

	/// Commit given transaction to storage.
	fn commit(&self, _storage_root: H::Out, _transaction: Self::Transaction) -> Result<(), Self::Error> {
		unimplemented!()
	}
}

impl<'a, T: Backend<H>, H: Hasher> Backend<H> for &'a T {
	type Error = T::Error;
	type Transaction = T::Transaction;
	type TrieBackendStorage = T::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		(*self).storage(key)
	}

	fn child_storage(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		(*self).child_storage(storage_key, child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		f: F,
	) {
		(*self).for_keys_in_child_storage(storage_key, child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		(*self).next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		(*self).next_child_storage_key(storage_key, child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		(*self).for_keys_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		(*self).for_child_keys_with_prefix(storage_key, child_info, prefix, f)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		H::Out: Ord,
	{
		(*self).storage_root(delta)
	}

	fn child_storage_root<I>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		delta: I,
	) -> (H::Out, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		H::Out: Ord,
	{
		(*self).child_storage_root(storage_key, child_info, delta)
	}

	fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		(*self).pairs()
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		(*self).for_key_values_with_prefix(prefix, f);
	}

	fn usage_info(&self) -> UsageInfo {
		(*self).usage_info()
	}
 }

/// Trait that allows consolidate two transactions together.
pub trait Consolidate {
	/// Consolidate two transactions into one.
	fn consolidate(&mut self, other: Self);
}

impl Consolidate for () {
	fn consolidate(&mut self, _: Self) {
		()
	}
}

impl Consolidate for Vec<(
		Option<(StorageKey, OwnedChildInfo)>,
		StorageCollection,
	)> {
	fn consolidate(&mut self, mut other: Self) {
		self.append(&mut other);
	}
}

impl<H: Hasher, KF: sp_trie::KeyFunction<H>> Consolidate for sp_trie::GenericMemoryDB<H, KF> {
	fn consolidate(&mut self, other: Self) {
		sp_trie::GenericMemoryDB::consolidate(self, other)
	}
}

/// Insert input pairs into memory db.
pub(crate) fn insert_into_memory_db<H, I>(mdb: &mut MemoryDB<H>, input: I) -> Option<H::Out>
	where
		H: Hasher,
		I: IntoIterator<Item=(StorageKey, StorageValue)>,
{
	let mut root = <H as Hasher>::Out::default();
	{
		let mut trie = TrieDBMut::<H>::new(mdb, &mut root);
		for (key, value) in input {
			if let Err(e) = trie.insert(&key, &value) {
				warn!(target: "trie", "Failed to write to trie: {}", e);
				return None;
			}
		}
	}

	Some(root)
}
