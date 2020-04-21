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

use hash_db::Hasher;
use codec::{Decode, Encode};
use sp_core::{traits::RuntimeCode, storage::{ChildInfo, well_known_keys}};

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
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>, Self::Error>;

	/// Get child keyed storage value hash or None if there is nothing associated.
	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<H::Out>, Self::Error> {
		self.child_storage(child_info, key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		Ok(self.child_storage(child_info, key)?.is_some())
	}

	/// Return the next key in storage in lexicographic order or `None` if there is no value.
	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error>;

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8]
	) -> Result<Option<StorageKey>, Self::Error>;

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
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
		child_info: &ChildInfo,
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
		child_info: &ChildInfo,
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
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<StorageKey> {
		let mut all = Vec::new();
		self.for_child_keys_with_prefix(child_info, prefix, |k| all.push(k.to_vec()));
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
		I2: IntoIterator<Item=(ChildInfo, I2i)>,
		H::Out: Ord + Encode,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (child_info, child_delta) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(&child_info, child_delta);
			let prefixed_storage_key = child_info.prefixed_storage_key();
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((prefixed_storage_key.into_inner(), None));
			} else {
				child_roots.push((prefixed_storage_key.into_inner(), Some(child_root.encode())));
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta.into_iter().chain(child_roots.into_iter())
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

	/// Register stats from overlay of state machine.
	///
	/// By default nothing is registered.
	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats);

	/// Query backend usage statistics (i/o, memory)
	///
	/// Not all implementations are expected to be able to do this. In the
	/// case when they don't, empty statistics is returned.
	fn usage_info(&self) -> UsageInfo;

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
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		(*self).child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		(*self).for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		(*self).next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		(*self).next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		(*self).for_keys_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		(*self).for_child_keys_with_prefix(child_info, prefix, f)
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
		child_info: &ChildInfo,
		delta: I,
	) -> (H::Out, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
		H::Out: Ord,
	{
		(*self).child_storage_root(child_info, delta)
	}

	fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		(*self).pairs()
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		(*self).for_key_values_with_prefix(prefix, f);
	}

	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) {	}

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
		Option<ChildInfo>,
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
#[cfg(test)]
pub(crate) fn insert_into_memory_db<H, I>(mdb: &mut sp_trie::MemoryDB<H>, input: I) -> Option<H::Out>
	where
		H: Hasher,
		I: IntoIterator<Item=(StorageKey, StorageValue)>,
{
	use sp_trie::{TrieMut, trie_types::TrieDBMut};

	let mut root = <H as Hasher>::Out::default();
	{
		let mut trie = TrieDBMut::<H>::new(mdb, &mut root);
		for (key, value) in input {
			if let Err(e) = trie.insert(&key, &value) {
				log::warn!(target: "trie", "Failed to write to trie: {}", e);
				return None;
			}
		}
	}

	Some(root)
}

/// Wrapper to create a [`RuntimeCode`] from a type that implements [`Backend`].
pub struct BackendRuntimeCode<'a, B, H> {
	backend: &'a B,
	_marker: std::marker::PhantomData<H>,
}

impl<'a, B: Backend<H>, H: Hasher> sp_core::traits::FetchRuntimeCode for
	BackendRuntimeCode<'a, B, H>
{
	fn fetch_runtime_code<'b>(&'b self) -> Option<std::borrow::Cow<'b, [u8]>> {
		self.backend.storage(well_known_keys::CODE).ok().flatten().map(Into::into)
	}
}

impl<'a, B: Backend<H>, H: Hasher> BackendRuntimeCode<'a, B, H> where H::Out: Encode {
	/// Create a new instance.
	pub fn new(backend: &'a B) -> Self {
		Self {
			backend,
			_marker: std::marker::PhantomData,
		}
	}

	/// Return the [`RuntimeCode`] build from the wrapped `backend`.
	pub fn runtime_code(&self) -> Result<RuntimeCode, &'static str> {
		let hash = self.backend.storage_hash(well_known_keys::CODE)
			.ok()
			.flatten()
			.ok_or("`:code` hash not found")?
			.encode();
		let heap_pages = self.backend.storage(well_known_keys::HEAP_PAGES)
			.ok()
			.flatten()
			.and_then(|d| Decode::decode(&mut &d[..]).ok());

		Ok(RuntimeCode { code_fetcher: self, hash, heap_pages })
	}
}
