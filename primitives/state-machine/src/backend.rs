// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! State machine backends. These manage the code and storage of contracts.

#[cfg(feature = "std")]
use crate::trie_backend::TrieBackend;
use crate::{
	trie_backend_essence::TrieBackendStorage, ChildStorageCollection, StorageCollection,
	StorageKey, StorageValue, UsageInfo,
};
use codec::Encode;
use core::marker::PhantomData;
use hash_db::Hasher;
use sp_core::storage::{ChildInfo, StateVersion, TrackedStorageKey};
#[cfg(feature = "std")]
use sp_core::traits::RuntimeCode;
use sp_std::vec::Vec;

/// A struct containing arguments for iterating over the storage.
#[derive(Default)]
#[non_exhaustive]
pub struct IterArgs<'a> {
	/// The prefix of the keys over which to iterate.
	pub prefix: Option<&'a [u8]>,

	/// The prefix from which to start the iteration from.
	///
	/// This is inclusive and the iteration will include the key which is specified here.
	pub start_at: Option<&'a [u8]>,

	/// The info of the child trie over which to iterate over.
	pub child_info: Option<ChildInfo>,

	/// Whether to stop iteration when a missing trie node is reached.
	///
	/// When a missing trie node is reached the iterator will:
	///   - return an error if this is set to `false` (default)
	///   - return `None` if this is set to `true`
	pub stop_on_incomplete_database: bool,
}

/// A trait for a raw storage iterator.
pub trait StorageIterator<H>
where
	H: Hasher,
{
	/// The state backend over which the iterator is iterating.
	type Backend;

	/// The error type.
	type Error;

	/// Fetches the next key from the storage.
	fn next_key(
		&mut self,
		backend: &Self::Backend,
	) -> Option<core::result::Result<StorageKey, Self::Error>>;

	/// Fetches the next key and value from the storage.
	fn next_pair(
		&mut self,
		backend: &Self::Backend,
	) -> Option<core::result::Result<(StorageKey, StorageValue), Self::Error>>;

	/// Returns whether the end of iteration was reached without an error.
	fn was_complete(&self) -> bool;
}

/// An iterator over storage keys and values.
pub struct PairsIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H>,
{
	backend: Option<&'a I::Backend>,
	raw_iter: I,
	_phantom: PhantomData<H>,
}

impl<'a, H, I> Iterator for PairsIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H>,
{
	type Item = Result<(Vec<u8>, Vec<u8>), <I as StorageIterator<H>>::Error>;
	fn next(&mut self) -> Option<Self::Item> {
		self.raw_iter.next_pair(self.backend.as_ref()?)
	}
}

impl<'a, H, I> Default for PairsIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H> + Default,
{
	fn default() -> Self {
		Self {
			backend: Default::default(),
			raw_iter: Default::default(),
			_phantom: Default::default(),
		}
	}
}

/// An iterator over storage keys.
pub struct KeysIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H>,
{
	backend: Option<&'a I::Backend>,
	raw_iter: I,
	_phantom: PhantomData<H>,
}

impl<'a, H, I> Iterator for KeysIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H>,
{
	type Item = Result<Vec<u8>, <I as StorageIterator<H>>::Error>;
	fn next(&mut self) -> Option<Self::Item> {
		self.raw_iter.next_key(self.backend.as_ref()?)
	}
}

impl<'a, H, I> Default for KeysIter<'a, H, I>
where
	H: Hasher,
	I: StorageIterator<H> + Default,
{
	fn default() -> Self {
		Self {
			backend: Default::default(),
			raw_iter: Default::default(),
			_phantom: Default::default(),
		}
	}
}

/// A state backend is used to read state data and can have changes committed
/// to it.
///
/// The clone operation (if implemented) should be cheap.
pub trait Backend<H: Hasher>: sp_std::fmt::Debug {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Storage changes to be applied if committing
	type Transaction: Consolidate + Default + Send;

	/// Type of trie backend storage.
	type TrieBackendStorage: TrieBackendStorage<H, Overlay = Self::Transaction>;

	/// Type of the raw storage iterator.
	type RawIter: StorageIterator<H, Backend = Self, Error = Self::Error>;

	/// Get keyed storage or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error>;

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error>;

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
	) -> Result<Option<H::Out>, Self::Error>;

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage_hash(key)?.is_some())
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		Ok(self.child_storage_hash(child_info, key)?.is_some())
	}

	/// Return the next key in storage in lexicographic order or `None` if there is no value.
	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error>;

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error>;

	/// Iterate over storage starting at key, for a given prefix and child trie.
	/// Aborts as soon as `f` returns false.
	/// Warning, this fails at first error when usual iteration skips errors.
	/// If `allow_missing` is true, iteration stops when it reaches a missing trie node.
	/// Otherwise an error is produced.
	///
	/// Returns `true` if trie end is reached.
	// TODO: Remove this.
	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		mut f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		let args = IterArgs {
			child_info: child_info.cloned(),
			prefix,
			start_at,
			stop_on_incomplete_database: allow_missing,
			..IterArgs::default()
		};
		let mut iter = self.pairs(args)?;
		while let Some(key_value) = iter.next() {
			let (key, value) = key_value?;
			if !f(key, value) {
				return Ok(false)
			}
		}
		Ok(iter.raw_iter.was_complete())
	}

	/// Retrieve all entries keys of storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	// TODO: Remove this.
	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		mut f: F,
	) -> Result<(), Self::Error> {
		let args =
			IterArgs { child_info: child_info.cloned(), prefix, start_at, ..IterArgs::default() };

		for key in self.keys(args)? {
			if !f(&key?) {
				return Ok(())
			}
		}
		Ok(())
	}

	/// Retrieve all entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	// TODO: Remove this.
	fn for_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		prefix: &[u8],
		mut f: F,
	) -> Result<(), Self::Error> {
		let args = IterArgs { prefix: Some(prefix), ..IterArgs::default() };
		self.keys(args)?.try_for_each(|key| {
			f(&key?);
			Ok(())
		})
	}

	/// Retrieve all entries keys and values of which start with the given prefix and
	/// call `f` for each of those keys.
	// TODO: Remove this.
	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(
		&self,
		prefix: &[u8],
		mut f: F,
	) -> Result<(), Self::Error> {
		let args = IterArgs { prefix: Some(prefix), ..IterArgs::default() };
		self.pairs(args)?.try_for_each(|key_value| {
			let (key, value) = key_value?;
			f(&key, &value);
			Ok(())
		})
	}

	/// Retrieve all child entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	// TODO: Remove this.
	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		mut f: F,
	) -> Result<(), Self::Error> {
		let args = IterArgs {
			child_info: Some(child_info.clone()),
			prefix: Some(prefix),
			..IterArgs::default()
		};
		self.keys(args)?.try_for_each(|key| {
			f(&key?);
			Ok(())
		})
	}

	/// Calculate the storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit.
	/// Does not include child storage updates.
	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord;

	/// Calculate the child storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit. The second argument
	/// is true if child storage root equals default storage root.
	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, Self::Transaction)
	where
		H::Out: Ord;

	/// Returns a lifetimeless raw storage iterator.
	fn raw_iter(&self, args: IterArgs) -> Result<Self::RawIter, Self::Error>;

	/// Get an iterator over key/value pairs.
	fn pairs<'a>(&'a self, args: IterArgs) -> Result<PairsIter<'a, H, Self::RawIter>, Self::Error> {
		Ok(PairsIter {
			backend: Some(self),
			raw_iter: self.raw_iter(args)?,
			_phantom: Default::default(),
		})
	}

	/// Get an iterator over keys.
	fn keys<'a>(&'a self, args: IterArgs) -> Result<KeysIter<'a, H, Self::RawIter>, Self::Error> {
		Ok(KeysIter {
			backend: Some(self),
			raw_iter: self.raw_iter(args)?,
			_phantom: Default::default(),
		})
	}

	/// Calculate the storage root, with given delta over what is already stored
	/// in the backend, and produce a "transaction" that can be used to commit.
	/// Does include child storage updates.
	fn full_storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		child_deltas: impl Iterator<
			Item = (&'a ChildInfo, impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>),
		>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord + Encode,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (child_info, child_delta) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(child_info, child_delta, state_version);
			let prefixed_storage_key = child_info.prefixed_storage_key();
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((prefixed_storage_key.into_inner(), None));
			} else {
				child_roots.push((prefixed_storage_key.into_inner(), Some(child_root.encode())));
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta
				.map(|(k, v)| (k, v.as_ref().map(|v| &v[..])))
				.chain(child_roots.iter().map(|(k, v)| (&k[..], v.as_ref().map(|v| &v[..])))),
			state_version,
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

	/// Register stats from overlay of state machine.
	///
	/// By default nothing is registered.
	fn register_overlay_stats(&self, _stats: &crate::stats::StateMachineStats);

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
	fn commit(
		&self,
		_: H::Out,
		_: Self::Transaction,
		_: StorageCollection,
		_: ChildStorageCollection,
	) -> Result<(), Self::Error> {
		unimplemented!()
	}

	/// Get the read/write count of the db
	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!()
	}

	/// Get the read/write count of the db
	fn reset_read_write_count(&self) {
		unimplemented!()
	}

	/// Get the whitelist for tracking db reads/writes
	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		Default::default()
	}

	/// Update the whitelist for tracking db reads/writes
	fn set_whitelist(&self, _: Vec<TrackedStorageKey>) {}

	/// Estimate proof size
	fn proof_size(&self) -> Option<u32> {
		unimplemented!()
	}

	/// Extend storage info for benchmarking db
	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		unimplemented!()
	}
}

/// Something that can be converted into a [`TrieBackend`].
#[cfg(feature = "std")]
pub trait AsTrieBackend<H: Hasher, C = sp_trie::cache::LocalTrieCache<H>> {
	/// Type of trie backend storage.
	type TrieBackendStorage: TrieBackendStorage<H>;

	/// Return the type as [`TrieBackend`].
	fn as_trie_backend(&self) -> &TrieBackend<Self::TrieBackendStorage, H, C>;
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

impl Consolidate for Vec<(Option<ChildInfo>, StorageCollection)> {
	fn consolidate(&mut self, mut other: Self) {
		self.append(&mut other);
	}
}

impl<H, KF> Consolidate for sp_trie::GenericMemoryDB<H, KF>
where
	H: Hasher,
	KF: sp_trie::KeyFunction<H>,
{
	fn consolidate(&mut self, other: Self) {
		sp_trie::GenericMemoryDB::consolidate(self, other)
	}
}

/// Wrapper to create a [`RuntimeCode`] from a type that implements [`Backend`].
#[cfg(feature = "std")]
pub struct BackendRuntimeCode<'a, B, H> {
	backend: &'a B,
	_marker: PhantomData<H>,
}

#[cfg(feature = "std")]
impl<'a, B: Backend<H>, H: Hasher> sp_core::traits::FetchRuntimeCode
	for BackendRuntimeCode<'a, B, H>
{
	fn fetch_runtime_code(&self) -> Option<std::borrow::Cow<[u8]>> {
		self.backend
			.storage(sp_core::storage::well_known_keys::CODE)
			.ok()
			.flatten()
			.map(Into::into)
	}
}

#[cfg(feature = "std")]
impl<'a, B: Backend<H>, H: Hasher> BackendRuntimeCode<'a, B, H>
where
	H::Out: Encode,
{
	/// Create a new instance.
	pub fn new(backend: &'a B) -> Self {
		Self { backend, _marker: PhantomData }
	}

	/// Return the [`RuntimeCode`] build from the wrapped `backend`.
	pub fn runtime_code(&self) -> Result<RuntimeCode, &'static str> {
		let hash = self
			.backend
			.storage_hash(sp_core::storage::well_known_keys::CODE)
			.ok()
			.flatten()
			.ok_or("`:code` hash not found")?
			.encode();
		let heap_pages = self
			.backend
			.storage(sp_core::storage::well_known_keys::HEAP_PAGES)
			.ok()
			.flatten()
			.and_then(|d| codec::Decode::decode(&mut &d[..]).ok());

		Ok(RuntimeCode { code_fetcher: self, hash, heap_pages })
	}
}
