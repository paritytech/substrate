// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Trie-based state machine backend essence used to read values
//! from storage.

use crate::{
	backend::Consolidate, debug, trie_backend::AsLocalTrieCache, warn, StorageKey, StorageValue,
};
use codec::Codec;
use hash_db::{self, AsHashDB, HashDB, HashDBRef, Hasher, Prefix};
#[cfg(feature = "std")]
use parking_lot::RwLock;
use sp_core::storage::{ChildInfo, ChildType, StateVersion};
#[cfg(not(feature = "std"))]
use sp_std::marker::PhantomData;
use sp_std::{boxed::Box, vec::Vec};
#[cfg(feature = "std")]
use sp_trie::recorder::Recorder;
use sp_trie::{
	child_delta_trie_root, delta_trie_root, empty_child_trie_root, read_child_trie_hash,
	read_child_trie_value, read_trie_value,
	trie_types::{TrieDBBuilder, TrieError},
	DBValue, KeySpacedDB, NodeCodec, Trie, TrieCache, TrieDBIterator, TrieDBKeyIterator,
	TrieRecorder,
};
#[cfg(feature = "std")]
use std::{collections::HashMap, sync::Arc};

// In this module, we only use layout for read operation and empty root,
// where V1 and V0 are equivalent.
use sp_trie::LayoutV1 as Layout;

#[cfg(not(feature = "std"))]
macro_rules! format {
	( $message:expr, $( $arg:expr )* ) => {
		{
			$( let _ = &$arg; )*
			crate::DefaultError
		}
	};
}

type Result<V> = sp_std::result::Result<V, crate::DefaultError>;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

/// Local cache for child root.
#[cfg(feature = "std")]
pub(crate) struct Cache<H> {
	pub child_root: HashMap<Vec<u8>, Option<H>>,
}

#[cfg(feature = "std")]
impl<H> Cache<H> {
	fn new() -> Self {
		Cache { child_root: HashMap::new() }
	}
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorage<H>, H: Hasher, C> {
	storage: S,
	root: H::Out,
	empty: H::Out,
	#[cfg(feature = "std")]
	pub(crate) cache: Arc<RwLock<Cache<H::Out>>>,
	#[cfg(feature = "std")]
	pub(crate) trie_node_cache: Option<C>,
	#[cfg(feature = "std")]
	pub(crate) recorder: Option<Recorder<H>>,
	#[cfg(not(feature = "std"))]
	_phantom: PhantomData<C>,
}

impl<S: TrieBackendStorage<H>, H: Hasher, C> TrieBackendEssence<S, H, C> {
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackendEssence {
			storage,
			root,
			empty: H::hash(&[0u8]),
			#[cfg(feature = "std")]
			cache: Arc::new(RwLock::new(Cache::new())),
			#[cfg(feature = "std")]
			trie_node_cache: None,
			#[cfg(feature = "std")]
			recorder: None,
			#[cfg(not(feature = "std"))]
			_phantom: PhantomData,
		}
	}

	/// Create new trie-based backend.
	#[cfg(feature = "std")]
	pub fn new_with_cache_and_recorder(
		storage: S,
		root: H::Out,
		cache: Option<C>,
		recorder: Option<Recorder<H>>,
	) -> Self {
		TrieBackendEssence {
			storage,
			root,
			empty: H::hash(&[0u8]),
			cache: Arc::new(RwLock::new(Cache::new())),
			trie_node_cache: cache,
			recorder,
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		&self.storage
	}

	/// Get backend storage mutable reference.
	pub fn backend_storage_mut(&mut self) -> &mut S {
		&mut self.storage
	}

	/// Get trie root.
	pub fn root(&self) -> &H::Out {
		&self.root
	}

	/// Set trie root. This is useful for testing.
	pub fn set_root(&mut self, root: H::Out) {
		// If root did change so can have cached content.
		self.reset_cache();
		self.root = root;
	}

	#[cfg(feature = "std")]
	fn reset_cache(&mut self) {
		self.cache = Arc::new(RwLock::new(Cache::new()));
	}

	#[cfg(not(feature = "std"))]
	fn reset_cache(&mut self) {}

	/// Consumes self and returns underlying storage.
	pub fn into_storage(self) -> S {
		self.storage
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H>> TrieBackendEssence<S, H, C> {
	/// Call the given closure passing it the recorder and the cache.
	///
	/// If the given `storage_root` is `None`, `self.root` will be used.
	#[cfg(feature = "std")]
	fn with_recorder_and_cache<R>(
		&self,
		storage_root: Option<H::Out>,
		callback: impl FnOnce(
			Option<&mut dyn TrieRecorder<H::Out>>,
			Option<&mut dyn TrieCache<NodeCodec<H>>>,
		) -> R,
	) -> R {
		let storage_root = storage_root.unwrap_or_else(|| self.root);
		let mut recorder = self.recorder.as_ref().map(|r| r.as_trie_recorder(storage_root));
		let recorder = match recorder.as_mut() {
			Some(recorder) => Some(recorder as &mut dyn TrieRecorder<H::Out>),
			None => None,
		};

		let mut cache = self
			.trie_node_cache
			.as_ref()
			.map(|c| c.as_local_trie_cache().as_trie_db_cache(storage_root));
		let cache = cache.as_mut().map(|c| c as _);

		callback(recorder, cache)
	}

	#[cfg(not(feature = "std"))]
	fn with_recorder_and_cache<R>(
		&self,
		_: Option<H::Out>,
		callback: impl FnOnce(
			Option<&mut dyn TrieRecorder<H::Out>>,
			Option<&mut dyn TrieCache<NodeCodec<H>>>,
		) -> R,
	) -> R {
		callback(None, None)
	}

	/// Call the given closure passing it the recorder and the cache.
	///
	/// This function must only be used when the operation in `callback` is
	/// calculating a `storage_root`. It is expected that `callback` returns
	/// the new storage root. This is required to register the changes in the cache
	/// for the correct storage root. The given `storage_root` corresponds to the root of the "old"
	/// trie. If the value is not given, `self.root` is used.
	#[cfg(feature = "std")]
	fn with_recorder_and_cache_for_storage_root<R>(
		&self,
		storage_root: Option<H::Out>,
		callback: impl FnOnce(
			Option<&mut dyn TrieRecorder<H::Out>>,
			Option<&mut dyn TrieCache<NodeCodec<H>>>,
		) -> (Option<H::Out>, R),
	) -> R {
		let storage_root = storage_root.unwrap_or_else(|| self.root);
		let mut recorder = self.recorder.as_ref().map(|r| r.as_trie_recorder(storage_root));
		let recorder = match recorder.as_mut() {
			Some(recorder) => Some(recorder as &mut dyn TrieRecorder<H::Out>),
			None => None,
		};

		let result = if let Some(local_cache) = self.trie_node_cache.as_ref() {
			let mut cache = local_cache.as_local_trie_cache().as_trie_db_mut_cache();

			let (new_root, r) = callback(recorder, Some(&mut cache));

			if let Some(new_root) = new_root {
				cache.merge_into(local_cache.as_local_trie_cache(), new_root);
			}

			r
		} else {
			callback(recorder, None).1
		};

		result
	}

	#[cfg(not(feature = "std"))]
	fn with_recorder_and_cache_for_storage_root<R>(
		&self,
		_: Option<H::Out>,
		callback: impl FnOnce(
			Option<&mut dyn TrieRecorder<H::Out>>,
			Option<&mut dyn TrieCache<NodeCodec<H>>>,
		) -> (Option<H::Out>, R),
	) -> R {
		callback(None, None).1
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync>
	TrieBackendEssence<S, H, C>
where
	H::Out: Codec + Ord,
{
	/// Return the next key in the trie i.e. the minimum key that is strictly superior to `key` in
	/// lexicographic order.
	pub fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>> {
		self.next_storage_key_from_root(&self.root, None, key)
	}

	/// Access the root of the child storage in its parent trie
	fn child_root(&self, child_info: &ChildInfo) -> Result<Option<H::Out>> {
		#[cfg(feature = "std")]
		{
			if let Some(result) = self.cache.read().child_root.get(child_info.storage_key()) {
				return Ok(*result)
			}
		}

		let result = self.storage(child_info.prefixed_storage_key().as_slice())?.map(|r| {
			let mut hash = H::Out::default();

			// root is fetched from DB, not writable by runtime, so it's always valid.
			hash.as_mut().copy_from_slice(&r[..]);

			hash
		});

		#[cfg(feature = "std")]
		{
			self.cache.write().child_root.insert(child_info.storage_key().to_vec(), result);
		}

		Ok(result)
	}

	/// Return the next key in the child trie i.e. the minimum key that is strictly superior to
	/// `key` in lexicographic order.
	pub fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let child_root = match self.child_root(child_info)? {
			Some(child_root) => child_root,
			None => return Ok(None),
		};

		self.next_storage_key_from_root(&child_root, Some(child_info), key)
	}

	/// Return next key from main trie or child trie by providing corresponding root.
	fn next_storage_key_from_root(
		&self,
		root: &H::Out,
		child_info: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let dyn_eph: &dyn HashDBRef<_, _>;
		let keyspace_eph;
		if let Some(child_info) = child_info.as_ref() {
			keyspace_eph = KeySpacedDB::new(self, child_info.keyspace());
			dyn_eph = &keyspace_eph;
		} else {
			dyn_eph = self;
		}

		self.with_recorder_and_cache(Some(*root), |recorder, cache| {
			let trie = TrieDBBuilder::<H>::new(dyn_eph, root)
				.with_optional_recorder(recorder)
				.with_optional_cache(cache)
				.build();

			let mut iter = trie.key_iter().map_err(|e| format!("TrieDB iteration error: {}", e))?;

			// The key just after the one given in input, basically `key++0`.
			// Note: We are sure this is the next key if:
			// * size of key has no limit (i.e. we can always add 0 to the path),
			// * and no keys can be inserted between `key` and `key++0` (this is ensured by sp-io).
			let mut potential_next_key = Vec::with_capacity(key.len() + 1);
			potential_next_key.extend_from_slice(key);
			potential_next_key.push(0);

			iter.seek(&potential_next_key)
				.map_err(|e| format!("TrieDB iterator seek error: {}", e))?;

			let next_element = iter.next();

			let next_key = if let Some(next_element) = next_element {
				let next_key =
					next_element.map_err(|e| format!("TrieDB iterator next error: {}", e))?;
				Some(next_key)
			} else {
				None
			};

			Ok(next_key)
		})
	}

	/// Returns the hash value
	pub fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>> {
		let map_e = |e| format!("Trie lookup error: {}", e);

		self.with_recorder_and_cache(None, |recorder, cache| {
			TrieDBBuilder::new(self, &self.root)
				.with_optional_cache(cache)
				.with_optional_recorder(recorder)
				.build()
				.get_hash(key)
				.map_err(map_e)
		})
	}

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>> {
		let map_e = |e| format!("Trie lookup error: {}", e);

		self.with_recorder_and_cache(None, |recorder, cache| {
			read_trie_value::<Layout<H>, _>(self, &self.root, key, recorder, cache).map_err(map_e)
		})
	}

	/// Returns the hash value
	pub fn child_storage_hash(&self, child_info: &ChildInfo, key: &[u8]) -> Result<Option<H::Out>> {
		let child_root = match self.child_root(child_info)? {
			Some(root) => root,
			None => return Ok(None),
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		self.with_recorder_and_cache(Some(child_root), |recorder, cache| {
			read_child_trie_hash::<Layout<H>, _>(
				child_info.keyspace(),
				self,
				&child_root,
				key,
				recorder,
				cache,
			)
			.map_err(map_e)
		})
	}

	/// Get the value of child storage at given key.
	pub fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>> {
		let child_root = match self.child_root(child_info)? {
			Some(root) => root,
			None => return Ok(None),
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		self.with_recorder_and_cache(Some(child_root), |recorder, cache| {
			read_child_trie_value::<Layout<H>, _>(
				child_info.keyspace(),
				self,
				&child_root,
				key,
				recorder,
				cache,
			)
			.map_err(map_e)
		})
	}

	/// Retrieve all entries keys of storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	///
	/// Returns `true` when all keys were iterated.
	pub fn apply_to_key_values_while(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: impl FnMut(Vec<u8>, Vec<u8>) -> bool,
		allow_missing_nodes: bool,
	) -> Result<bool> {
		let root = if let Some(child_info) = child_info.as_ref() {
			match self.child_root(child_info)? {
				Some(child_root) => child_root,
				None => return Ok(true),
			}
		} else {
			self.root
		};

		self.trie_iter_inner(&root, prefix, f, child_info, start_at, allow_missing_nodes)
	}

	/// Retrieve all entries keys of a storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	pub fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
	) {
		let root = if let Some(child_info) = child_info.as_ref() {
			match self.child_root(child_info) {
				Ok(Some(v)) => v,
				// If the child trie doesn't exist, there is no need to continue.
				Ok(None) => return,
				Err(e) => {
					debug!(target: "trie", "Error while iterating child storage: {}", e);
					return
				},
			}
		} else {
			self.root
		};

		self.trie_iter_key_inner(&root, prefix, f, child_info, start_at)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_child_keys_with_prefix(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		mut f: impl FnMut(&[u8]),
	) {
		let root = match self.child_root(child_info) {
			Ok(Some(v)) => v,
			// If the child trie doesn't exist, there is no need to continue.
			Ok(None) => return,
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return
			},
		};

		self.trie_iter_key_inner(
			&root,
			Some(prefix),
			|k| {
				f(k);
				true
			},
			Some(child_info),
			None,
		)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.trie_iter_key_inner(
			&self.root,
			Some(prefix),
			|k| {
				f(k);
				true
			},
			None,
			None,
		)
	}

	fn trie_iter_key_inner<F: FnMut(&[u8]) -> bool>(
		&self,
		root: &H::Out,
		maybe_prefix: Option<&[u8]>,
		mut f: F,
		child_info: Option<&ChildInfo>,
		maybe_start_at: Option<&[u8]>,
	) {
		let mut iter = move |db| -> sp_std::result::Result<(), Box<TrieError<H::Out>>> {
			self.with_recorder_and_cache(Some(*root), |recorder, cache| {
				let trie = TrieDBBuilder::<H>::new(db, root)
					.with_optional_recorder(recorder)
					.with_optional_cache(cache)
					.build();
				let prefix = maybe_prefix.unwrap_or(&[]);
				let iter = match maybe_start_at {
					Some(start_at) =>
						TrieDBKeyIterator::new_prefixed_then_seek(&trie, prefix, start_at),
					None => TrieDBKeyIterator::new_prefixed(&trie, prefix),
				}?;

				for x in iter {
					let key = x?;

					debug_assert!(maybe_prefix
						.as_ref()
						.map(|prefix| key.starts_with(prefix))
						.unwrap_or(true));

					if !f(&key) {
						break
					}
				}

				Ok(())
			})
		};

		let result = if let Some(child_info) = child_info {
			let db = KeySpacedDB::new(self, child_info.keyspace());
			iter(&db)
		} else {
			iter(self)
		};
		if let Err(e) = result {
			debug!(target: "trie", "Error while iterating by prefix: {}", e);
		}
	}

	fn trie_iter_inner<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		root: &H::Out,
		prefix: Option<&[u8]>,
		mut f: F,
		child_info: Option<&ChildInfo>,
		start_at: Option<&[u8]>,
		allow_missing_nodes: bool,
	) -> Result<bool> {
		let mut iter = move |db| -> sp_std::result::Result<bool, Box<TrieError<H::Out>>> {
			self.with_recorder_and_cache(Some(*root), |recorder, cache| {
				let trie = TrieDBBuilder::<H>::new(db, root)
					.with_optional_recorder(recorder)
					.with_optional_cache(cache)
					.build();

				let prefix = prefix.unwrap_or(&[]);
				let iterator = if let Some(start_at) = start_at {
					TrieDBIterator::new_prefixed_then_seek(&trie, prefix, start_at)?
				} else {
					TrieDBIterator::new_prefixed(&trie, prefix)?
				};
				for x in iterator {
					let (key, value) = x?;

					debug_assert!(key.starts_with(prefix));

					if !f(key, value) {
						return Ok(false)
					}
				}

				Ok(true)
			})
		};

		let result = if let Some(child_info) = child_info {
			let db = KeySpacedDB::new(self, child_info.keyspace());
			iter(&db)
		} else {
			iter(self)
		};
		match result {
			Ok(completed) => Ok(completed),
			Err(e) if matches!(*e, TrieError::IncompleteDatabase(_)) && allow_missing_nodes =>
				Ok(false),
			Err(e) => Err(format!("TrieDB iteration error: {}", e)),
		}
	}

	/// Execute given closure for all key and values starting with prefix.
	pub fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], mut f: F) {
		let _ = self.trie_iter_inner(
			&self.root,
			Some(prefix),
			|k, v| {
				f(&k, &v);
				true
			},
			None,
			None,
			false,
		);
	}

	/// Returns all `(key, value)` pairs in the trie.
	pub fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		let collect_all = || -> sp_std::result::Result<_, Box<TrieError<H::Out>>> {
			self.with_recorder_and_cache(None, |recorder, cache| {
				let trie = TrieDBBuilder::<H>::new(self, self.root())
					.with_optional_cache(cache)
					.with_optional_recorder(recorder)
					.build();

				let mut v = Vec::new();
				for x in trie.iter()? {
					let (key, value) = x?;
					v.push((key.to_vec(), value.to_vec()));
				}

				Ok(v)
			})
		};

		match collect_all() {
			Ok(v) => v,
			Err(e) => {
				debug!(target: "trie", "Error extracting trie values: {}", e);
				Vec::new()
			},
		}
	}

	/// Returns all keys that start with the given `prefix`.
	pub fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let mut keys = Vec::new();
		self.for_keys_with_prefix(prefix, |k| keys.push(k.to_vec()));
		keys
	}

	/// Return the storage root after applying the given `delta`.
	pub fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, S::Overlay) {
		let mut write_overlay = S::Overlay::default();

		let root = self.with_recorder_and_cache_for_storage_root(None, |recorder, cache| {
			let mut eph = Ephemeral::new(self.backend_storage(), &mut write_overlay);
			let res = match state_version {
				StateVersion::V0 => delta_trie_root::<sp_trie::LayoutV0<H>, _, _, _, _, _>(
					&mut eph, self.root, delta, recorder, cache,
				),
				StateVersion::V1 => delta_trie_root::<sp_trie::LayoutV1<H>, _, _, _, _, _>(
					&mut eph, self.root, delta, recorder, cache,
				),
			};

			match res {
				Ok(ret) => (Some(ret), ret),
				Err(e) => {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					(None, self.root)
				},
			}
		});

		(root, write_overlay)
	}

	/// Returns the child storage root for the child trie `child_info` after applying the given
	/// `delta`.
	pub fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, S::Overlay) {
		let default_root = match child_info.child_type() {
			ChildType::ParentKeyId => empty_child_trie_root::<sp_trie::LayoutV1<H>>(),
		};
		let mut write_overlay = S::Overlay::default();
		let child_root = match self.child_root(child_info) {
			Ok(Some(hash)) => hash,
			Ok(None) => default_root,
			Err(e) => {
				warn!(target: "trie", "Failed to read child storage root: {}", e);
				default_root
			},
		};

		let new_child_root =
			self.with_recorder_and_cache_for_storage_root(Some(child_root), |recorder, cache| {
				let mut eph = Ephemeral::new(self.backend_storage(), &mut write_overlay);
				match match state_version {
					StateVersion::V0 =>
						child_delta_trie_root::<sp_trie::LayoutV0<H>, _, _, _, _, _, _>(
							child_info.keyspace(),
							&mut eph,
							child_root,
							delta,
							recorder,
							cache,
						),
					StateVersion::V1 =>
						child_delta_trie_root::<sp_trie::LayoutV1<H>, _, _, _, _, _, _>(
							child_info.keyspace(),
							&mut eph,
							child_root,
							delta,
							recorder,
							cache,
						),
				} {
					Ok(ret) => (Some(ret), ret),
					Err(e) => {
						warn!(target: "trie", "Failed to write to trie: {}", e);
						(None, child_root)
					},
				}
			});

		let is_default = new_child_root == default_root;

		(new_child_root, is_default, write_overlay)
	}
}

pub(crate) struct Ephemeral<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	storage: &'a S,
	overlay: &'a mut S::Overlay,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> AsHashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn HashDB<H, DBValue> + 'b) {
		self
	}
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<H, DBValue> + 'b) {
		self
	}
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> Ephemeral<'a, S, H> {
	pub fn new(storage: &'a S, overlay: &'a mut S::Overlay) -> Self {
		Ephemeral { storage, overlay }
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> hash_db::HashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self.overlay, key, prefix).or_else(|| {
			self.storage.get(key, prefix).unwrap_or_else(|e| {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			})
		})
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		HashDB::insert(self.overlay, prefix, value)
	}

	fn emplace(&mut self, key: H::Out, prefix: Prefix, value: DBValue) {
		HashDB::emplace(self.overlay, key, prefix, value)
	}

	fn remove(&mut self, key: &H::Out, prefix: Prefix) {
		HashDB::remove(self.overlay, key, prefix)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> HashDBRef<H, DBValue> for Ephemeral<'a, S, H> {
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::contains(self, key, prefix)
	}
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: Send + Sync {
	/// Type of in-memory overlay.
	type Overlay: HashDB<H, DBValue> + Default + Consolidate;

	/// Get the value stored at key.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

impl<T: TrieBackendStorage<H>, H: Hasher> TrieBackendStorage<H> for &T {
	type Overlay = T::Overlay;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		(*self).get(key, prefix)
	}
}

// This implementation is used by normal storage trie clients.
#[cfg(feature = "std")]
impl<H: Hasher> TrieBackendStorage<H> for Arc<dyn Storage<H>> {
	type Overlay = sp_trie::PrefixedMemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Storage::<H>::get(std::ops::Deref::deref(self), key, prefix)
	}
}

impl<H, KF> TrieBackendStorage<H> for sp_trie::GenericMemoryDB<H, KF>
where
	H: Hasher,
	KF: sp_trie::KeyFunction<H> + Send + Sync,
{
	type Overlay = Self;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync> AsHashDB<H, DBValue>
	for TrieBackendEssence<S, H, C>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn HashDB<H, DBValue> + 'b) {
		self
	}
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<H, DBValue> + 'b) {
		self
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync> HashDB<H, DBValue>
	for TrieBackendEssence<S, H, C>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if *key == self.empty {
			return Some([0u8].to_vec())
		}
		match self.storage.get(key, prefix) {
			Ok(x) => x,
			Err(e) => {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			},
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, _prefix: Prefix, _value: &[u8]) -> H::Out {
		unimplemented!();
	}

	fn emplace(&mut self, _key: H::Out, _prefix: Prefix, _value: DBValue) {
		unimplemented!();
	}

	fn remove(&mut self, _key: &H::Out, _prefix: Prefix) {
		unimplemented!();
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync>
	HashDBRef<H, DBValue> for TrieBackendEssence<S, H, C>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::contains(self, key, prefix)
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::{Blake2Hasher, H256};
	use sp_trie::{
		cache::LocalTrieCache, trie_types::TrieDBMutBuilderV1 as TrieDBMutBuilder, KeySpacedDBMut,
		PrefixedMemoryDB, TrieMut,
	};

	#[test]
	fn next_storage_key_and_next_child_storage_key_work() {
		let child_info = ChildInfo::new_default(b"MyChild");
		let child_info = &child_info;
		// Contains values
		let mut root_1 = H256::default();
		// Contains child trie
		let mut root_2 = H256::default();

		let mut mdb = PrefixedMemoryDB::<Blake2Hasher>::default();
		{
			let mut trie = TrieDBMutBuilder::new(&mut mdb, &mut root_1).build();
			trie.insert(b"3", &[1]).expect("insert failed");
			trie.insert(b"4", &[1]).expect("insert failed");
			trie.insert(b"6", &[1]).expect("insert failed");
		}
		{
			let mut mdb = KeySpacedDBMut::new(&mut mdb, child_info.keyspace());
			// reuse of root_1 implicitly assert child trie root is same
			// as top trie (contents must remain the same).
			let mut trie = TrieDBMutBuilder::new(&mut mdb, &mut root_1).build();
			trie.insert(b"3", &[1]).expect("insert failed");
			trie.insert(b"4", &[1]).expect("insert failed");
			trie.insert(b"6", &[1]).expect("insert failed");
		}
		{
			let mut trie = TrieDBMutBuilder::new(&mut mdb, &mut root_2).build();
			trie.insert(child_info.prefixed_storage_key().as_slice(), root_1.as_ref())
				.expect("insert failed");
		};

		let essence_1 = TrieBackendEssence::<_, _, LocalTrieCache<_>>::new(mdb, root_1);

		assert_eq!(essence_1.next_storage_key(b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"6"), Ok(None));

		let mdb = essence_1.backend_storage().clone();
		let essence_2 = TrieBackendEssence::<_, _, LocalTrieCache<_>>::new(mdb, root_2);

		assert_eq!(essence_2.next_child_storage_key(child_info, b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"6"), Ok(None));
	}
}
