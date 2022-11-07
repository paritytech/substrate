// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Trie recorder
//!
//! Provides an implementation of the [`TrieRecorder`](trie_db::TrieRecorder) trait. It can be used
//! to record storage accesses to the state to generate a [`StorageProof`].

use crate::{NodeCodec, StorageProof};
use codec::Encode;
use hash_db::Hasher;
use parking_lot::Mutex;
use std::{
	collections::HashMap,
	marker::PhantomData,
	mem,
	ops::DerefMut,
	sync::{
		atomic::{AtomicUsize, Ordering},
		Arc,
	},
};
use trie_db::{RecordedForKey, TrieAccess};

const LOG_TARGET: &str = "trie-recorder";

/// The internals of [`Recorder`].
struct RecorderInner<H> {
	/// The keys for that we have recorded the trie nodes and if we have recorded up to the value.
	recorded_keys: HashMap<H, HashMap<Vec<u8>, RecordedForKey>>,
	/// The encoded nodes we accessed while recording.
	accessed_nodes: HashMap<H, Vec<u8>>,
}

impl<H> Default for RecorderInner<H> {
	fn default() -> Self {
		Self { recorded_keys: Default::default(), accessed_nodes: Default::default() }
	}
}

/// The trie recorder.
///
/// It can be used to record accesses to the trie and then to convert them into a [`StorageProof`].
pub struct Recorder<H: Hasher> {
	inner: Arc<Mutex<RecorderInner<H::Out>>>,
	/// The estimated encoded size of the storage proof this recorder will produce.
	///
	/// We store this in an atomic to be able to fetch the value while the `inner` is may locked.
	encoded_size_estimation: Arc<AtomicUsize>,
}

impl<H: Hasher> Default for Recorder<H> {
	fn default() -> Self {
		Self { inner: Default::default(), encoded_size_estimation: Arc::new(0.into()) }
	}
}

impl<H: Hasher> Clone for Recorder<H> {
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.clone(),
			encoded_size_estimation: self.encoded_size_estimation.clone(),
		}
	}
}

impl<H: Hasher> Recorder<H> {
	/// Returns the recorder as [`TrieRecorder`](trie_db::TrieRecorder) compatible type.
	///
	/// - `storage_root`: The storage root of the trie for which accesses are recorded. This is
	///   important when recording access to different tries at once (like top and child tries).
	pub fn as_trie_recorder(
		&self,
		storage_root: H::Out,
	) -> impl trie_db::TrieRecorder<H::Out> + '_ {
		TrieRecorder::<H, _> {
			inner: self.inner.lock(),
			storage_root,
			encoded_size_estimation: self.encoded_size_estimation.clone(),
			_phantom: PhantomData,
		}
	}

	/// Drain the recording into a [`StorageProof`].
	///
	/// While a recorder can be cloned, all share the same internal state. After calling this
	/// function, all other instances will have their internal state reset as well.
	///
	/// If you don't want to drain the recorded state, use [`Self::to_storage_proof`].
	///
	/// Returns the [`StorageProof`].
	pub fn drain_storage_proof(self) -> StorageProof {
		let mut recorder = mem::take(&mut *self.inner.lock());
		StorageProof::new(recorder.accessed_nodes.drain().map(|(_, v)| v))
	}

	/// Convert the recording to a [`StorageProof`].
	///
	/// In contrast to [`Self::drain_storage_proof`] this doesn't consumes and doesn't clears the
	/// recordings.
	///
	/// Returns the [`StorageProof`].
	pub fn to_storage_proof(&self) -> StorageProof {
		let recorder = self.inner.lock();
		StorageProof::new(recorder.accessed_nodes.values().cloned())
	}

	/// Returns the estimated encoded size of the proof.
	///
	/// The estimation is based on all the nodes that were accessed until now while
	/// accessing the trie.
	pub fn estimate_encoded_size(&self) -> usize {
		self.encoded_size_estimation.load(Ordering::Relaxed)
	}

	/// Reset the state.
	///
	/// This discards all recorded data.
	pub fn reset(&self) {
		mem::take(&mut *self.inner.lock());
		self.encoded_size_estimation.store(0, Ordering::Relaxed);
	}
}

/// The [`TrieRecorder`](trie_db::TrieRecorder) implementation.
struct TrieRecorder<H: Hasher, I> {
	inner: I,
	storage_root: H::Out,
	encoded_size_estimation: Arc<AtomicUsize>,
	_phantom: PhantomData<H>,
}

impl<H: Hasher, I: DerefMut<Target = RecorderInner<H::Out>>> trie_db::TrieRecorder<H::Out>
	for TrieRecorder<H, I>
{
	fn record<'b>(&mut self, access: TrieAccess<'b, H::Out>) {
		let mut encoded_size_update = 0;

		match access {
			TrieAccess::NodeOwned { hash, node_owned } => {
				tracing::trace!(
					target: LOG_TARGET,
					hash = ?hash,
					"Recording node",
				);

				self.inner.accessed_nodes.entry(hash).or_insert_with(|| {
					let node = node_owned.to_encoded::<NodeCodec<H>>();

					encoded_size_update += node.encoded_size();

					node
				});
			},
			TrieAccess::EncodedNode { hash, encoded_node } => {
				tracing::trace!(
					target: LOG_TARGET,
					hash = ?hash,
					"Recording node",
				);

				self.inner.accessed_nodes.entry(hash).or_insert_with(|| {
					let node = encoded_node.into_owned();

					encoded_size_update += node.encoded_size();

					node
				});
			},
			TrieAccess::Value { hash, value, full_key } => {
				tracing::trace!(
					target: LOG_TARGET,
					hash = ?hash,
					key = ?sp_core::hexdisplay::HexDisplay::from(&full_key),
					"Recording value",
				);

				self.inner.accessed_nodes.entry(hash).or_insert_with(|| {
					let value = value.into_owned();

					encoded_size_update += value.encoded_size();

					value
				});

				self.inner
					.recorded_keys
					.entry(self.storage_root)
					.or_default()
					.entry(full_key.to_vec())
					.and_modify(|e| *e = RecordedForKey::Value)
					.or_insert(RecordedForKey::Value);
			},
			TrieAccess::Hash { full_key } => {
				tracing::trace!(
					target: LOG_TARGET,
					key = ?sp_core::hexdisplay::HexDisplay::from(&full_key),
					"Recorded hash access for key",
				);

				// We don't need to update the `encoded_size_update` as the hash was already
				// accounted for by the recorded node that holds the hash.
				self.inner
					.recorded_keys
					.entry(self.storage_root)
					.or_default()
					.entry(full_key.to_vec())
					.or_insert(RecordedForKey::Hash);
			},
			TrieAccess::NonExisting { full_key } => {
				tracing::trace!(
					target: LOG_TARGET,
					key = ?sp_core::hexdisplay::HexDisplay::from(&full_key),
					"Recorded non-existing value access for key",
				);

				// Non-existing access means we recorded all trie nodes up to the value.
				// Not the actual value, as it doesn't exist, but all trie nodes to know
				// that the value doesn't exist in the trie.
				self.inner
					.recorded_keys
					.entry(self.storage_root)
					.or_default()
					.entry(full_key.to_vec())
					.and_modify(|e| *e = RecordedForKey::Value)
					.or_insert(RecordedForKey::Value);
			},
		};

		self.encoded_size_estimation.fetch_add(encoded_size_update, Ordering::Relaxed);
	}

	fn trie_nodes_recorded_for_key(&self, key: &[u8]) -> RecordedForKey {
		self.inner
			.recorded_keys
			.get(&self.storage_root)
			.and_then(|k| k.get(key).copied())
			.unwrap_or(RecordedForKey::None)
	}
}

#[cfg(test)]
mod tests {
	use trie_db::{Trie, TrieDBBuilder, TrieDBMutBuilder, TrieHash, TrieMut};

	type MemoryDB = crate::MemoryDB<sp_core::Blake2Hasher>;
	type Layout = crate::LayoutV1<sp_core::Blake2Hasher>;
	type Recorder = super::Recorder<sp_core::Blake2Hasher>;

	const TEST_DATA: &[(&[u8], &[u8])] =
		&[(b"key1", b"val1"), (b"key2", b"val2"), (b"key3", b"val3"), (b"key4", b"val4")];

	fn create_trie() -> (MemoryDB, TrieHash<Layout>) {
		let mut db = MemoryDB::default();
		let mut root = Default::default();

		{
			let mut trie = TrieDBMutBuilder::<Layout>::new(&mut db, &mut root).build();
			for (k, v) in TEST_DATA {
				trie.insert(k, v).expect("Inserts data");
			}
		}

		(db, root)
	}

	#[test]
	fn recorder_works() {
		let (db, root) = create_trie();

		let recorder = Recorder::default();

		{
			let mut trie_recorder = recorder.as_trie_recorder(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root)
				.with_recorder(&mut trie_recorder)
				.build();
			assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
		}

		let storage_proof = recorder.drain_storage_proof();
		let memory_db: MemoryDB = storage_proof.into_memory_db();

		// Check that we recorded the required data
		let trie = TrieDBBuilder::<Layout>::new(&memory_db, &root).build();
		assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
	}
}
