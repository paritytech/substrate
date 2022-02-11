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

use crate::{cache::TrieNodeCache, NodeCodec, StorageProof, TrieDBBuilder};
use hash_db::{HashDBRef, Hasher};
use parking_lot::{Mutex, MutexGuard};
use std::{
	collections::{HashMap, HashSet},
	hash::Hash,
	mem,
	sync::Arc,
};
use trie_db::{node::NodeOwned, CError, DBValue, TrieAccess, TrieLayout, TrieRecorder};

pub struct Recorder<H: Hasher> {
	inner: Arc<Mutex<RecorderInner<H::Out>>>,
}

impl<H: Hasher> Default for Recorder<H> {
	fn default() -> Self {
		Self { inner: Default::default() }
	}
}

impl<H: Hasher> Clone for Recorder<H> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone() }
	}
}

impl<H: Hasher> Recorder<H> {
	pub fn as_trie_recorder(&self) -> MutexGuard<impl TrieRecorder<H::Out>> {
		self.inner.lock()
	}

	pub fn into_storage_proof<L: TrieLayout<Hash = H, Codec = NodeCodec<H>>>(
		self,
		root: &H::Out,
		hash_db: &dyn HashDBRef<H, DBValue>,
		cache: Option<&mut TrieNodeCache<H>>,
	) -> trie_db::Result<StorageProof, H::Out, CError<L>> {
		let mut recorder = mem::take(&mut *self.inner.lock());
		let accessed_keys = mem::take(&mut recorder.accessed_keys);

		let trie = TrieDBBuilder::<L>::new(hash_db, root)?
			.with_recorder(&mut recorder)
			.with_optional_cache(cache.map(|c| c as _))
			.build();

		accessed_keys.iter().try_for_each(|k| trie.traverse_to(&k))?;

		Ok(StorageProof::new(
			recorder
				.accessed_encoded_nodes
				.drain()
				.map(|(_, v)| v)
				.chain(
					recorder
						.accessed_owned_nodes
						.drain()
						.map(|(_, v)| v.to_encoded::<NodeCodec<H>>()),
				)
				.collect(),
		))
	}
}

struct RecorderInner<H> {
	/// If we are recording while a cache is enabled, we may don't access all nodes because some
	/// data is already cached. Thus, we will only be informed about the key that was accessed. We
	/// will use these keys when building the [`StorageProof`] to traverse the trie again and
	/// collecting the required trie nodes for accessing the data.
	accessed_keys: HashSet<Vec<u8>>,
	/// The [`NodeOwned`] we accessed while recording. This should only be populated when a cache
	/// is used.
	accessed_owned_nodes: HashMap<H, NodeOwned<H>>,
	/// The encoded nodes we accessed while recording. This should only be populated when no cache
	/// is used.
	accessed_encoded_nodes: HashMap<H, Vec<u8>>,
}

impl<H> Default for RecorderInner<H> {
	fn default() -> Self {
		Self {
			accessed_keys: HashSet::new(),
			accessed_owned_nodes: HashMap::new(),
			accessed_encoded_nodes: HashMap::new(),
		}
	}
}

impl<H> trie_db::TrieRecorder<H> for RecorderInner<H>
where
	H: Eq + Hash + Clone,
{
	fn record<'a>(&mut self, access: TrieAccess<'a, H>) {
		match access {
			TrieAccess::Key(key) => {
				self.accessed_keys.insert(key.into());
			},
			TrieAccess::NodeOwned { hash, node_owned } => {
				self.accessed_owned_nodes.entry(hash).or_insert_with(|| (*node_owned).clone());
			},
			TrieAccess::EncodedNode { hash, encoded_node } => {
				self.accessed_encoded_nodes
					.entry(hash)
					.or_insert_with(|| encoded_node.into_owned());
			},
			TrieAccess::Value { hash, value } => {
				// We can just record this as encoded node, because we store just raw bytes anyway.
				self.accessed_encoded_nodes.entry(hash).or_insert_with(|| value.into_owned());
			},
		}
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
			let mut trie_recorder = recorder.as_trie_recorder();
			let trie = TrieDBBuilder::<Layout>::new_unchecked(&db, &root)
				.with_recorder(&mut *trie_recorder)
				.build();
			assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
		}

		let storage_proof = recorder.into_storage_proof::<Layout>(&root, &db, None).unwrap();
		let memory_db: MemoryDB = storage_proof.into_memory_db();

		// Check that we recorded the required data
		let trie = TrieDBBuilder::<Layout>::new_unchecked(&memory_db, &root).build();
		assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
	}
}
