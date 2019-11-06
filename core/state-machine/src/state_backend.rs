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

//! State machine backend build from a trie and an auxilliary
//! key value backend.


use log::{warn, debug};
use hash_db::Hasher;
use trie::{Trie, delta_trie_root, default_child_trie_root, child_delta_trie_root};
use trie::trie_types::{TrieDB, TrieError, Layout};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{TrieBackendStorage, Ephemeral};
use crate::Backend;
use crate::kv_backend::KvBackend;
use std::collections::HashMap;

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
/// A simple key value backend is also accessible for direct key value storage without
/// proof.
pub struct StateBackend<S: TrieBackendStorage<H>, H: Hasher, K: KvBackend> {
	trie: TrieBackend<S, H>,
	kv: K,
}

impl<S: TrieBackendStorage<H>, K: KvBackend, H: Hasher> StateBackend<S, H, K> {
	/// Create new state backend.
	pub fn new(storage: S, root: H::Out, kv: K) -> Self {
		StateBackend {
			trie: TrieBackend::new(storage, root),
			kv,
		}
	}

	/// Get backend essence reference.
	pub fn trie(&self) -> &TrieBackend<S, H> {
		&self.trie
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		self.trie.backend_storage()
	}

	/// Get key value storage backend reference.
	pub fn kv_backend(&self) -> &K {
		&self.kv
	}

	/// Get key value storage backend mutable reference.
	pub fn kv_backend_mut(&mut self) -> &mut K {
		&mut self.kv
	}

	/// Consumes self and returns underlying storage.
	pub fn into_storage(self) -> S {
		self.trie.into_storage()
	}

}

impl<
	S: TrieBackendStorage<H>,
	H: Hasher,
	K: KvBackend,
> std::fmt::Debug for StateBackend<S, H, K> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "StateBackend")
	}
}

impl<
	S: TrieBackendStorage<H>,
	H: Hasher,
	K: KvBackend,
> Backend<H> for StateBackend<S, H, K> where
	H::Out: Ord,
{
	type Error = String;
	type Transaction = (S::Overlay, HashMap<Vec<u8>, Option<Vec<u8>>>);
	type TrieBackendStorage = S;
	type KvBackend = K;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie.storage(key)
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie.child_storage(storage_key, key)
	}

	fn kv_storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.kv.get(key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.trie.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.trie.for_key_values_with_prefix(prefix, f)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		self.trie.for_keys_in_child_storage(storage_key, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(&self, storage_key: &[u8], prefix: &[u8], f: F) {
		self.trie.for_child_keys_with_prefix(storage_key, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.trie.pairs()
	}

	fn children_storage_keys(&self) -> Vec<Vec<u8>> {
		self.trie.children_storage_keys()
	}

	fn child_pairs(&self, storage_key: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.trie.child_pairs(storage_key)
	}

	fn kv_in_memory(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>> {
		self.kv.in_memory()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(self.trie.backend_storage(), &mut read_overlay);

		let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(&eph, self.trie.root())?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, _) = x?;
				if key.starts_with(prefix) {
					v.push(key.to_vec());
				}
			}

			Ok(v)
		};

		collect_all().map_err(|e| debug!(target: "trie", "Error extracting trie keys: {}", e)).unwrap_or_default()
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut write_overlay = S::Overlay::default();
		let mut root = *self.trie.root();

		{
			let mut eph = Ephemeral::new(
				self.trie.backend_storage(),
				&mut write_overlay,
			);

			match delta_trie_root::<Layout<H>, _, _, _, _>(&mut eph, root, delta) {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		(root, (write_overlay, Default::default()))
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
			H::Out: Ord
	{
		let default_root = default_child_trie_root::<Layout<H>>(storage_key);

		let mut write_overlay = S::Overlay::default();
		let mut root = match self.storage(storage_key) {
			Ok(value) => value.unwrap_or(default_root.clone()),
			Err(e) => {
				warn!(target: "trie", "Failed to read child storage root: {}", e);
				default_root.clone()
			},
		};

		{
			let mut eph = Ephemeral::new(
				self.trie.backend_storage(),
				&mut write_overlay,
			);

			match child_delta_trie_root::<Layout<H>, _, _, _, _>(
				storage_key,
				&mut eph,
				root.clone(),
				delta
			) {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		let is_default = root == default_root;

		(root, is_default, (write_overlay, Default::default()))
	}

	fn kv_transaction<I>(&self, delta: I) -> Self::Transaction
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut result = self.kv.in_memory();
		result.extend(delta.into_iter());
		(Default::default(), result)
	}

	fn as_state_backend(&mut self) -> Option<
		&StateBackend<Self::TrieBackendStorage, H, Self::KvBackend>
	> {
		Some(self)
	}
}

#[cfg(test)]
pub mod tests {
	use crate::trie_backend::tests::{test_db, KvBackend};
	use primitives::Blake2Hasher;
	use trie::PrefixedMemoryDB;
	use super::*;

	pub(crate) fn test_state(
	) -> StateBackend<PrefixedMemoryDB<Blake2Hasher>, Blake2Hasher, KvBackend> {
		let (mdb, root, kv) = test_db();
		StateBackend::new(mdb, root, kv)
	}
}
