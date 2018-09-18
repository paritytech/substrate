// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Conrete externalities implementation.

use std::{error, fmt, cmp::Ord};
use backend::Backend;
use changes_trie::{Storage as ChangesTrieStorage, compute_changes_trie_root};
use {Externalities, OverlayedChanges};
use hashdb::Hasher;
use memorydb::MemoryDB;
use rlp::Encodable;
use patricia_trie::{NodeCodec, TrieDBMut, TrieMut};
use heapsize::HeapSizeOf;

const EXT_NOT_ALLOWED_TO_FAIL: &'static str = "Externalities not allowed to fail within runtime";

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
{
	/// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	/// The storage backend to read from.
	backend: &'a B,
	/// The storage transaction necessary to commit to the backend. Is cached when
	/// `storage_root` is called and the cache is cleared on every subsequent change.
	storage_transaction: Option<(B::Transaction, H::Out)>,
	/// Changes trie storage to read from.
	changes_trie_storage: Option<&'a T>,
	/// The changes trie transaction necessary to commit to the changes trie backend.
	/// Set to Some when `storage_changes_root` is called. Could be replaced later
	/// by calling `storage_changes_root` again => never used as cache.
	/// This differs from `storage_transaction` behavior, because the moment when
	/// `storage_changes_root` is called matters + we need to remember additional
	/// data at this moment (block number).
	changes_trie_transaction: Option<(u64, MemoryDB<H>, H::Out)>,
}

impl<'a, H, C, B, T> Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
	H::Out: Ord + Encodable + HeapSizeOf,
{
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(overlay: &'a mut OverlayedChanges, backend: &'a B, changes_trie_storage: Option<&'a T>) -> Self {
		Ext {
			overlay,
			backend,
			storage_transaction: None,
			changes_trie_storage,
			changes_trie_transaction: None,
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> (B::Transaction, Option<MemoryDB<H>>) {
		let _ = self.storage_root();

		let (storage_transaction, changes_trie_transaction) = (
			self.storage_transaction
				.expect("storage_transaction always set after calling storage root; qed"),
			self.changes_trie_transaction
				.map(|(_, tx, _)| tx),
		);

		(
			storage_transaction.0,
			changes_trie_transaction,
		)
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.storage_transaction = None;
	}
}

#[cfg(test)]
impl<'a, H, C, B, T> Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H,C>,
	T: 'a + ChangesTrieStorage<H>,
{
	pub fn storage_pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		use std::collections::HashMap;

		self.backend.pairs().iter()
			.map(|&(ref k, ref v)| (k.to_vec(), Some(v.to_vec())))
			.chain(self.overlay.committed.clone().into_iter().map(|(k, v)| (k, v.value)))
			.chain(self.overlay.prospective.clone().into_iter().map(|(k, v)| (k, v.value)))
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
			.collect()
	}
}

impl<'a, B: 'a, T: 'a, H, C> Externalities<H> for Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
	H::Out: Ord + Encodable + HeapSizeOf,
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		}
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> H::Out {
		if let Some((_, ref root)) =  self.storage_transaction {
			return root.clone();
		}

		// compute and memoize
		let delta = self.overlay.committed.iter().map(|(k, v)| (k.clone(), v.value.clone()))
			.chain(self.overlay.prospective.iter().map(|(k, v)| (k.clone(), v.value.clone())));

		let (root, transaction) = self.backend.storage_root(delta);
		self.storage_transaction = Some((transaction, root));
		root
	}

	fn storage_changes_root(&mut self, block: u64) -> Option<H::Out> {
		let root_and_tx = compute_changes_trie_root::<_, T, H, C>(
			self.backend,
			self.changes_trie_storage.clone(),
			self.overlay,
			block,
		);
		let root_and_tx = root_and_tx.map(|(root, changes)| {
			let mut calculated_root = Default::default();
			let mut mdb = MemoryDB::new();
			{
				let mut trie = TrieDBMut::<H, C>::new(&mut mdb, &mut calculated_root);
				for (key, value) in changes {
					trie.insert(&key, &value).expect(EXT_NOT_ALLOWED_TO_FAIL);
				}
			}

			(block, mdb, root)
		});
		let root = root_and_tx.as_ref().map(|(_, _, root)| root.clone());
		self.changes_trie_transaction = root_and_tx;
		root
	}
}

#[cfg(test)]
mod tests {
	use codec::Encode;
	use primitives::{Blake2Hasher, RlpCodec};
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use backend::InMemory;
	use changes_trie::{Configuration as ChangesTrieConfiguration,
		InMemoryStorage as InMemoryChangesTrieStorage};
	use overlayed_changes::OverlayedValue;
	use super::*;

	type TestBackend = InMemory<Blake2Hasher, RlpCodec>;
	type TestChangesTrieStorage = InMemoryChangesTrieStorage<Blake2Hasher>;
	type TestExt<'a> = Ext<'a, Blake2Hasher, RlpCodec, TestBackend, TestChangesTrieStorage>;

	fn prepare_overlay_with_changes() -> OverlayedChanges {
		OverlayedChanges {
			prospective: vec![
				(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
					value: Some(3u32.encode()),
					extrinsics: Some(vec![1].into_iter().collect())
				}),
				(vec![1], OverlayedValue {
					value: Some(vec![100].into_iter().collect()),
					extrinsics: Some(vec![1].into_iter().collect())
				}),
			].into_iter().collect(),
			committed: Default::default(),
			changes_trie_config: Some(ChangesTrieConfiguration {
				digest_interval: 0,
				digest_levels: 0,
			}),
		}
	}

	#[test]
	fn storage_changes_root_is_none_when_storage_is_not_provided() {
		let mut overlay = prepare_overlay_with_changes();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, None);
		assert_eq!(ext.storage_changes_root(100), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_extrinsic_changes_are_none() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.changes_trie_config = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(100), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(100),
			Some(hex!("b2ecc5ca20de9f8a2d82482fcaa0fdfcca2fb76bf3d89860edf422bd15d075ec").into()));
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_empty() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.prospective.get_mut(&vec![1]).unwrap().value = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(100),
			Some(hex!("8c12eccf80c166aefc23af540649979581cb404d95af25b0ed38dc6949ba2453").into()));
	}
}
