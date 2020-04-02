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

//! The overlayed changes to state.

use crate::{
	backend::Backend, ChangesTrieTransaction,
	changes_trie::{
		NO_EXTRINSIC_INDEX, BlockNumber, build_changes_trie,
		State as ChangesTrieState,
	},
	stats::StateMachineStats,
};

#[cfg(test)]
use std::iter::FromIterator;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use codec::{Decode, Encode};
use sp_core::storage::{well_known_keys::EXTRINSIC_INDEX, ChildInfo,
	PrefixedStorageKey, ChildChange, ChildUpdate};
use std::{mem, ops};

use sp_core::Hasher;

/// Storage key.
pub type StorageKey = Vec<u8>;

/// Storage value.
pub type StorageValue = Vec<u8>;

/// In memory array of storage values.
pub type StorageCollection = Vec<(StorageKey, Option<StorageValue>)>;

/// In memory arrays of storage values for multiple child tries.
pub type ChildStorageCollection = Vec<(ChildInfo, ChildChange, StorageCollection)>;

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Changes that are not yet committed.
	pub(crate) prospective: OverlayedChangeSet,
	/// Committed changes.
	pub(crate) committed: OverlayedChangeSet,
	/// True if extrinsics stats must be collected.
	pub(crate) collect_extrinsics: bool,
	/// Collect statistic on this execution.
	pub(crate) stats: StateMachineStats,
}

/// The storage value, used inside OverlayedChanges.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedValue {
	/// Current value. None if value has been deleted.
	pub value: Option<StorageValue>,
	/// The set of extrinsic indices where the values has been changed.
	/// Is filled only if runtime has announced changes trie support.
	pub extrinsics: Option<BTreeSet<u32>>,
}

/// Overlay change set of a given child state.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ChildChangeSet {
	/// Child definition.
	pub info: ChildInfo,
	/// Kind of modification for this change, and
	/// possibly extrinsic index of the change.
	/// Currently it can only be a single extrinsic
	/// for first bulk deletion.
	pub change: (ChildChange, Option<u32>),
	/// Deltas of modified values for this change.
	/// The map key is the child storage key without the common prefix.
	pub values: BTreeMap<StorageKey, OverlayedValue>,
}

/// Prospective or committed overlayed change set.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Top level storage changes.
	pub top: BTreeMap<StorageKey, OverlayedValue>,
	/// Child storage changes.
	pub children_default: HashMap<StorageKey, ChildChangeSet>,
}

/// A storage changes structure that can be generated by the data collected in [`OverlayedChanges`].
///
/// This contains all the changes to the storage and transactions to apply theses changes to the
/// backend.
pub struct StorageChanges<Transaction, H: Hasher, N: BlockNumber> {
	/// All changes to the main storage.
	///
	/// A value of `None` means that it was deleted.
	pub main_storage_changes: StorageCollection,
	/// All changes to the child storages.
	pub child_storage_changes: ChildStorageCollection,
	/// A transaction for the backend that contains all changes from
	/// [`main_storage_changes`](Self::main_storage_changes) and from
	/// [`child_storage_changes`](Self::child_storage_changes).
	pub transaction: Transaction,
	/// The storage root after applying the transaction.
	pub transaction_storage_root: H::Out,
	/// Contains the transaction for the backend for the changes trie.
	///
	/// If changes trie is disabled the value is set to `None`.
	pub changes_trie_transaction: Option<ChangesTrieTransaction<H, N>>,
}

impl<Transaction, H: Hasher, N: BlockNumber> StorageChanges<Transaction, H, N> {
	/// Deconstruct into the inner values
	pub fn into_inner(self) -> (
		StorageCollection,
		ChildStorageCollection,
		Transaction,
		H::Out,
		Option<ChangesTrieTransaction<H, N>>,
	) {
		(
			self.main_storage_changes,
			self.child_storage_changes,
			self.transaction,
			self.transaction_storage_root,
			self.changes_trie_transaction,
		)
	}
}

/// The storage transaction are calculated as part of the `storage_root` and
/// `changes_trie_storage_root`. These transactions can be reused for importing the block into the
/// storage. So, we cache them to not require a recomputation of those transactions.
pub struct StorageTransactionCache<Transaction, H: Hasher, N: BlockNumber> {
	/// Contains the changes for the main and the child storages as one transaction.
	pub(crate) transaction: Option<Transaction>,
	/// The storage root after applying the transaction.
	pub(crate) transaction_storage_root: Option<H::Out>,
	/// The storage child roots after applying the transaction.
	pub(crate) transaction_child_storage_root: BTreeMap<PrefixedStorageKey, Option<H::Out>>,
	/// Contains the changes trie transaction.
	pub(crate) changes_trie_transaction: Option<Option<ChangesTrieTransaction<H, N>>>,
	/// The storage root after applying the changes trie transaction.
	pub(crate) changes_trie_transaction_storage_root: Option<Option<H::Out>>,
}

impl<Transaction, H: Hasher, N: BlockNumber> StorageTransactionCache<Transaction, H, N> {
	/// Reset the cached transactions.
	pub fn reset(&mut self) {
		*self = Self::default();
	}
}

impl<Transaction, H: Hasher, N: BlockNumber> Default for StorageTransactionCache<Transaction, H, N> {
	fn default() -> Self {
		Self {
			transaction: None,
			transaction_storage_root: None,
			transaction_child_storage_root: Default::default(),
			changes_trie_transaction: None,
			changes_trie_transaction_storage_root: None,
		}
	}
}

impl<Transaction: Default, H: Hasher, N: BlockNumber> Default for StorageChanges<Transaction, H, N> {
	fn default() -> Self {
		Self {
			main_storage_changes: Default::default(),
			child_storage_changes: Default::default(),
			transaction: Default::default(),
			transaction_storage_root: Default::default(),
			changes_trie_transaction: None,
		}
	}
}

#[cfg(test)]
impl FromIterator<(StorageKey, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (StorageKey, OverlayedValue)>>(iter: T) -> Self {
		Self {
			top: iter.into_iter().collect(),
			children_default: Default::default(),
		}
	}
}

impl OverlayedChangeSet {
	/// Whether the change set is empty.
	pub fn is_empty(&self) -> bool {
		self.top.is_empty() && self.children_default.is_empty()
	}

	/// Clear the change set.
	pub fn clear(&mut self) {
		self.top.clear();
		self.children_default.clear();
	}
}

impl OverlayedChanges {
	/// Whether the overlayed changes are empty.
	pub fn is_empty(&self) -> bool {
		self.prospective.is_empty() && self.committed.is_empty()
	}

	/// Ask to collect/not to collect extrinsics indices where key(s) has been changed.
	pub fn set_collect_extrinsics(&mut self, collect_extrinsics: bool) {
		self.collect_extrinsics = collect_extrinsics;
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.prospective.top.get(key)
			.or_else(|| self.committed.top.get(key))
			.map(|x| {
				let size_read = x.value.as_ref().map(|x| x.len() as u64).unwrap_or(0);
				self.stats.tally_read_modified(size_read);
				x.value.as_ref().map(AsRef::as_ref)
			})
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&self, child_info: &ChildInfo, key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(child) = self.prospective.children_default.get(child_info.storage_key()) {
			if child.change.0 == ChildChange::BulkDeleteByKeyspace {
				return Some(None);
			}
			if let Some(val) = child.values.get(key) {
				let size_read = val.value.as_ref().map(|x| x.len() as u64).unwrap_or(0);
				self.stats.tally_read_modified(size_read);
				return Some(val.value.as_ref().map(AsRef::as_ref));
			}
		}

		if let Some(child) = self.committed.children_default.get(child_info.storage_key()) {
			if child.change.0 == ChildChange::BulkDeleteByKeyspace {
				return Some(None);
			}
			if let Some(val) = child.values.get(key) {
				let size_read = val.value.as_ref().map(|x| x.len() as u64).unwrap_or(0);
				self.stats.tally_read_modified(size_read);
				return Some(val.value.as_ref().map(AsRef::as_ref));
			}
		}

		None
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_storage(&mut self, key: StorageKey, val: Option<StorageValue>) {
		let size_write = val.as_ref().map(|x| x.len() as u64).unwrap_or(0);
		self.stats.tally_write_overlay(size_write);
		let extrinsic_index = self.extrinsic_index();
		let entry = self.prospective.top.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Inserts the given key-value pair into the prospective child change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		val: Option<StorageValue>,
	) {
		let size_write = val.as_ref().map(|x| x.len() as u64).unwrap_or(0);
		self.stats.tally_write_overlay(size_write);
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.get_or_init_prospective(child_info);
		let updatable = map_entry.info.try_update(&map_entry.change.0, child_info);
		debug_assert!(updatable != ChildUpdate::Incompatible);
		if updatable == ChildUpdate::Ignore {
			return;
		}

		let entry = map_entry.values.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Clear child storage of given storage key.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		let extrinsic_index = self.extrinsic_index();

		let map_entry = self.get_or_init_prospective(child_info);
		let updatable = map_entry.info.try_update(&map_entry.change.0, child_info);
		debug_assert!(updatable != ChildUpdate::Incompatible);
		if updatable == ChildUpdate::Ignore {
			return;
		}

		map_entry.change = (ChildChange::BulkDeleteByKeyspace, extrinsic_index);
		// drop value to reclaim some memory, keep change trie if there is some.
		if !extrinsic_index.is_some() {
			map_entry.values.clear();
		}
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		// Iterate over all prospective and mark all keys that share
		// the given prefix as removed (None).
		for (key, entry) in self.prospective.top.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		// Then do the same with keys from committed changes.
		// NOTE that we are making changes in the prospective change set.
		for key in self.committed.top.keys() {
			if key.starts_with(prefix) {
				let entry = self.prospective.top.entry(key.clone()).or_default();
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}
	}

	pub(crate) fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry =	Self::get_or_init_prospective_inner(
			&mut self.prospective,
			&self.committed,
			child_info,
		);
		let updatable = map_entry.info.try_update(&map_entry.change.0, child_info);
		debug_assert!(updatable != ChildUpdate::Incompatible);
		if updatable == ChildUpdate::Ignore {
			return;
		}

		for (key, entry) in map_entry.values.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		if let Some(child_committed) = self.committed.children_default.get(child_info.storage_key()) {
			// Then do the same with keys from committed changes.
			// NOTE that we are making changes in the prospective change set.
			for key in child_committed.values.keys() {
				if key.starts_with(prefix) {
					let entry = map_entry.values.entry(key.clone()).or_default();
					entry.value = None;

					if let Some(extrinsic) = extrinsic_index {
						entry.extrinsics.get_or_insert_with(Default::default)
							.insert(extrinsic);
					}
				}
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			let top_to_commit = mem::replace(&mut self.prospective.top, BTreeMap::new());
			for (key, val) in top_to_commit.into_iter() {
				let entry = self.committed.top.entry(key).or_default();
				entry.value = val.value;

				if let Some(prospective_extrinsics) = val.extrinsics {
					entry.extrinsics.get_or_insert_with(Default::default)
						.extend(prospective_extrinsics);
				}
			}
			for (storage_key, child) in self.prospective.children_default.drain() {
				let child_committed = self.committed.children_default.entry(storage_key)
					.or_insert_with(|| ChildChangeSet {
						info: child.info.clone(), 
						change: child.change,
						values: Default::default()
					});
				child_committed.change = child.change;
				// No update to child info at this point (will be needed for deletion).
				for (key, val) in child.values.into_iter() {
					let entry = child_committed.values.entry(key).or_default();
					entry.value = val.value;

					if let Some(prospective_extrinsics) = val.extrinsics {
						entry.extrinsics.get_or_insert_with(Default::default)
							.extend(prospective_extrinsics);
					}
				}
			}
		}
	}

	/// Consume `OverlayedChanges` and take committed set.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	fn drain_committed(&mut self) -> (
		impl Iterator<Item=(StorageKey, Option<StorageValue>)>,
		impl Iterator<Item=(ChildInfo, ChildChange, impl Iterator<Item=(StorageKey, Option<StorageValue>)>)>,
	) {
		assert!(self.prospective.is_empty());
		(
			std::mem::replace(&mut self.committed.top, Default::default())
				.into_iter()
				.map(|(k, v)| (k, v.value)),
			std::mem::replace(&mut self.committed.children_default, Default::default())
				.into_iter()
				.map(|(_sk, child)| (child.info, child.change.0, child.values.into_iter().map(|(k, v)| (k, v.value)))),
		)
	}

	/// Convert this instance with all changes into a [`StorageChanges`] instance.
	pub fn into_storage_changes<
		B: Backend<H>, H: Hasher, N: BlockNumber
	>(
		mut self,
		backend: &B,
		changes_trie_state: Option<&ChangesTrieState<H, N>>,
		parent_hash: H::Out,
		mut cache: StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<StorageChanges<B::Transaction, H, N>, String> where H::Out: Ord + Encode + 'static {
		self.drain_storage_changes(backend, changes_trie_state, parent_hash, &mut cache)
	}

	/// Drain all changes into a [`StorageChanges`] instance. Leave empty overlay in place.
	pub fn drain_storage_changes<B: Backend<H>, H: Hasher, N: BlockNumber>(
		&mut self,
		backend: &B,
		changes_trie_state: Option<&ChangesTrieState<H, N>>,
		parent_hash: H::Out,
		mut cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<StorageChanges<B::Transaction, H, N>, String> where H::Out: Ord + Encode + 'static {
		// If the transaction does not exist, we generate it.
		if cache.transaction.is_none() {
			self.storage_root(backend, &mut cache);
		}

		let (transaction, transaction_storage_root) = cache.transaction.take()
			.and_then(|t| cache.transaction_storage_root.take().map(|tr| (t, tr)))
			.expect("Transaction was be generated as part of `storage_root`; qed");

		// If the transaction does not exist, we generate it.
		if cache.changes_trie_transaction.is_none() {
			self.changes_trie_root(
				backend,
				changes_trie_state,
				parent_hash,
				false,
				&mut cache,
			).map_err(|_| "Failed to generate changes trie transaction")?;
		}

		let changes_trie_transaction = cache.changes_trie_transaction
			.take()
			.expect("Changes trie transaction was generated by `changes_trie_root`; qed");

		let (main_storage_changes, child_storage_changes) = self.drain_committed();

		Ok(StorageChanges {
			main_storage_changes: main_storage_changes.collect(),
			child_storage_changes: child_storage_changes
				.map(|(ci, cc, it)| (ci, cc, it.collect())).collect(),
			transaction,
			transaction_storage_root,
			changes_trie_transaction,
		})
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		self.prospective.top.insert(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
			value: Some(extrinsic_index.encode()),
			extrinsics: None,
		});
	}

	/// Returns current extrinsic index to use in changes trie construction.
	/// None is returned if it is not set or changes trie config is not set.
	/// Persistent value (from the backend) can be ignored because runtime must
	/// set this index before first and unset after last extrinsic is executed.
	/// Changes that are made outside of extrinsics, are marked with
	/// `NO_EXTRINSIC_INDEX` index.
	fn extrinsic_index(&self) -> Option<u32> {
		match self.collect_extrinsics {
			true => Some(
				self.storage(EXTRINSIC_INDEX)
					.and_then(|idx| idx.and_then(|idx| Decode::decode(&mut &*idx).ok()))
					.unwrap_or(NO_EXTRINSIC_INDEX)),
			false => None,
		}
	}

	/// Generate the storage root using `backend` and all changes from `prospective` and `committed`.
	///
	/// Returns the storage root and caches storage transaction in the given `cache`.
	pub fn storage_root<H: Hasher, N: BlockNumber, B: Backend<H>>(
		&self,
		backend: &B,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> H::Out
		where H::Out: Ord + Encode,
	{
		let child_storage_keys = self.prospective.children_default.keys()
				.chain(self.committed.children_default.keys());
		let child_delta_iter = child_storage_keys.map(|storage_key| {
			let (child_info, child_change) = self.default_child_info(storage_key)
					.expect("child info initialized in either committed or prospective");
			(
				child_info.clone(),
				child_change,
				self.committed.children_default.get(storage_key)
					.into_iter()
					.flat_map(|child| child.values.iter().map(|(k, v)| (k.clone(), v.value.clone())))
					.chain(
						self.prospective.children_default.get(storage_key)
							.into_iter()
							.flat_map(|child| child.values.iter().map(|(k, v)| (k.clone(), v.value.clone())))
					),
			)
		});

		// compute and memoize
		let delta = self.committed.top.iter().map(|(k, v)| (k.clone(), v.value.clone()))
			.chain(self.prospective.top.iter().map(|(k, v)| (k.clone(), v.value.clone())));

		let (root, transaction, child_roots) = backend.full_storage_root(delta, child_delta_iter, true);

		cache.transaction = Some(transaction);
		cache.transaction_storage_root = Some(root);
		cache.transaction_child_storage_root = child_roots.into_iter().collect();

		root
	}

	/// Generate the changes trie root.
	///
	/// Returns the changes trie root and caches the storage transaction into the given `cache`.
	///
	/// # Panics
	///
	/// Panics on storage error, when `panic_on_storage_error` is set.
	pub fn changes_trie_root<'a, H: Hasher, N: BlockNumber, B: Backend<H>>(
		&self,
		backend: &B,
		changes_trie_state: Option<&'a ChangesTrieState<'a, H, N>>,
		parent_hash: H::Out,
		panic_on_storage_error: bool,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<Option<H::Out>, ()> where H::Out: Ord + Encode + 'static {
		build_changes_trie::<_, H, N>(
			backend,
			changes_trie_state,
			self,
			parent_hash,
			panic_on_storage_error,
		).map(|r| {
			let root = r.as_ref().map(|r| r.1).clone();
			cache.changes_trie_transaction = Some(r.map(|(db, _, cache)| (db, cache)));
			cache.changes_trie_transaction_storage_root = Some(root);
			root
		})
	}

	/// Get child info for a storage key.
	/// Take the latest value so prospective first.
	pub fn default_child_info(&self, storage_key: &[u8]) -> Option<(&ChildInfo, ChildChange)> {
		if let Some(child) = self.prospective.children_default.get(storage_key) {
			return Some((&child.info, child.change.0));
		}
		if let Some(child) = self.committed.children_default.get(storage_key) {
			return Some((&child.info, child.change.0));
		}
		None
	}

	/// Returns the next (in lexicographic order) storage key in the overlayed alongside its value.
	/// If no value is next then `None` is returned.
	pub fn next_storage_key_change(&self, key: &[u8]) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		let next_prospective_key = self.prospective.top
			.range::<[u8], _>(range)
			.next()
			.map(|(k, v)| (&k[..], v));

		let next_committed_key = self.committed.top
			.range::<[u8], _>(range)
			.next()
			.map(|(k, v)| (&k[..], v));

		match (next_committed_key, next_prospective_key) {
			// Committed is strictly less than prospective
			(Some(committed_key), Some(prospective_key)) if committed_key.0 < prospective_key.0 =>
				Some(committed_key),
			(committed_key, None) => committed_key,
			// Prospective key is less or equal to committed or committed doesn't exist
			(_, prospective_key) => prospective_key,
		}
	}

	/// Returns the next (in lexicographic order) child storage key in the overlayed alongside its
	/// value.  If no value is next then `None` is returned.
	pub fn next_child_storage_key_change(
		&self,
		storage_key: &[u8],
		key: &[u8]
	) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		let prospective = self.prospective.children_default.get(storage_key);
		if prospective.map(|child| child.change.0) == Some(ChildChange::BulkDeleteByKeyspace) {
			return None;
		}

		let next_prospective_key = prospective
			.and_then(|child| child.values.range::<[u8], _>(range).next().map(|(k, v)| (&k[..], v)));

		let committed = self.committed.children_default.get(storage_key);
		if committed.map(|child| child.change.0) == Some(ChildChange::BulkDeleteByKeyspace) {
			return None;
		}

		let next_committed_key = committed
			.and_then(|child| child.values.range::<[u8], _>(range).next().map(|(k, v)| (&k[..], v)));

		match (next_committed_key, next_prospective_key) {
			// Committed is strictly less than prospective
			(Some(committed_key), Some(prospective_key)) if committed_key.0 < prospective_key.0 =>
				Some(committed_key),
			(committed_key, None) => committed_key,
			// Prospective key is less or equal to committed or committed doesn't exist
			(_, prospective_key) => prospective_key,
		}
	}

	fn get_or_init_prospective_inner<'a>(
		prospective: &'a mut OverlayedChangeSet,
		committed: &OverlayedChangeSet,
		child_info: &ChildInfo,
	) -> &'a mut ChildChangeSet {
		prospective.children_default.entry(child_info.storage_key().to_vec())
			.or_insert(ChildChangeSet {
				info: child_info.to_owned(),
				change: committed.children_default.get(child_info.storage_key())
					.map(|child| (child.change.0, None))
					.unwrap_or(Default::default()),
				values: Default::default(),
			})
	}

	fn get_or_init_prospective(&mut self, child_info: &ChildInfo) -> &mut ChildChangeSet {
		Self::get_or_init_prospective_inner(&mut self.prospective, &self.committed, child_info)
	}
}

#[cfg(test)]
impl From<Option<StorageValue>> for OverlayedValue {
	fn from(value: Option<StorageValue>) -> OverlayedValue {
		OverlayedValue { value, ..Default::default() }
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use sp_core::{
		Blake2Hasher, traits::Externalities, storage::well_known_keys::EXTRINSIC_INDEX,
	};
	use crate::InMemoryBackend;
	use crate::ext::Ext;
	use super::*;

	fn strip_extrinsic_index(map: &BTreeMap<StorageKey, OverlayedValue>)
		-> BTreeMap<StorageKey, OverlayedValue>
	{
		let mut clone = map.clone();
		clone.remove(&EXTRINSIC_INDEX.to_vec());
		clone
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: BTreeMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemoryBackend::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges {
			committed: vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			prospective: vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect(),
			..Default::default()
		};

		let mut cache = StorageTransactionCache::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut cache,
			&backend,
			crate::changes_trie::disabled_state::<_, u64>(),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn extrinsic_changes_are_collected() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_collect_extrinsics(true);

		overlay.set_storage(vec![100], Some(vec![101]));

		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));

		overlay.set_extrinsic_index(1);
		overlay.set_storage(vec![3], Some(vec![4]));

		overlay.set_extrinsic_index(2);
		overlay.set_storage(vec![1], Some(vec![6]));

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
				 extrinsics: Some(vec![4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
				 extrinsics: Some(vec![3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
				 extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
				 extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.prospective,
			Default::default());
	}

	#[test]
	fn next_storage_key_change_works() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_storage(vec![20], Some(vec![20]));
		overlay.set_storage(vec![30], Some(vec![30]));
		overlay.set_storage(vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_storage(vec![10], Some(vec![10]));
		overlay.set_storage(vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_storage_key_change(&[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_storage_key_change(&[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_storage_key_change(&[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_storage_key_change(&[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_storage(vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_storage_key_change(&[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}

	#[test]
	fn next_child_storage_key_change_works() {
		let child_info = ChildInfo::new_default(b"Child1");
		let child_info = &child_info;
		let child = child_info.storage_key();
		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(child_info, vec![20], Some(vec![20]));
		overlay.set_child_storage(child_info, vec![30], Some(vec![30]));
		overlay.set_child_storage(child_info, vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_child_storage(child_info, vec![10], Some(vec![10]));
		overlay.set_child_storage(child_info, vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_child_storage_key_change(child, &[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_child_storage_key_change(child, &[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_child_storage_key_change(child, &[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_child_storage_key_change(child, &[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_child_storage(child_info, vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_child_storage_key_change(child, &[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}
}
