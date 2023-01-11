// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
// limitations under the License

//! Houses the code that implements the transactional overlay storage.

use super::{StorageKey, StorageValue, Transactional};

use crate::stats::StateMachineStats;
use smallvec::SmallVec;
use sp_externalities::range_slice;
#[cfg(not(feature = "std"))]
use sp_std::collections::btree_set::BTreeSet as Set;
use sp_std::{collections::btree_map::BTreeMap, hash::Hash};
#[cfg(feature = "std")]
use std::collections::HashSet as Set;

const PROOF_OVERLAY_NON_EMPTY: &str = "\
	An OverlayValue is always created with at least one transaction and dropped as soon
	as the last transaction is removed; qed";

type Dirty<I> = SmallVec<[I; 5]>;
type DirtyKeysSets<K> = Dirty<Set<K>>;
type Transactions<V> = SmallVec<[V; 5]>;

/// Error returned when trying to commit or rollback while no transaction is open or
/// when the runtime is trying to close a transaction started by the client.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct NoOpenTransaction;

/// Error when calling `enter_runtime` when already being in runtime execution mode.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct AlreadyInRuntime;

/// Error when calling `exit_runtime` when not being in runtime exection mdde.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct NotInRuntime;

/// Describes in which mode the node is currently executing.
#[derive(Debug, Clone, Copy)]
pub enum ExecutionMode {
	/// Executing in client mode: Removal of all transactions possible.
	Client,
	/// Executing in runtime mode: Transactions started by the client are protected.
	Runtime,
}

/// An overlay that contains all versions of a value for a specific key.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedEntry<V> {
	/// The individual versions of that value.
	/// One entry per transactions during that the value was actually written.
	transactions: Transactions<V>,
}

impl<V> Default for OverlayedEntry<V> {
	fn default() -> Self {
		Self { transactions: SmallVec::new() }
	}
}

/// History of value, with removal support.
pub type OverlayedValue = OverlayedEntry<Option<StorageValue>>;

/// Change set for basic key value with extrinsics index recording and removal support.
pub type OverlayedChangeSet = OverlayedMap<StorageKey, Option<StorageValue>>;

#[derive(Debug, Default, Clone)]
pub struct OverlayedContext {
	/// The number of how many transactions beginning from the first transactions are started
	/// by the client. Those transactions are protected against close (commit, rollback)
	/// when in runtime mode.
	num_client_transactions: usize,
	/// Determines whether the node is using the overlay from the client or the runtime.
	execution_mode: ExecutionMode,
	/// Total number of transactions (same as `top.number_transaction`).
	number_transactions: usize,
}

/// Holds a set of changes with the ability modify them using nested transactions.
#[derive(Debug, Clone)]
pub struct OverlayedMap<K, V> {
	/// Stores the changes that this overlay constitutes.
	changes: BTreeMap<K, OverlayedEntry<V>>,
	/// Stores which keys are dirty per transaction. Needed in order to determine which
	/// values to merge into the parent transaction on commit. The length of this vector
	/// therefore determines how many nested transactions are currently open (depth).
	dirty_keys: DirtyKeysSets<K>,
}

impl<K, V> Default for OverlayedMap<K, V> {
	fn default() -> Self {
		Self { changes: BTreeMap::new(), dirty_keys: SmallVec::new() }
	}
}

#[cfg(feature = "std")]
impl From<sp_core::storage::StorageMap> for OverlayedMap<StorageKey, Option<StorageValue>> {
	fn from(storage: sp_core::storage::StorageMap) -> Self {
		Self {
			changes: storage
				.into_iter()
				.map(|(k, v)| (k, OverlayedEntry { transactions: SmallVec::from_iter([Some(v)]) }))
				.collect(),
			dirty_keys: Default::default(),
		}
	}
}

impl Default for ExecutionMode {
	fn default() -> Self {
		Self::Client
	}
}

impl<V> OverlayedEntry<V> {
	/// The value as seen by the current transaction.
	pub fn value_ref(&self) -> &V {
		&self.transactions.last().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// The value as seen by the current transaction.
	pub fn into_value(mut self) -> V {
		self.transactions.pop().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// Mutable reference to the most recent version.
	fn value_mut(&mut self) -> &mut V {
		self.transactions.last_mut().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// Remove the last version and return it.
	fn pop_transaction(&mut self) -> V {
		self.transactions.pop().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// Writes a new version of a value.
	///
	/// This makes sure that the old version is not overwritten and can be properly
	/// rolled back when required.
	fn set(&mut self, value: V, first_write_in_tx: bool) {
		if first_write_in_tx || self.transactions.is_empty() {
			self.transactions.push(value);
		} else {
			*self.value_mut() = value;
		}
	}
}

impl<V> OverlayedEntry<Option<V>> {
	/// The value as seen by the current transaction.
	pub fn value(&self) -> Option<&V> {
		self.value_ref().as_ref()
	}
}

/// Inserts a key into the dirty set.
///
/// Returns true iff we are currently have at least one open transaction and if this
/// is the first write to the given key that transaction.
fn insert_dirty<K: Ord + Hash>(set: &mut DirtyKeysSets<K>, key: K) -> bool {
	set.last_mut().map(|dk| dk.insert(key)).unwrap_or_default()
}

impl<K: Ord + Hash + Clone, V> OverlayedMap<K, V> {
	/// True if no changes at all are contained in the change set.
	pub fn is_empty(&self) -> bool {
		self.changes.is_empty()
	}

	/// Get an optional reference to the value stored for the specified key.
	pub fn get<Q>(&self, key: &Q) -> Option<&OverlayedEntry<V>>
	where
		K: sp_std::borrow::Borrow<Q>,
		Q: Ord + ?Sized,
	{
		self.changes.get(key)
	}

	/// Set a new value for the specified key.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub fn set(&mut self, key: K, value: V) {
		let overlayed = self.changes.entry(key.clone()).or_default();
		overlayed.set(value, insert_dirty(&mut self.dirty_keys, key));
	}

	/// Get a list of all changes as seen by current transaction.
	pub fn changes(&self) -> impl Iterator<Item = (&K, &OverlayedEntry<V>)> {
		self.changes.iter()
	}

	/// Get a list of all changes as seen by current transaction.
	pub fn changes_mut(&mut self) -> impl Iterator<Item = (&K, &mut OverlayedEntry<V>)> {
		self.changes.iter_mut()
	}

	/// Get a list of all changes as seen by current transaction, consumes
	/// the overlay.
	pub fn into_changes(self) -> impl Iterator<Item = (K, OverlayedEntry<V>)> {
		self.changes.into_iter()
	}

	/// Consume this changeset and return all committed changes.
	pub fn drain_committed(self) -> impl Iterator<Item = (K, V)> {
		self.changes.into_iter().map(|(k, mut v)| (k, v.pop_transaction()))
	}

	/// Returns the current nesting depth of the transaction stack.
	///
	/// A value of zero means that no transaction is open and changes are committed on write.
	pub fn transaction_depth(&self) -> usize {
		self.dirty_keys.len()
	}

	fn close_transaction(
		&mut self,
		rollback: bool,
		transaction_depth: usize,
	) -> Result<(), NoOpenTransaction> {
		debug_assert!(transaction_depth == self.dirty_keys.len());
		for key in self.dirty_keys.pop().ok_or(NoOpenTransaction)? {
			let overlayed = self.changes.get_mut(&key).expect(
				"\
				A write to an OverlayedValue is recorded in the dirty key set. Before an
				OverlayedValue is removed, its containing dirty set is removed. This
				function is only called for keys that are in the dirty set. qed\
			",
			);

			if rollback {
				overlayed.pop_transaction();

				// We need to remove the key as an `OverlayValue` with no transactions
				// violates its invariant of always having at least one transaction.
				if overlayed.transactions.is_empty() {
					self.changes.remove(&key);
				}
			} else {
				let has_predecessor = if let Some(dirty_keys) = self.dirty_keys.last_mut() {
					// Not the last tx: Did the previous tx write to this key?
					!dirty_keys.insert(key)
				} else {
					// Last tx: Is there already a value in the committed set?
					// Check against one rather than empty because the current tx is still
					// in the list as it is popped later in this function.
					overlayed.transactions.len() > 1
				};

				// We only need to merge if there is an pre-existing value. It may be a value from
				// the previous transaction or a value committed without any open transaction.
				if has_predecessor {
					let dropped_tx = overlayed.pop_transaction();
					*overlayed.value_mut() = dropped_tx;
				}
			}
		}

		Ok(())
	}
}

impl<K: Ord + Hash + Clone, V> Transactional for OverlayedMap<K, V> {
	const REQUIRE_START_TRANSACTION: bool = true;

	fn start_transaction(&mut self) {
		self.dirty_keys.push(Default::default());
	}

	fn commit_transaction(&mut self, depth: usize) -> Result<(), NoOpenTransaction> {
		self.close_transaction(false, depth)
	}

	fn rollback_transaction(&mut self, depth: usize) -> Result<bool, NoOpenTransaction> {
		self.close_transaction(true, depth)?;
		Ok(self.changes.is_empty())
	}
}

impl OverlayedContext {
	/// Create a new changeset at the same transaction state but without any contents.
	///
	/// This changeset might be created when there are already open transactions.
	/// We need to catch up here so that the child is at the same transaction depth.
	pub fn spawn_child<K: Clone, V>(&self) -> OverlayedMap<K, V> {
		use sp_std::iter::repeat;
		OverlayedMap {
			changes: Default::default(),
			dirty_keys: repeat(Set::new()).take(self.transaction_depth()).collect(),
		}
	}

	/// Call this before transfering control to the runtime.
	///
	/// This protects all existing transactions from being removed by the runtime.
	/// Calling this while already inside the runtime will return an error.
	///
	/// This assume current transaction layer is empty (a new transaction
	/// has been open or no rollback is needed).
	pub fn enter_runtime(&mut self) -> Result<(), AlreadyInRuntime> {
		if let ExecutionMode::Runtime = self.execution_mode {
			return Err(AlreadyInRuntime)
		}
		self.execution_mode = ExecutionMode::Runtime;
		self.num_client_transactions = self.number_transactions;
		Ok(())
	}

	/// Register start of a transaction in context.
	pub fn start_transaction(&mut self) {
		self.number_transactions += 1;
	}

	/// Rollback a transaction in context.
	pub fn rollback_transaction(&mut self) -> Result<(), NoOpenTransaction> {
		// runtime is not allowed to close transactions started by the client
		if let ExecutionMode::Runtime = self.execution_mode {
			if self.number_transactions <= self.num_client_transactions {
				return Err(NoOpenTransaction)
			}
		}
		if self.number_transactions == 0 {
			return Err(NoOpenTransaction)
		}

		self.number_transactions -= 1;
		Ok(())
	}

	/// Rollback a transaction in context.
	pub fn commit_transaction(&mut self) -> Result<(), NoOpenTransaction> {
		self.rollback_transaction()
	}

	/// Call this when control returns from the runtime.
	/// Returns number of transaction to close.
	#[must_use = "Transactions should be rollback or commited depending on logic."]
	pub fn exit_runtime(&mut self) -> Result<usize, NotInRuntime> {
		if let ExecutionMode::Client = self.execution_mode {
			return Err(NotInRuntime)
		}
		self.execution_mode = ExecutionMode::Client;
		let result = self.number_transactions - self.num_client_transactions;
		self.num_client_transactions = 0;
		Ok(result)
	}

	/// Panic if we cannot drain committed (if transactions are open).
	pub fn guard_drain_committed(&self) {
		assert!(self.number_transactions == 0, "Drain is not allowed with open transactions.");
	}

	/// Number of open transaction (including non runtime ones).
	pub fn transaction_depth(&self) -> usize {
		self.number_transactions
	}
}

impl OverlayedChangeSet {
	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(
		&self,
		key: &[u8],
		start: u32,
		limit: Option<u32>,
		stats: &StateMachineStats,
	) -> Option<Option<&[u8]>> {
		if let Some(x) = self.get(key) {
			let value = range_slice(x.value().map(AsRef::as_ref), start, limit);
			let size_read = value.map(|x| x.len() as u64).unwrap_or(0);
			stats.tally_read_modified(size_read);
			Some(value)
		} else {
			None
		}
	}

	/// Get a mutable reference for a value.
	///
	/// Can be rolled back or committed when called inside a transaction.
	#[must_use = "A change was registered, so this value MUST be modified."]
	pub fn modify(
		&mut self,
		key: StorageKey,
		init: impl Fn() -> StorageValue,
	) -> &mut Option<StorageValue> {
		let overlayed = self.changes.entry(key.clone()).or_default();
		let first_write_in_tx = insert_dirty(&mut self.dirty_keys, key);
		let clone_into_new_tx = if let Some(tx) = overlayed.transactions.last() {
			if first_write_in_tx {
				Some(tx.clone())
			} else {
				None
			}
		} else {
			Some(Some(init()))
		};

		if let Some(cloned) = clone_into_new_tx {
			overlayed.set(cloned, first_write_in_tx);
		}
		overlayed.value_mut()
	}

	/// Set all values to deleted which are matched by the predicate.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub fn clear_where(&mut self, predicate: impl Fn(&[u8], &OverlayedValue) -> bool) -> u32 {
		let mut count = 0;
		for (key, val) in self.changes.iter_mut().filter(|(k, v)| predicate(k, v)) {
			if val.value_ref().is_some() {
				count += 1;
			}
			val.set(None, insert_dirty(&mut self.dirty_keys, key.clone()));
		}
		count
	}

	/// Get the iterator over all changes that follow the supplied `key`.
	pub fn changes_after(&self, key: &[u8]) -> impl Iterator<Item = (&[u8], &OverlayedValue)> {
		use sp_std::ops::Bound;
		let range = (Bound::Excluded(key), Bound::Unbounded);
		self.changes.range::<[u8], _>(range).map(|(k, v)| (k.as_slice(), v))
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use pretty_assertions::assert_eq;

	type Changes<'a> = Vec<(&'a [u8], Option<&'a [u8]>)>;
	type Drained<'a> = Vec<(&'a [u8], Option<&'a [u8]>)>;

	fn assert_changes(is: &OverlayedChangeSet, expected: &Changes) {
		let is: Changes =
			is.changes().map(|(k, v)| (k.as_ref(), v.value().map(AsRef::as_ref))).collect();
		assert_eq!(&is, expected);
	}

	fn assert_drained_changes(is: OverlayedChangeSet, expected: Changes) {
		let is = is.drain_committed().collect::<Vec<_>>();
		let expected = expected
			.iter()
			.map(|(k, v)| (k.to_vec(), v.map(From::from)))
			.collect::<Vec<_>>();
		assert_eq!(is, expected);
	}

	fn assert_drained(is: OverlayedChangeSet, expected: Drained) {
		let is = is.drain_committed().collect::<Vec<_>>();
		let expected = expected
			.iter()
			.map(|(k, v)| (k.to_vec(), v.map(From::from)))
			.collect::<Vec<_>>();
		assert_eq!(is, expected);
	}

	#[test]
	fn no_transaction_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()));

		assert_drained(changeset, vec![(b"key0", Some(b"val0-1")), (b"key1", Some(b"val1"))]);
	}

	#[test]
	fn transaction_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		// no transaction: committed on set
		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		// we will commit that later
		changeset.set(b"key42".to_vec(), Some(b"val42".to_vec()));
		changeset.set(b"key99".to_vec(), Some(b"val99".to_vec()));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		// we will roll that back
		changeset.set(b"key42".to_vec(), Some(b"val42-rolled".to_vec()));
		changeset.set(b"key7".to_vec(), Some(b"val7-rolled".to_vec()));
		changeset.set(b"key0".to_vec(), Some(b"val0-rolled".to_vec()));
		changeset.set(b"key5".to_vec(), Some(b"val5-rolled".to_vec()));

		// changes contain all changes not only the commmited ones.
		let all_changes: Changes = vec![
			(b"key0", Some(b"val0-rolled")),
			(b"key1", Some(b"val1")),
			(b"key42", Some(b"val42-rolled")),
			(b"key5", Some(b"val5-rolled")),
			(b"key7", Some(b"val7-rolled")),
			(b"key99", Some(b"val99")),
		];
		assert_changes(&changeset, &all_changes);

		// this should be no-op
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 4);
		changeset.rollback_transaction(4).unwrap();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction(3).unwrap();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		// roll back our first transactions that actually contains something
		changeset.rollback_transaction(2).unwrap();
		assert_eq!(changeset.transaction_depth(), 1);

		let rolled_back: Changes = vec![
			(b"key0", Some(b"val0-1")),
			(b"key1", Some(b"val1")),
			(b"key42", Some(b"val42")),
			(b"key99", Some(b"val99")),
		];
		assert_changes(&changeset, &rolled_back);

		changeset.commit_transaction(1).unwrap();
		assert_eq!(changeset.transaction_depth(), 0);
		assert_changes(&changeset, &rolled_back);

		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn transaction_commit_then_rollback_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		changeset.set(b"key42".to_vec(), Some(b"val42".to_vec()));
		changeset.set(b"key99".to_vec(), Some(b"val99".to_vec()));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		changeset.set(b"key42".to_vec(), Some(b"val42-rolled".to_vec()));
		changeset.set(b"key7".to_vec(), Some(b"val7-rolled".to_vec()));
		changeset.set(b"key0".to_vec(), Some(b"val0-rolled".to_vec()));
		changeset.set(b"key5".to_vec(), Some(b"val5-rolled".to_vec()));

		let all_changes: Changes = vec![
			(b"key0", Some(b"val0-rolled")),
			(b"key1", Some(b"val1")),
			(b"key42", Some(b"val42-rolled")),
			(b"key5", Some(b"val5-rolled")),
			(b"key7", Some(b"val7-rolled")),
			(b"key99", Some(b"val99")),
		];
		assert_changes(&changeset, &all_changes);

		// this should be no-op
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 4);
		changeset.rollback_transaction(4).unwrap();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction(3).unwrap();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		changeset.commit_transaction(2).unwrap();
		assert_eq!(changeset.transaction_depth(), 1);

		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction(1).unwrap();
		assert_eq!(changeset.transaction_depth(), 0);

		let rolled_back: Changes = vec![(b"key0", Some(b"val0-1")), (b"key1", Some(b"val1"))];
		assert_changes(&changeset, &rolled_back);

		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn modify_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		let init = || b"valinit".to_vec();

		// committed set
		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), None);
		let val = changeset.modify(b"key3".to_vec(), init);
		assert_eq!(val, &Some(b"valinit".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		// non existing value -> init value should be returned
		let val = changeset.modify(b"key2".to_vec(), init);
		assert_eq!(val, &Some(b"valinit".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		// existing value should be returned by modify
		let val = changeset.modify(b"key0".to_vec(), init);
		assert_eq!(val, &Some(b"val0".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		// should work for deleted keys
		let val = changeset.modify(b"key1".to_vec(), init);
		assert_eq!(val, &None);
		*val = Some(b"deleted-modified".to_vec());

		let all_changes: Changes = vec![
			(b"key0", Some(b"val0-modified")),
			(b"key1", Some(b"deleted-modified")),
			(b"key2", Some(b"valinit-modified")),
			(b"key3", Some(b"valinit-modified")),
		];
		assert_changes(&changeset, &all_changes);
		changeset.commit_transaction(2).unwrap();
		assert_eq!(changeset.transaction_depth(), 1);
		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction(1).unwrap();
		assert_eq!(changeset.transaction_depth(), 0);
		let rolled_back: Changes =
			vec![(b"key0", Some(b"val0")), (b"key1", None), (b"key3", Some(b"valinit-modified"))];
		assert_changes(&changeset, &rolled_back);
		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn clear_works() {
		let mut changeset = OverlayedChangeSet::default();

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()));
		changeset.set(b"del1".to_vec(), Some(b"delval1".to_vec()));
		changeset.set(b"del2".to_vec(), Some(b"delval2".to_vec()));

		changeset.start_transaction();

		changeset.clear_where(|k, _| k.starts_with(b"del"));

		assert_changes(
			&changeset,
			&vec![
				(b"del1", None),
				(b"del2", None),
				(b"key0", Some(b"val0")),
				(b"key1", Some(b"val1")),
			],
		);

		changeset.rollback_transaction(1).unwrap();

		assert_changes(
			&changeset,
			&vec![
				(b"del1", Some(b"delval1")),
				(b"del2", Some(b"delval2")),
				(b"key0", Some(b"val0")),
				(b"key1", Some(b"val1")),
			],
		);
	}

	#[test]
	fn next_change_works() {
		let mut changeset = OverlayedChangeSet::default();

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()));
		changeset.set(b"key2".to_vec(), Some(b"val2".to_vec()));

		changeset.start_transaction();

		changeset.set(b"key3".to_vec(), Some(b"val3".to_vec()));
		changeset.set(b"key4".to_vec(), Some(b"val4".to_vec()));
		changeset.set(b"key11".to_vec(), Some(b"val11".to_vec()));

		assert_eq!(changeset.changes_after(b"key0").next().unwrap().0, b"key1");
		assert_eq!(
			changeset.changes_after(b"key0").next().unwrap().1.value(),
			Some(&b"val1".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key1").next().unwrap().0, b"key11");
		assert_eq!(
			changeset.changes_after(b"key1").next().unwrap().1.value(),
			Some(&b"val11".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key11").next().unwrap().0, b"key2");
		assert_eq!(
			changeset.changes_after(b"key11").next().unwrap().1.value(),
			Some(&b"val2".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key2").next().unwrap().0, b"key3");
		assert_eq!(
			changeset.changes_after(b"key2").next().unwrap().1.value(),
			Some(&b"val3".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key3").next().unwrap().0, b"key4");
		assert_eq!(
			changeset.changes_after(b"key3").next().unwrap().1.value(),
			Some(&b"val4".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key4").next(), None);

		changeset.rollback_transaction(1).unwrap();

		assert_eq!(changeset.changes_after(b"key0").next().unwrap().0, b"key1");
		assert_eq!(
			changeset.changes_after(b"key0").next().unwrap().1.value(),
			Some(&b"val1".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key1").next().unwrap().0, b"key2");
		assert_eq!(
			changeset.changes_after(b"key1").next().unwrap().1.value(),
			Some(&b"val2".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key11").next().unwrap().0, b"key2");
		assert_eq!(
			changeset.changes_after(b"key11").next().unwrap().1.value(),
			Some(&b"val2".to_vec())
		);
		assert_eq!(changeset.changes_after(b"key2").next(), None);
		assert_eq!(changeset.changes_after(b"key3").next(), None);
		assert_eq!(changeset.changes_after(b"key4").next(), None);
	}

	#[test]
	fn no_open_tx_commit_errors() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		assert_eq!(changeset.commit_transaction(0), Err(NoOpenTransaction));
	}

	#[test]
	fn no_open_tx_rollback_errors() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		assert_eq!(changeset.rollback_transaction(0), Err(NoOpenTransaction));
	}

	#[test]
	fn unbalanced_transactions_errors() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		changeset.commit_transaction(1).unwrap();
		assert_eq!(changeset.commit_transaction(0), Err(NoOpenTransaction));
	}

	#[test]
	fn runtime_cannot_close_client_tx() {
		let mut context = OverlayedContext::default();
		context.start_transaction();
		context.enter_runtime().unwrap();
		context.start_transaction();
		context.commit_transaction().unwrap();
		assert_eq!(context.rollback_transaction(), Err(NoOpenTransaction));
	}

	#[test]
	fn enter_exit_runtime_fails_when_already_in_requested_mode() {
		let mut context = OverlayedContext::default();

		assert_eq!(context.exit_runtime(), Err(NotInRuntime));
		assert_eq!(context.enter_runtime(), Ok(()));
		assert_eq!(context.enter_runtime(), Err(AlreadyInRuntime));
		assert_eq!(context.exit_runtime(), Ok(0));
		assert_eq!(context.exit_runtime(), Err(NotInRuntime));
	}
}
