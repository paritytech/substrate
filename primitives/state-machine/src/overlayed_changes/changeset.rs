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

use super::{Extrinsics, StorageKey, StorageValue};

#[cfg(not(feature = "std"))]
use sp_std::collections::btree_set::BTreeSet as Set;
#[cfg(feature = "std")]
use std::collections::HashSet as Set;

use crate::warn;
use smallvec::SmallVec;
use sp_std::{
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	hash::Hash,
};

const PROOF_OVERLAY_NON_EMPTY: &str = "\
	An OverlayValue is always created with at least one transaction and dropped as soon
	as the last transaction is removed; qed";

type DirtyKeysSets<K> = SmallVec<[Set<K>; 5]>;
type Transactions<V> = SmallVec<[InnerValue<V>; 5]>;

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
	/// Exeuting in client mode: Removal of all transactions possible.
	Client,
	/// Executing in runtime mode: Transactions started by the client are protected.
	Runtime,
}

#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
struct InnerValue<V> {
	/// Current value. None if value has been deleted.
	value: V,
	/// The set of extrinsic indices where the values has been changed.
	extrinsics: Extrinsics,
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

/// Holds a set of changes with the ability modify them using nested transactions.
#[derive(Debug, Clone)]
pub struct OverlayedMap<K: Ord + Hash, V> {
	/// Stores the changes that this overlay constitutes.
	changes: BTreeMap<K, OverlayedEntry<V>>,
	/// Stores which keys are dirty per transaction. Needed in order to determine which
	/// values to merge into the parent transaction on commit. The length of this vector
	/// therefore determines how many nested transactions are currently open (depth).
	dirty_keys: DirtyKeysSets<K>,
	/// The number of how many transactions beginning from the first transactions are started
	/// by the client. Those transactions are protected against close (commit, rollback)
	/// when in runtime mode.
	num_client_transactions: usize,
	/// Determines whether the node is using the overlay from the client or the runtime.
	execution_mode: ExecutionMode,
}

impl<K: Ord + Hash, V> Default for OverlayedMap<K, V> {
	fn default() -> Self {
		Self {
			changes: BTreeMap::new(),
			dirty_keys: SmallVec::new(),
			num_client_transactions: Default::default(),
			execution_mode: Default::default(),
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
		&self.transactions.last().expect(PROOF_OVERLAY_NON_EMPTY).value
	}

	/// The value as seen by the current transaction.
	pub fn into_value(mut self) -> V {
		self.transactions.pop().expect(PROOF_OVERLAY_NON_EMPTY).value
	}

	/// Unique list of extrinsic indices which modified the value.
	pub fn extrinsics(&self) -> BTreeSet<u32> {
		let mut set = BTreeSet::new();
		self.transactions
			.iter()
			.for_each(|t| t.extrinsics.copy_extrinsics_into(&mut set));
		set
	}

	/// Mutable reference to the most recent version.
	fn value_mut(&mut self) -> &mut V {
		&mut self.transactions.last_mut().expect(PROOF_OVERLAY_NON_EMPTY).value
	}

	/// Remove the last version and return it.
	fn pop_transaction(&mut self) -> InnerValue<V> {
		self.transactions.pop().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// Mutable reference to the set which holds the indices for the **current transaction only**.
	fn transaction_extrinsics_mut(&mut self) -> &mut Extrinsics {
		&mut self.transactions.last_mut().expect(PROOF_OVERLAY_NON_EMPTY).extrinsics
	}

	/// Writes a new version of a value.
	///
	/// This makes sure that the old version is not overwritten and can be properly
	/// rolled back when required.
	fn set(&mut self, value: V, first_write_in_tx: bool, at_extrinsic: Option<u32>) {
		if first_write_in_tx || self.transactions.is_empty() {
			self.transactions.push(InnerValue { value, extrinsics: Default::default() });
		} else {
			*self.value_mut() = value;
		}

		if let Some(extrinsic) = at_extrinsic {
			self.transaction_extrinsics_mut().insert(extrinsic);
		}
	}
}

impl OverlayedEntry<Option<StorageValue>> {
	/// The value as seen by the current transaction.
	pub fn value(&self) -> Option<&StorageValue> {
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
	/// Create a new changeset at the same transaction state but without any contents.
	///
	/// This changeset might be created when there are already open transactions.
	/// We need to catch up here so that the child is at the same transaction depth.
	pub fn spawn_child(&self) -> Self {
		use sp_std::iter::repeat;
		Self {
			changes: Default::default(),
			dirty_keys: repeat(Set::new()).take(self.transaction_depth()).collect(),
			num_client_transactions: self.num_client_transactions,
			execution_mode: self.execution_mode,
		}
	}

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
	pub fn set(&mut self, key: K, value: V, at_extrinsic: Option<u32>) {
		let overlayed = self.changes.entry(key.clone()).or_default();
		overlayed.set(value, insert_dirty(&mut self.dirty_keys, key), at_extrinsic);
	}

	/// Get a list of all changes as seen by current transaction.
	pub fn changes(&self) -> impl Iterator<Item = (&K, &OverlayedEntry<V>)> {
		self.changes.iter()
	}

	/// Get a list of all changes as seen by current transaction, consumes
	/// the overlay.
	pub fn into_changes(self) -> impl Iterator<Item = (K, OverlayedEntry<V>)> {
		self.changes.into_iter()
	}

	/// Consume this changeset and return all committed changes.
	///
	/// Panics:
	/// Panics if there are open transactions: `transaction_depth() > 0`
	pub fn drain_commited(self) -> impl Iterator<Item = (K, V)> {
		assert!(self.transaction_depth() == 0, "Drain is not allowed with open transactions.");
		self.changes.into_iter().map(|(k, mut v)| (k, v.pop_transaction().value))
	}

	/// Returns the current nesting depth of the transaction stack.
	///
	/// A value of zero means that no transaction is open and changes are committed on write.
	pub fn transaction_depth(&self) -> usize {
		self.dirty_keys.len()
	}

	/// Call this before transfering control to the runtime.
	///
	/// This protects all existing transactions from being removed by the runtime.
	/// Calling this while already inside the runtime will return an error.
	pub fn enter_runtime(&mut self) -> Result<(), AlreadyInRuntime> {
		if let ExecutionMode::Runtime = self.execution_mode {
			return Err(AlreadyInRuntime)
		}
		self.execution_mode = ExecutionMode::Runtime;
		self.num_client_transactions = self.transaction_depth();
		Ok(())
	}

	/// Call this when control returns from the runtime.
	///
	/// This commits all dangling transaction left open by the runtime.
	/// Calling this while already outside the runtime will return an error.
	pub fn exit_runtime(&mut self) -> Result<(), NotInRuntime> {
		if let ExecutionMode::Client = self.execution_mode {
			return Err(NotInRuntime)
		}
		self.execution_mode = ExecutionMode::Client;
		if self.has_open_runtime_transactions() {
			warn!(
				"{} storage transactions are left open by the runtime. Those will be rolled back.",
				self.transaction_depth() - self.num_client_transactions,
			);
		}
		while self.has_open_runtime_transactions() {
			self.rollback_transaction()
				.expect("The loop condition checks that the transaction depth is > 0; qed");
		}
		Ok(())
	}

	/// Start a new nested transaction.
	///
	/// This allows to either commit or roll back all changes that were made while this
	/// transaction was open. Any transaction must be closed by either `commit_transaction`
	/// or `rollback_transaction` before this overlay can be converted into storage changes.
	///
	/// Changes made without any open transaction are committed immediately.
	pub fn start_transaction(&mut self) {
		self.dirty_keys.push(Default::default());
	}

	/// Rollback the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are discarded. Returns an error if
	/// there is no open transaction that can be rolled back.
	pub fn rollback_transaction(&mut self) -> Result<(), NoOpenTransaction> {
		self.close_transaction(true)
	}

	/// Commit the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are committed. Returns an error if
	/// there is no open transaction that can be committed.
	pub fn commit_transaction(&mut self) -> Result<(), NoOpenTransaction> {
		self.close_transaction(false)
	}

	fn close_transaction(&mut self, rollback: bool) -> Result<(), NoOpenTransaction> {
		// runtime is not allowed to close transactions started by the client
		if let ExecutionMode::Runtime = self.execution_mode {
			if !self.has_open_runtime_transactions() {
				return Err(NoOpenTransaction)
			}
		}

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
					*overlayed.value_mut() = dropped_tx.value;
					overlayed.transaction_extrinsics_mut().extend(dropped_tx.extrinsics);
				}
			}
		}

		Ok(())
	}

	fn has_open_runtime_transactions(&self) -> bool {
		self.transaction_depth() > self.num_client_transactions
	}
}

impl OverlayedChangeSet {
	/// Get a mutable reference for a value.
	///
	/// Can be rolled back or committed when called inside a transaction.
	#[must_use = "A change was registered, so this value MUST be modified."]
	pub fn modify(
		&mut self,
		key: StorageKey,
		init: impl Fn() -> StorageValue,
		at_extrinsic: Option<u32>,
	) -> &mut Option<StorageValue> {
		let overlayed = self.changes.entry(key.clone()).or_default();
		let first_write_in_tx = insert_dirty(&mut self.dirty_keys, key);
		let clone_into_new_tx = if let Some(tx) = overlayed.transactions.last() {
			if first_write_in_tx {
				Some(tx.value.clone())
			} else {
				None
			}
		} else {
			Some(Some(init()))
		};

		if let Some(cloned) = clone_into_new_tx {
			overlayed.set(cloned, first_write_in_tx, at_extrinsic);
		}
		overlayed.value_mut()
	}

	/// Set all values to deleted which are matched by the predicate.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub fn clear_where(
		&mut self,
		predicate: impl Fn(&[u8], &OverlayedValue) -> bool,
		at_extrinsic: Option<u32>,
	) -> u32 {
		let mut count = 0;
		for (key, val) in self.changes.iter_mut().filter(|(k, v)| predicate(k, v)) {
			if val.value_ref().is_some() {
				count += 1;
			}
			val.set(None, insert_dirty(&mut self.dirty_keys, key.clone()), at_extrinsic);
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

	type Changes<'a> = Vec<(&'a [u8], (Option<&'a [u8]>, Vec<u32>))>;
	type Drained<'a> = Vec<(&'a [u8], Option<&'a [u8]>)>;

	fn assert_changes(is: &OverlayedChangeSet, expected: &Changes) {
		let is: Changes = is
			.changes()
			.map(|(k, v)| {
				(k.as_ref(), (v.value().map(AsRef::as_ref), v.extrinsics().into_iter().collect()))
			})
			.collect();
		assert_eq!(&is, expected);
	}

	fn assert_drained_changes(is: OverlayedChangeSet, expected: Changes) {
		let is = is.drain_commited().collect::<Vec<_>>();
		let expected = expected
			.iter()
			.map(|(k, v)| (k.to_vec(), v.0.map(From::from)))
			.collect::<Vec<_>>();
		assert_eq!(is, expected);
	}

	fn assert_drained(is: OverlayedChangeSet, expected: Drained) {
		let is = is.drain_commited().collect::<Vec<_>>();
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

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(2));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()), Some(9));

		assert_drained(changeset, vec![(b"key0", Some(b"val0-1")), (b"key1", Some(b"val1"))]);
	}

	#[test]
	fn transaction_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		// no transaction: committed on set
		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(1));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()), Some(10));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		// we will commit that later
		changeset.set(b"key42".to_vec(), Some(b"val42".to_vec()), Some(42));
		changeset.set(b"key99".to_vec(), Some(b"val99".to_vec()), Some(99));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		// we will roll that back
		changeset.set(b"key42".to_vec(), Some(b"val42-rolled".to_vec()), Some(421));
		changeset.set(b"key7".to_vec(), Some(b"val7-rolled".to_vec()), Some(77));
		changeset.set(b"key0".to_vec(), Some(b"val0-rolled".to_vec()), Some(1000));
		changeset.set(b"key5".to_vec(), Some(b"val5-rolled".to_vec()), None);

		// changes contain all changes not only the commmited ones.
		let all_changes: Changes = vec![
			(b"key0", (Some(b"val0-rolled"), vec![1, 10, 1000])),
			(b"key1", (Some(b"val1"), vec![1])),
			(b"key42", (Some(b"val42-rolled"), vec![42, 421])),
			(b"key5", (Some(b"val5-rolled"), vec![])),
			(b"key7", (Some(b"val7-rolled"), vec![77])),
			(b"key99", (Some(b"val99"), vec![99])),
		];
		assert_changes(&changeset, &all_changes);

		// this should be no-op
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 4);
		changeset.rollback_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		// roll back our first transactions that actually contains something
		changeset.rollback_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 1);

		let rolled_back: Changes = vec![
			(b"key0", (Some(b"val0-1"), vec![1, 10])),
			(b"key1", (Some(b"val1"), vec![1])),
			(b"key42", (Some(b"val42"), vec![42])),
			(b"key99", (Some(b"val99"), vec![99])),
		];
		assert_changes(&changeset, &rolled_back);

		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 0);
		assert_changes(&changeset, &rolled_back);

		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn transaction_commit_then_rollback_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(1));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()), Some(10));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		changeset.set(b"key42".to_vec(), Some(b"val42".to_vec()), Some(42));
		changeset.set(b"key99".to_vec(), Some(b"val99".to_vec()), Some(99));

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		changeset.set(b"key42".to_vec(), Some(b"val42-rolled".to_vec()), Some(421));
		changeset.set(b"key7".to_vec(), Some(b"val7-rolled".to_vec()), Some(77));
		changeset.set(b"key0".to_vec(), Some(b"val0-rolled".to_vec()), Some(1000));
		changeset.set(b"key5".to_vec(), Some(b"val5-rolled".to_vec()), None);

		let all_changes: Changes = vec![
			(b"key0", (Some(b"val0-rolled"), vec![1, 10, 1000])),
			(b"key1", (Some(b"val1"), vec![1])),
			(b"key42", (Some(b"val42-rolled"), vec![42, 421])),
			(b"key5", (Some(b"val5-rolled"), vec![])),
			(b"key7", (Some(b"val7-rolled"), vec![77])),
			(b"key99", (Some(b"val99"), vec![99])),
		];
		assert_changes(&changeset, &all_changes);

		// this should be no-op
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 4);
		changeset.rollback_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 1);

		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 0);

		let rolled_back: Changes =
			vec![(b"key0", (Some(b"val0-1"), vec![1, 10])), (b"key1", (Some(b"val1"), vec![1]))];
		assert_changes(&changeset, &rolled_back);

		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn modify_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		let init = || b"valinit".to_vec();

		// committed set
		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(0));
		changeset.set(b"key1".to_vec(), None, Some(1));
		let val = changeset.modify(b"key3".to_vec(), init, Some(3));
		assert_eq!(val, &Some(b"valinit".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 1);
		changeset.start_transaction();
		assert_eq!(changeset.transaction_depth(), 2);

		// non existing value -> init value should be returned
		let val = changeset.modify(b"key2".to_vec(), init, Some(2));
		assert_eq!(val, &Some(b"valinit".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		// existing value should be returned by modify
		let val = changeset.modify(b"key0".to_vec(), init, Some(10));
		assert_eq!(val, &Some(b"val0".to_vec()));
		val.as_mut().unwrap().extend_from_slice(b"-modified");

		// should work for deleted keys
		let val = changeset.modify(b"key1".to_vec(), init, Some(20));
		assert_eq!(val, &None);
		*val = Some(b"deleted-modified".to_vec());

		let all_changes: Changes = vec![
			(b"key0", (Some(b"val0-modified"), vec![0, 10])),
			(b"key1", (Some(b"deleted-modified"), vec![1, 20])),
			(b"key2", (Some(b"valinit-modified"), vec![2])),
			(b"key3", (Some(b"valinit-modified"), vec![3])),
		];
		assert_changes(&changeset, &all_changes);
		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 1);
		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 0);
		let rolled_back: Changes = vec![
			(b"key0", (Some(b"val0"), vec![0])),
			(b"key1", (None, vec![1])),
			(b"key3", (Some(b"valinit-modified"), vec![3])),
		];
		assert_changes(&changeset, &rolled_back);
		assert_drained_changes(changeset, rolled_back);
	}

	#[test]
	fn clear_works() {
		let mut changeset = OverlayedChangeSet::default();

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(2));
		changeset.set(b"del1".to_vec(), Some(b"delval1".to_vec()), Some(3));
		changeset.set(b"del2".to_vec(), Some(b"delval2".to_vec()), Some(4));

		changeset.start_transaction();

		changeset.clear_where(|k, _| k.starts_with(b"del"), Some(5));

		assert_changes(
			&changeset,
			&vec![
				(b"del1", (None, vec![3, 5])),
				(b"del2", (None, vec![4, 5])),
				(b"key0", (Some(b"val0"), vec![1])),
				(b"key1", (Some(b"val1"), vec![2])),
			],
		);

		changeset.rollback_transaction().unwrap();

		assert_changes(
			&changeset,
			&vec![
				(b"del1", (Some(b"delval1"), vec![3])),
				(b"del2", (Some(b"delval2"), vec![4])),
				(b"key0", (Some(b"val0"), vec![1])),
				(b"key1", (Some(b"val1"), vec![2])),
			],
		);
	}

	#[test]
	fn next_change_works() {
		let mut changeset = OverlayedChangeSet::default();

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(0));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(1));
		changeset.set(b"key2".to_vec(), Some(b"val2".to_vec()), Some(2));

		changeset.start_transaction();

		changeset.set(b"key3".to_vec(), Some(b"val3".to_vec()), Some(3));
		changeset.set(b"key4".to_vec(), Some(b"val4".to_vec()), Some(4));
		changeset.set(b"key11".to_vec(), Some(b"val11".to_vec()), Some(11));

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

		changeset.rollback_transaction().unwrap();

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
		assert_eq!(changeset.commit_transaction(), Err(NoOpenTransaction));
	}

	#[test]
	fn no_open_tx_rollback_errors() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		assert_eq!(changeset.rollback_transaction(), Err(NoOpenTransaction));
	}

	#[test]
	fn unbalanced_transactions_errors() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.commit_transaction(), Err(NoOpenTransaction));
	}

	#[test]
	#[should_panic]
	fn drain_with_open_transaction_panics() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		let _ = changeset.drain_commited();
	}

	#[test]
	fn runtime_cannot_close_client_tx() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		changeset.enter_runtime().unwrap();
		changeset.start_transaction();
		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.commit_transaction(), Err(NoOpenTransaction));
		assert_eq!(changeset.rollback_transaction(), Err(NoOpenTransaction));
	}

	#[test]
	fn exit_runtime_closes_runtime_tx() {
		let mut changeset = OverlayedChangeSet::default();

		changeset.start_transaction();

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));

		changeset.enter_runtime().unwrap();
		changeset.start_transaction();
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(2));
		changeset.exit_runtime().unwrap();

		changeset.commit_transaction().unwrap();
		assert_eq!(changeset.transaction_depth(), 0);

		assert_drained(changeset, vec![(b"key0", Some(b"val0"))]);
	}

	#[test]
	fn enter_exit_runtime_fails_when_already_in_requested_mode() {
		let mut changeset = OverlayedChangeSet::default();

		assert_eq!(changeset.exit_runtime(), Err(NotInRuntime));
		assert_eq!(changeset.enter_runtime(), Ok(()));
		assert_eq!(changeset.enter_runtime(), Err(AlreadyInRuntime));
		assert_eq!(changeset.exit_runtime(), Ok(()));
		assert_eq!(changeset.exit_runtime(), Err(NotInRuntime));
	}
}
