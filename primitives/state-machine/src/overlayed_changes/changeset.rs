// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use super::{StorageKey, StorageValue};

use itertools::Itertools;
use std::collections::{HashSet, BTreeMap, BTreeSet};
use smallvec::SmallVec;

const PROOF_DIRTY_KEYS: &str = "\
	We assume transactions are balanced. Every start of a transaction created one dirty
	keys element. This function is only called on transaction close. Therefore an element
	created when starting the transaction must exist; qed";

const PROOF_DIRTY_OVERLAY_VALUE: &str = "\
	A write to an OverlayedValue is recorded in the dirty key set. Before an OverlayedValues
	is removed its containing dirty set is removed. This function is only called for keys that
	are in the dirty set. Therefore the entry must exist; qed";

const PROOF_OVERLAY_NON_EMPTY: &str = "\
	An OverlayValue is always created with at least one transaction and dropped as soon
	as the last transaction is removed; qed";

type DirtyKeys = SmallVec<[HashSet<StorageKey>; 5]>;
type Transactions = SmallVec<[InnerValue; 5]>;

#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
struct InnerValue {
	/// Current value. None if value has been deleted.
	value: Option<StorageValue>,
	/// The set of extrinsic indices where the values has been changed.
	/// Is filled only if runtime has announced changes trie support.
	extrinsics: BTreeSet<u32>,
}

/// An overlay that contains all versions of a value for a specific key.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedValue {
	/// The individual versions of that value.
	/// One entry per transactions during that the value was actually written.
	transactions: Transactions,
}

/// Holds a set of changes with the ability modify them using nested transactions.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChangeSet {
	/// Stores the changes that this overlay constitutes.
	changes: BTreeMap<StorageKey, OverlayedValue>,
	/// Stores which keys are dirty per transaction. Needed in order to determine which
	/// values to merge into the parent transaction on commit. The length of this vector
	/// therefore determines how many nested transactions are currently open (depth).
	dirty_keys: DirtyKeys,
}

impl OverlayedValue {
	/// The value as seen by the current transaction.
	pub fn value(&self) -> Option<&StorageValue> {
		self.transactions.last().expect(PROOF_OVERLAY_NON_EMPTY).value.as_ref()
	}

	/// Unique list of extrinsic indices which modified the value.
	pub fn extrinsics(&self) -> impl Iterator<Item=&u32> {
		self.transactions.iter().flat_map(|t| t.extrinsics.iter()).unique()
	}

	/// Mutable reference to the most recent version.
	fn value_mut(&mut self) -> &mut Option<StorageValue> {
		&mut self.transactions.last_mut().expect(PROOF_OVERLAY_NON_EMPTY).value
	}

	/// Remove the last version and return it.
	fn pop_transaction(&mut self) -> InnerValue {
		self.transactions.pop().expect(PROOF_OVERLAY_NON_EMPTY)
	}

	/// Mutable reference to the set which holds the indices for the **current transaction only**.
	fn transaction_extrinsics_mut(&mut self) -> &mut BTreeSet<u32> {
		&mut self.transactions.last_mut().expect(PROOF_OVERLAY_NON_EMPTY).extrinsics
	}

	/// Writes a new version of a value.
	///
	/// This makes sure that the old version is not overwritten and can be properly
	/// rolled back when required.
	fn set(
		&mut self,
		value: Option<StorageValue>,
		first_write_in_tx: bool,
		at_extrinsic: Option<u32>
	) {
		if first_write_in_tx || self.transactions.is_empty() {
			self.transactions.push(InnerValue {
				value,
				.. Default::default()
			});
		} else {
			*self.value_mut() = value;
		}

		if let Some(extrinsic) = at_extrinsic {
			self.transaction_extrinsics_mut().insert(extrinsic);
		}
	}
}

/// Inserts a key into the dirty set.
///
/// Returns true iff we are currently have at least one open transaction and if this
/// is the first write to the given key that transaction.
fn insert_dirty(set: &mut DirtyKeys, key: StorageKey) -> bool {
	if let Some(dirty_keys) = set.last_mut() {
		dirty_keys.insert(key)
	} else {
		false
	}
}

impl OverlayedChangeSet {
	/// Create a new changeset with the specified transaction depth.
	pub fn with_depth(depth: usize) -> Self {
		use std::iter::repeat;
		Self {
			dirty_keys: repeat(HashSet::new()).take(depth).collect(),
			.. Default::default()
		}
	}

	/// True if no changes at all are contained in the change set.
	pub fn is_empty(&self) -> bool {
		self.changes.is_empty()
	}

	/// Get an optional reference to the value stored for the specified key.
	pub fn get(&self, key: &[u8]) -> Option<&OverlayedValue> {
		self.changes.get(key)
	}

	/// Set a new value for the specified key.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub fn set(
		&mut self,
		key: StorageKey,
		value: Option<StorageValue>,
		at_extrinsic: Option<u32>
	) {
		let overlayed = self.changes.entry(key.clone()).or_insert_with(Default::default);
		overlayed.set(value, insert_dirty(&mut self.dirty_keys, key), at_extrinsic);
	}

	/// Get a mutable reference for a value.
	///
	/// Can be rolled back or committed when called inside a transaction.
	#[must_use = "A change was registered, so this value MUST be modified."]
	pub fn modify(
		&mut self,
		key: StorageKey,
		init: impl Fn() -> StorageValue,
		at_extrinsic: Option<u32>
	) -> &mut Option<StorageValue> {
		let overlayed = self.changes.entry(key.clone()).or_insert_with(Default::default);
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
		at_extrinsic: Option<u32>
	) {
		for (key, val) in self.changes.iter_mut().filter(|(k, v)| predicate(k, v)) {
			val.set(None, insert_dirty(&mut self.dirty_keys, key.to_owned()), at_extrinsic);
		}
	}

	/// Get a list of all changes as seen by current transaction.
	pub fn changes(&self) -> impl Iterator<Item=(&StorageKey, &OverlayedValue)> {
		self.changes.iter()
	}

	/// Get the change that is next to the supplied key.
	pub fn next_change(&self, key: &[u8]) -> Option<(&[u8], &OverlayedValue)> {
		use std::ops::Bound;
		let range = (Bound::Excluded(key), Bound::Unbounded);
		self.changes.range::<[u8], _>(range).next().map(|(k, v)| (&k[..], v))
	}

	/// Consume this changeset and return all committed changes.
	///
	/// Panics:
	/// Panics if there are open transactions: `transaction_depth() > 0`
	pub fn drain_commited(self) -> impl Iterator<Item=(StorageKey, Option<StorageValue>)> {
		assert!(self.transaction_depth() == 0, "Drain is not allowed with open transactions.");
		self.changes.into_iter().map(|(k, mut v)| (k, v.pop_transaction().value))
	}

	/// Returns the current nesting depth of the transaction stack.
	///
	/// A value of zero means that no transaction is open and changes are committed on write.
	pub fn transaction_depth(&self) -> usize {
		self.dirty_keys.len()
	}

	/// Start a new nested transaction.
	///
	/// This allows to either commit or roll back all changes that where made while this
	/// transaction was open. Any transaction must be closed by one of the aforementioned
	/// functions before this overlay can be converted into storage changes.
	///
	/// Changes made without any open transaction are committed immediatly.
	pub fn start_transaction(&mut self) {
		self.dirty_keys.push(Default::default());
	}

	/// Rollback the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are discarded.
	///
	/// Panics:
	/// Will panic if there is no open transaction.
	pub fn rollback_transaction(&mut self) {
		self.close_transaction(true);
	}

	/// Commit the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are committed.
	///
	/// Panics:
	/// Will panic if there is no open transaction.
	pub fn commit_transaction(&mut self) {
		self.close_transaction(false);
	}

	fn close_transaction(&mut self, rollback: bool) {
		for key in self.dirty_keys.pop().expect(PROOF_DIRTY_KEYS) {
			let value = self.changes.get_mut(&key).expect(PROOF_DIRTY_OVERLAY_VALUE);

			if rollback {
				value.pop_transaction();

				// We need to remove the key as an `OverlayValue` with no transactions
				// violates its invariant of always having at least one transaction.
				if value.transactions.is_empty() {
					self.changes.remove(&key);
				}
			} else {
				let has_predecessor = ! if let Some(dirty_keys) = self.dirty_keys.last_mut() {
					// Not the last tx: Did the previous tx write to this key?
					dirty_keys.insert(key)
				} else {
					// Last tx: Is there already a value in the committed set?
					// Check against one rather than empty because the current tx is still
					// in the list as it is popped later in this function.
					value.transactions.len() == 1
				};

				// We only need to merge if in the previous tx (or committed set) there is
				// already an existing value.
				if has_predecessor {
					let dropped_tx = value.pop_transaction();
					*value.value_mut() = dropped_tx.value;
					value.transaction_extrinsics_mut().extend(dropped_tx.extrinsics);
				}
			}
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use pretty_assertions::assert_eq;

	type Changes<'a> = Vec<(&'a [u8], (Option<&'a [u8]>, Vec<u32>))>;
	type Drained<'a> = Vec<(&'a [u8], Option<&'a [u8]>)>;

	fn assert_changes(is: &OverlayedChangeSet, should: &Changes) {
		let is: Changes = is.changes().map(|(k, v)| {
			(k.as_ref(), (v.value().map(AsRef::as_ref), v.extrinsics().cloned().collect()))
		}).collect();
		assert_eq!(&is, should);
	}

	fn assert_drained_changes(is: OverlayedChangeSet, should: Changes) {
		let is = is.drain_commited().collect::<Vec<_>>();
		let should = should
			.iter()
			.map(|(k, v)| (k.to_vec(), v.0.map(From::from))).collect::<Vec<_>>();
		assert_eq!(is, should);
	}

	fn assert_drained(is: OverlayedChangeSet, should: Drained) {
		let is = is.drain_commited().collect::<Vec<_>>();
		let should = should
			.iter()
			.map(|(k, v)| (k.to_vec(), v.map(From::from))).collect::<Vec<_>>();
		assert_eq!(is, should);
	}

	#[test]
	fn no_transaction_works() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);

		changeset.set(b"key0".to_vec(), Some(b"val0".to_vec()), Some(1));
		changeset.set(b"key1".to_vec(), Some(b"val1".to_vec()), Some(2));
		changeset.set(b"key0".to_vec(), Some(b"val0-1".to_vec()), Some(9));

		assert_drained(changeset, vec![
			(b"key0", Some(b"val0-1")),
			(b"key1", Some(b"val1")),
		]);
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
		changeset.rollback_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		// roll back our first transactions that actually contains something
		changeset.rollback_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		let rolled_back: Changes = vec![
			(b"key0", (Some(b"val0-1"), vec![1, 10])),
			(b"key1", (Some(b"val1"), vec![1])),
			(b"key42", (Some(b"val42"), vec![42])),
			(b"key99", (Some(b"val99"), vec![99])),
		];
		assert_changes(&changeset, &rolled_back);

		changeset.commit_transaction();
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
		changeset.rollback_transaction();
		assert_eq!(changeset.transaction_depth(), 3);
		changeset.commit_transaction();
		assert_eq!(changeset.transaction_depth(), 2);
		assert_changes(&changeset, &all_changes);

		changeset.commit_transaction();
		assert_eq!(changeset.transaction_depth(), 1);

		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction();
		assert_eq!(changeset.transaction_depth(), 0);

		let rolled_back: Changes = vec![
			(b"key0", (Some(b"val0-1"), vec![1, 10])),
			(b"key1", (Some(b"val1"), vec![1])),
		];
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
		changeset.commit_transaction();
		assert_eq!(changeset.transaction_depth(), 1);
		assert_changes(&changeset, &all_changes);

		changeset.rollback_transaction();
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

		assert_changes(&changeset, &vec![
			(b"del1", (None, vec![3, 5])),
			(b"del2", (None, vec![4, 5])),
			(b"key0", (Some(b"val0"), vec![1])),
			(b"key1", (Some(b"val1"), vec![2])),
		]);

		changeset.rollback_transaction();

		assert_changes(&changeset, &vec![
			(b"del1", (Some(b"delval1"), vec![3])),
			(b"del2", (Some(b"delval2"), vec![4])),
			(b"key0", (Some(b"val0"), vec![1])),
			(b"key1", (Some(b"val1"), vec![2])),
		]);
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

		assert_eq!(changeset.next_change(b"key0").unwrap().0, b"key1");
		assert_eq!(changeset.next_change(b"key0").unwrap().1.value(), Some(&b"val1".to_vec()));
		assert_eq!(changeset.next_change(b"key1").unwrap().0, b"key11");
		assert_eq!(changeset.next_change(b"key1").unwrap().1.value(), Some(&b"val11".to_vec()));
		assert_eq!(changeset.next_change(b"key11").unwrap().0, b"key2");
		assert_eq!(changeset.next_change(b"key11").unwrap().1.value(), Some(&b"val2".to_vec()));
		assert_eq!(changeset.next_change(b"key2").unwrap().0, b"key3");
		assert_eq!(changeset.next_change(b"key2").unwrap().1.value(), Some(&b"val3".to_vec()));
		assert_eq!(changeset.next_change(b"key3").unwrap().0, b"key4");
		assert_eq!(changeset.next_change(b"key3").unwrap().1.value(), Some(&b"val4".to_vec()));
		assert_eq!(changeset.next_change(b"key4"), None);

		changeset.rollback_transaction();

		assert_eq!(changeset.next_change(b"key0").unwrap().0, b"key1");
		assert_eq!(changeset.next_change(b"key0").unwrap().1.value(), Some(&b"val1".to_vec()));
		assert_eq!(changeset.next_change(b"key1").unwrap().0, b"key2");
		assert_eq!(changeset.next_change(b"key1").unwrap().1.value(), Some(&b"val2".to_vec()));
		assert_eq!(changeset.next_change(b"key11").unwrap().0, b"key2");
		assert_eq!(changeset.next_change(b"key11").unwrap().1.value(), Some(&b"val2".to_vec()));
		assert_eq!(changeset.next_change(b"key2"), None);
		assert_eq!(changeset.next_change(b"key3"), None);
		assert_eq!(changeset.next_change(b"key4"), None);

	}

	#[test]
	#[should_panic]
	fn no_open_tx_commit_panics() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		changeset.commit_transaction();
	}

	#[test]
	#[should_panic]
	fn no_open_tx_rollback_panics() {
		let mut changeset = OverlayedChangeSet::default();
		assert_eq!(changeset.transaction_depth(), 0);
		changeset.rollback_transaction();
	}

	#[test]
	#[should_panic]
	fn unbalanced_transactions_panics() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		changeset.commit_transaction();
		changeset.commit_transaction();
	}

	#[test]
	#[should_panic]
	fn drain_with_open_transaction_panics() {
		let mut changeset = OverlayedChangeSet::default();
		changeset.start_transaction();
		let _ = changeset.drain_commited();
	}
}
