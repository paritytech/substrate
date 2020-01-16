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

//! Types and method for managing a stack of transactional values.


#[derive(Debug, Clone, Eq, PartialEq, Copy)]
/// State of a transactional layer.
pub(crate) enum TransactionState {
	/// Data is under change and can still be dropped.
	Pending,
	/// Same as pending but does count as a transaction start.
	TxPending,
	/// Data pointing to this indexed historic state should
	/// not be returned and can be removed.
	Dropped,
}

/// States for all past transaction layers.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct States {
	history: Vec<TransactionState>,
	// Keep track of the transaction positions.
	// This is redundant with `history`.
	// This is only use to precalculate the result
	// of a backward iteration to find the start
	// of a transactional window (function
	// `transaction_start_windows`).
	//
	// At many place we could use this instead
	// of the `TxPending` state, but `TxPending`
	// state is favored, except for `start_windows`
	// case.
	start_transaction_window: Vec<usize>,
	// commit is the position in history of the latest committed.
	commit: usize,
}

impl Default for States {
	fn default() -> Self {
		States {
			history: vec![TransactionState::Pending],
			start_transaction_window: vec![0],
			commit: 0,
		}
	}
}

impl States {
	/// Get reference of state, that is enough
	/// information to query historical
	/// data.
	pub(crate) fn as_ref(&self) -> &[TransactionState] {
		self.history.as_ref()
	}

	/// Current number of inner states.
	pub fn num_states(&self) -> usize {
		self.history.len()
	}

	/// Get index of committed layer.
	pub fn committed(&self) -> usize {
		self.commit
	}

	/// Allow to rollback to a previous committed
	/// index.
	/// This can only work if there was no eager
	/// garbage collection (eager collection can
	/// change interval between `old_committed` and
	/// `self.commit`).
	pub fn unchecked_rollback_committed(&mut self, old_committed: usize) {
		self.commit = old_committed;
		self.discard_prospective();
	}

	/// Build any state for testing only.
	#[cfg(test)]
	pub(crate) fn test_vector(
		history: Vec<TransactionState>,
		start_transaction_window: Vec<usize>,
		commit: usize,
	) -> Self {
		States { history, start_transaction_window, commit }
	}

	/// Discard prospective changes to state.
	/// That is revert all transaction up to the committed index.
	pub fn discard_prospective(&mut self) {
		for i in self.commit .. self.history.len() {
			self.history[i] = TransactionState::Dropped;
			self.start_transaction_window[i] = self.commit;
		}
		self.history.push(TransactionState::Pending);
		self.start_transaction_window.push(self.commit);
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		self.commit = self.history.len();
		self.history.push(TransactionState::Pending);
		for i in 0..self.history.len() - 1 {
			self.start_transaction_window[i] = self.commit;
		}
		self.start_transaction_window.push(self.commit);
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.start_transaction_window.push(self.history.len());
		self.history.push(TransactionState::TxPending);
	}

	/// Discard a transactional layer.
	/// A transaction is always running (history always end with pending).
	pub fn discard_transaction(&mut self) {
		let mut i = self.history.len();
		while i > self.commit {
			i -= 1;
			match self.history[i] {
				TransactionState::Dropped => (),
				TransactionState::Pending => {
					self.history[i] = TransactionState::Dropped;
				},
				TransactionState::TxPending => {
					self.history[i] = TransactionState::Dropped;
					break;
				},
			}
		}
		self.history.push(TransactionState::Pending);
		self.start_transaction_window.truncate(i);
		let previous = self.start_transaction_window.last()
			.cloned().unwrap_or(self.commit);
		self.start_transaction_window.resize(self.history.len(), previous);
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		let mut i = self.history.len();
		while i > self.commit {
			i -= 1;
			match self.history[i] {
				TransactionState::Pending
				| TransactionState::Dropped => (),
				TransactionState::TxPending => {
					self.history[i] = TransactionState::Pending;
					break;
				},
			}
		}
		self.history.push(TransactionState::Pending);
		self.start_transaction_window.truncate(i);
		let previous = self.start_transaction_window.last()
			.cloned().unwrap_or(self.commit);
		self.start_transaction_window.resize(self.history.len(), previous);
	}
}

#[inline]
/// Get previous index of pending state.
///
/// Used to say if it is possible to drop a committed transaction
/// state value.
/// Committed index is seen as a transaction state.
pub fn transaction_start_windows(states: &States, from: usize) -> usize {
	states.start_transaction_window[from]
}

/// Stack of values at different transactional layers.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Layers<V>(pub(crate) smallvec::SmallVec<[LayerEntry<V>; ALLOCATED_HISTORY]>);

#[cfg(test)]
/// Index of reserved layer for commited values.
pub(crate) const COMMITTED_LAYER: usize = 0;

/// Start transaction stack layer at a size of two,
/// to only allocate at first transaction (we always
/// have a fix committed layer).
const ALLOCATED_HISTORY: usize = 2;

impl<V> Default for Layers<V> {
	fn default() -> Self {
		Layers(Default::default())
	}
}

/// An value entry of a indexed transactional layer.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct LayerEntry<V> {
	/// The stored value.
	pub value: V,
	/// The transactional layer index.
	pub index: usize,
}

impl<V> From<(V, usize)> for LayerEntry<V> {
	fn from(input: (V, usize)) -> LayerEntry<V> {
		LayerEntry { value: input.0, index: input.1 }
	}
}

impl<V> LayerEntry<V> {
	fn as_ref(&self) -> LayerEntry<&V> {
		LayerEntry { value: &self.value, index: self.index }
	}
}

impl<V> Layers<V> {
	fn remove_until(&mut self, index: usize) {
		if index > 0 {
			if self.0.spilled() {
				let owned = std::mem::replace(&mut self.0, Default::default());
				self.0 = smallvec::SmallVec::from_vec(owned.into_vec().split_off(index));
			} else {
				for i in (0..index).rev() {
					self.0.remove(i);
				}
			}
		}
	}

	fn get_pending_unchecked(
		&self,
		states: &[TransactionState],
		history_index: usize,
	)	-> Option<LayerEntry<&V>> {
		let LayerEntry { value, index } = self.0[history_index].as_ref();
		match states[index] {
			TransactionState::Dropped => (),
			TransactionState::Pending
			| TransactionState::TxPending =>
				return Some(LayerEntry { value, index }),
		}
		None
	}

	/// Push a value without checking without transactional layer
	/// consistency.
	pub(crate) fn push_unchecked(&mut self, item: LayerEntry<V>) {
		self.0.push(item);
	}

	/// Access to the latest pending value (non dropped state).
	/// When possible please prefer `get_mut` as it can free
	/// some memory.
	/// If tail freeing is needed, the function also return true
	/// (this indicates the operation run suboptimally and could
	/// in certain condition leads to bad complexity).
	pub(crate) fn get(&self, states: &[TransactionState]) -> (Option<&V>, bool) {
		let self_len = self.0.len();
		if self_len == 0 {
			return (None, false);
		}
		debug_assert!(states.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states, index) {
				return (Some(h.value), index != self_len - 1);
			}
		}
		(None, true)
	}

	/// Access to latest pending value (non dropped state).
	///
	/// This method removes latest dropped and merged values,
	/// only keeping the latest valid value.
	///
	/// Returns mutable latest pending value.
	pub(crate) fn get_mut(
		&mut self,
		states: &States,
	) -> Option<LayerEntry<&mut V>> {
		let self_len = self.0.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.history.len() >= self_len);
		let mut result = None;
		let mut start_transaction_window = usize::max_value();
		let mut previous_switch = None;
		for index in (0 .. self_len).rev() {
			let state_index = self.0[index].index;
			match states.history[state_index] {
				TransactionState::TxPending => {
					if state_index >= start_transaction_window {
						previous_switch = Some(index);
					} else {
						if result.is_none() {
							result = Some((index, state_index));
						}
					}
					break;
				},
				TransactionState::Pending => {
					if state_index >= start_transaction_window {
						previous_switch = Some(index);
					} else {
						if result.is_none() {
							result = Some((index, state_index));
							start_transaction_window = transaction_start_windows(states, state_index);
						} else {
							break;
						}
					}
				},
				TransactionState::Dropped => (),
			}
		}
		self.drop_last_values(result, previous_switch, 0)
	}

	/// Method to prune regarding a full state.
	/// It also returns the last value as mutable.
	/// Internally it acts like `get_mut` with an
	/// additional cleaning capacity to clean committed
	/// state if `prune_to_commit` is set to true.
	pub(crate) fn get_mut_pruning(
		&mut self,
		states: &States,
		prune_to_commit: bool,
	) -> Option<LayerEntry<&mut V>> {
		let self_len = self.0.len();
		if self_len == 0 {
			return None;
		}
		let mut prune_index = 0;
		debug_assert!(states.history.len() >= self_len);
		let mut result = None;
		let mut start_transaction_window = usize::max_value();
		let mut previous_switch = None;
		for index in (0 .. self_len).rev() {
			let state_index = self.0[index].index;
			match states.history[state_index] {
				state @ TransactionState::TxPending
				| state @ TransactionState::Pending => {
					if state_index < states.commit && index > prune_index {
						prune_index = index;
					}

					if state_index >= start_transaction_window {
						previous_switch = Some(index);
					} else {
						if result.is_none() {
							result = Some((index, state_index));
							if state == TransactionState::Pending {
								start_transaction_window = transaction_start_windows(states, state_index);
							}
						} else {
							if prune_to_commit {
								if state_index < states.commit {
									break;
								}
							} else {
								break;
							}
						}
					}
				},
				TransactionState::Dropped => (),
			}
		}
		let deleted = if prune_to_commit && prune_index > 0 && result.is_some() {
			self.remove_until(prune_index);
			prune_index
		} else {
			0
		};
		self.drop_last_values(result, previous_switch, deleted)
	}

	// Function used to remove all last values for `get_mut` and
	// `get_mut_pruning`.
	//
	// It expects the `result` of the iteration that lookup
	// for the latest non dropped value (coupled with its state
	// index). That is to remove terminal dropped states.
	//
	// It also does remove values on committed state that are
	// not needed (before another committed value).
	// `previous_switch` is the index to the first unneeded value.
	//
	// An index offset is here in case some content was `deleted` before
	// this function call.
	fn drop_last_values(
		&mut self,
		result: Option<(usize, usize)>,
		previous_switch: Option<usize>,
		deleted: usize,
	) -> Option<LayerEntry<&mut V>> {
		if let Some((index, state_index)) = result {
			if index + 1 - deleted < self.0.len() {
				self.0.truncate(index + 1 - deleted);
			}
			if let Some(switch_index) = previous_switch {
				if let Some(mut value) = self.0.pop() {
					self.0.truncate(switch_index - deleted);
					value.index = state_index;
					self.push_unchecked(value);
				}
				Some((&mut self.0[switch_index - deleted].value, state_index).into())
			} else {
				Some((&mut self.0[index - deleted].value, state_index).into())
			}
		} else {
			self.0.clear();
			None
		}
	}

	/// Set a value, it uses a state history as parameter.
	///
	/// This method uses `get_mut` and does remove pending
	/// dropped value.
	pub(crate) fn set(&mut self, states: &States, value: V) {
		let last_state_index = states.num_states() - 1;
		if let Some(v) = self.get_mut(states) {
			if v.index == last_state_index {
				*v.value = value;
				return;
			}
			debug_assert!(v.index < last_state_index, "Layers expects \
				only new values at the latest state");
		}
		self.push_unchecked(LayerEntry {
			value,
			index: last_state_index,
		});
	}

	/// Extracts the committed value if there is one.
	pub fn into_committed(mut self, states: &[TransactionState], committed: usize) -> Option<V> {
		let self_len = self.0.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states, index) {
				if h.index < committed {
						self.0.truncate(index + 1);
						return self.0.pop().map(|v| v.value);
				}
			}
		}
		None
	}
}

#[cfg(test)]
impl<V> Layers<V> {
	/// Create an history from a sequence of historical values.
	pub fn from_iter(input: impl IntoIterator<Item = LayerEntry<V>>) -> Self {
		let mut history = Layers::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	/// Get latest prospective value, excludes
	/// committed values.
	pub(crate) fn get_prospective(&self, states: &States) -> Option<&V> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.history.len() >= self_len);
		for index in (states.commit .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states.history.as_ref(), index) {
				return Some(h.value);
			}
		}
		None
	}

	/// Get latest committed value.
	pub(crate) fn get_committed(&self, states: &States) -> Option<&V> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.history.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states.history.as_ref(), index) {
				if h.index < states.commit {
					return Some(h.value);
				}
			}
		}
		None
	}
}


/// A default sample configuration to manage garbage collection
/// triggering.
pub(crate) const DEFAULT_GC_CONF: GCConfiguration = GCConfiguration {
	trigger_transaction_gc: 1_000_000,
	trigger_commit_gc: 100_000,
	add_content_size_unit: 64,
};

/// Garbage collection configuration.
/// It is designed to listen on two different operation, transaction
/// and commit.
/// It match transcational semantic with transaction for transaction
/// operation and commit for prospective operation.
/// Considering transaction can be manipulated in extrinsic, this option
/// is quite unsafe and shoudl be use with care (the default value is
/// explicitelly very high).
/// More generally it should be very unlikelly that gc is needed
/// during a block processing for most use case.
///
/// This is not a very good measurement and should be replace by
/// heap measurement or other metrics, at this point the gc even
/// if tested should not be required.
pub(crate) struct GCConfiguration {
	/// Treshold in number of operation before running a garbage collection.
	///
	/// Should be same as `TRIGGER_COMMIT_GC` or higher
	/// (we most likely do not want lower as transaction are
	/// possibly more frequent than commit).
	pub trigger_transaction_gc: usize,

	/// Treshold in number of operation before running a garbage colletion
	/// on a commit operation.
	///
	/// We may want a lower value than for a transaction, even
	/// a 1 if we want to do it between every operation.
	pub trigger_commit_gc: usize,

	/// Used to count big content as multiple operations.
	/// This is a number of octet.
	/// Set to 0 to ignore.
	pub add_content_size_unit: usize,
}

impl GCConfiguration {
	/// Cost depending on value if any.
	pub fn operation_cost(&self, val: Option<&Vec<u8>>) -> usize {
		let additional_cost = if self.add_content_size_unit > 0 {
			if let Some(s) = val.as_ref() {
				s.len() / self.add_content_size_unit
			} else {
				0
			}
		} else { 0 };
		1 + additional_cost
	}

}
/// Base code for fuzzing.
#[cfg(any(test, feature = "test-helpers"))]
pub mod fuzz {
	use crate::overlayed_changes::OverlayedChanges;
	use std::collections::HashMap;
	use super::Layers;

	/// Size of key, max 255
	const KEY_SPACE: u8 = 20;

	/// Size of key, max 255
	const VALUE_SPACE: u8 = 50;

	impl<V> Layers<V> {
		/// Get current number of stored historical values.
		pub fn len(&self) -> usize {
			self.0.len()
		}
	}

	/// Fuzz input against a stack of hash map reference implementation.
	/// `check_compactness` add a check in the number of stored entry.
	pub fn fuzz_transactions_inner(input: &[u8], check_compactness: bool) {
		let mut input_index: usize = 0;
		let mut overlayed = OverlayedChanges::default();
		let mut ref_overlayed = RefOverlayedChanges::default();

		let mut actions = Vec::new();
		let mut values = Vec::new();
		loop {
			let action: Actions = if let Some(v) = input.get(input_index) {
				input_index += 1;
				(*v).into()
			} else { break };

			actions.push(action);
			match action {
				Actions::CommitProspective => {
					overlayed.commit_prospective();
					ref_overlayed.commit_prospective();
				},
				Actions::DropProspective => {
					overlayed.discard_prospective();
					ref_overlayed.discard_prospective();
				},
				Actions::NewTransaction => {
					overlayed.start_transaction();
					ref_overlayed.start_transaction();
				},
				Actions::CommitTransaction => {
					overlayed.commit_transaction();
					ref_overlayed.commit_transaction();
				},
				Actions::DropTransaction => {
					overlayed.discard_transaction();
					ref_overlayed.discard_transaction();
				},
				Actions::Insert => {
					let key = if let Some(v) = input.get(input_index) {
						input_index += 1;
						v % KEY_SPACE
					} else { break };
					let value = if let Some(v) = input.get(input_index) {
						input_index += 1;
						v % VALUE_SPACE
					} else { break };
					values.push((key, value));
					overlayed.set_storage(vec![key], Some(vec![value]));
					ref_overlayed.set_storage(vec![key], Some(vec![value]));
				}
			}

		}

		let mut success = true;

		let (check_value, len) = check_values(&overlayed, &ref_overlayed);
		success &= check_value;

		if check_compactness {
			let reference_size = ref_overlayed.total_length();
			overlayed.gc(true);
			let size = overlayed.top_count_keyvalue_pair();
			if reference_size != size {
				println!("inconsistent gc {} {}", size, reference_size);
				success = false;
			}
			let (check_value, len_compactness) = check_values(&overlayed, &ref_overlayed);
			success &= check_value;
			success &= len_compactness == len;
		}
		ref_overlayed.commit_prospective();
		let ref_len = ref_overlayed.committed.len();
		if len != ref_len {
			println!("inconsistent length {} {}", len, ref_len);
			success = false;
		}
		if !success {
			println!("fuzzing: \n {:x?}", (&actions, &values));
			println!("input: \n {:?}", &input);
		}

		assert!(success);
	}

	fn check_values(overlayed: &OverlayedChanges, ref_overlayed: &RefOverlayedChanges) -> (bool, usize) {
		let mut len = 0;
		let mut success = true;
		for (key, value) in overlayed.iter_values(None) {
			let ref_value = ref_overlayed.storage(key);
			if Some(value) != ref_value {
				println!("at {:x?} different values {:x?} {:x?}", key, Some(value), ref_value);
				success = false;
			}
			len += 1;
		}
		(success, len)
	}

	#[derive(Clone, Copy, Debug)]
	enum Actions {
		Insert,
		// Delete, same as an insert do not test.
		CommitProspective,
		DropProspective,
		NewTransaction,
		CommitTransaction,
		DropTransaction,
	}

	impl From<u8> for Actions {
		fn from(v: u8) -> Self {
			match (v as usize) * 100 / 255 {
				v if v <= 5 => Actions::CommitProspective,
				v if v <= 10 => Actions::DropProspective,
				v if v <= 20 => Actions::NewTransaction,
				v if v <= 30 => Actions::CommitTransaction,
				v if v <= 40 => Actions::DropTransaction,
				_ => Actions::Insert,
			}
		}
	}

	/// A simple implementation of overlayed change
	/// to use as a comparision.
	/// It is partly incomplete (no child trie support, no change trie).
	#[derive(Debug, Clone, Default)]
	struct RefOverlayedChanges {
		committed: HashMap<Vec<u8>, Vec<u8>>,
		prospective: HashMap<Vec<u8>, Vec<u8>>,
		transactions: Vec<HashMap<Vec<u8>, Vec<u8>>>,
	}

	impl RefOverlayedChanges {
		fn discard_prospective(&mut self) {
			self.transactions.clear();
			self.prospective.clear();
		}

		fn commit_prospective(&mut self) {
			for _ in 0 .. self.transactions.len() {
				self.commit_transaction();
			}
			self.committed.extend(self.prospective.drain());
		}

		fn start_transaction(&mut self) {
			self.transactions.push(Default::default());
		}

		fn discard_transaction(&mut self) {
			if self.transactions.len() == 0 {
				// clear prospective on no transaction started.
				self.prospective.clear();
			} else {
				let _ = self.transactions.pop();
			}
		}

		/// Commit a transactional layer.
		fn commit_transaction(&mut self) {
			match self.transactions.len() {
				0 => (),
				1 => self.prospective.extend(
					self.transactions.pop().expect("length just checked").into_iter()
				),
				_ => {
					let t = self.transactions.pop().expect("length just checked");
					self.transactions.last_mut().expect("length just checked")
						.extend(t.into_iter());
				}
			}
		}

		fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
			if self.transactions.len() > 0 {
				self.transactions.last_mut().expect("length just checked")
					.insert(key, val.expect("fuzzer do not delete"));
			} else {
				self.prospective.insert(key, val.expect("fuzzer do not delete"));
			}
		}

		fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
			for t in self.transactions.iter().rev() {
				if let Some(v) = t.get(key) {
					return Some(Some(v));
				}
			}
			if let Some(v) = self.prospective.get(key) {
				return Some(Some(v));
			}
			if let Some(v) = self.committed.get(key) {
				return Some(Some(v));
			}
			None
		}

		fn total_length(&self) -> usize {
			let tr_len: usize = self.transactions.iter()
				.map(|l| l.len()).sum();
			self.committed.len() + self.prospective.len() + tr_len
		}
	}

	// Those are samples which found error during fuzzing.
	// They are kept as a low cust rust test for non regression purpose.
	#[test]
	fn previous_fuzzed_error() {
		let inputs = [
			vec![0x2,0xee,0xee,0x12,0x2,0x16,0x67,0xee,0xee,0xee,],
			vec![50, 208, 50, 38, 46, 58, 209, 50, 216, 255, 255],
			vec![0x98,0x98,0xf6,0x12,0xee,0x98,0xf9,],
			vec![0xf1,0x0,0x0,0x1,0x38,0xb2,0x0,0x67,],
			vec![238, 0, 36, 43, 50, 46, 38, 211, 0, 0, 61],
			vec![50, 255, 38, 38, 186, 35, 46, 43, 46, 35, 255, 255, 102, 67],
			vec![0x6e, 0xff, 0xf7, 0x0, 0x6e, 0xff, 0xff, 0x2d, 0xff, 0xff, 0xff, 0xe],
			vec![0x2e,0x6e,0x22,0x32,0x2e,0x6e,0x22,0x32,0x3f,0x2e,],
			vec![0xd9,0xff,0xfd,0x0,0xff,0xff,0xf8,0x1,0x92,0xff,0xbf,0x14,],
			vec![0xef,0xdf,0xc1,0x0,0xc1,0xdf,0xc1,0x2b,0xf3,0xf3,0xb0,0x18,
				0xef,0xdf,0x2e,0x3a,0xef,0xdf,0x0,0xc1,0xf3,0x30,0x18,0xef,0xdf,
				0xc1,0x2b,0xf3,0xf3,0x30,0x17,0x0,0xdf,],
		];
		for input in inputs.iter() {
			fuzz_transactions_inner(&input[..], true);
		}
	}
}
