// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Transactional overlay implementation.
//!
//! This follows a linear succession of states.
//! This contains multiple unbounded transaction layer
//! and an additional top level 'prospective' layer.
//! It only allows linear history (no branch so
//! inner storage is only an array of element).

use rstd::vec::Vec;
use rstd::vec;

#[derive(Debug, Clone, Eq, PartialEq, Copy)]
/// State of a transactional layer.
pub enum TransactionState {
	/// Data is under change and can still be dropped.
	Pending,
	/// Same as pending but does count as a transaction start.
	TxPending,
	/// Data pointing to this indexed historic state should
	/// not be returned and can be removed.
	Dropped,
}


/// An entry at a given history height.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct HistoricalValue<V> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: usize,
}

impl<V> From<(V, usize)> for HistoricalValue<V> {
	fn from(input: (V, usize)) -> HistoricalValue<V> {
		HistoricalValue { value: input.0, index: input.1 }
	}
}

impl<V> HistoricalValue<V> {
	fn as_ref(&self) -> HistoricalValue<&V> {
		HistoricalValue {
			value: &self.value,
			index: self.index,
		}
	}
}

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
type MemoryOnly<V> = smallvec::SmallVec<[HistoricalValue<V>; ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
const ALLOCATED_HISTORY: usize = 2;

/// History of value that are related to a state history (eg field `history` of
/// an `OverlayedChangeSet`).
///
/// Values are always paired with a state history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct History<V>(MemoryOnly<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Default::default())
	}
}

// Following implementation are here to isolate
// buffer specific functions.
impl<V> History<V> {

	fn get_state(&self, index: usize) -> HistoricalValue<&V> {
		self.0[index].as_ref()
	}

	#[cfg(any(test, feature = "test-helpers"))]
	/// Create an history from an existing history.
	pub fn from_iter(input: impl IntoIterator<Item = HistoricalValue<V>>) -> Self {
		let mut history = History::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	/// Current number of inner states.
	pub fn len(&self) -> usize {
		self.0.len()
	}

	fn truncate(&mut self, index: usize) {
		self.0.truncate(index)
	}

	fn truncate_until(&mut self, index: usize) {
		if index > 0 {
			if self.0.spilled() {
				let owned = rstd::mem::replace(&mut self.0, Default::default());
				self.0 = smallvec::SmallVec::from_vec(owned.into_vec().split_off(index));
			} else {
				for i in (0..index).rev() {
					self.0.remove(i);
				}
			}
		}
	}

	fn pop(&mut self) -> Option<HistoricalValue<V>> {
		self.0.pop()
	}

	/// Append without checking if a value already exist.
	/// If a value already exists, the history will be broken.
	/// This method shall only be call after a `get_mut` where
	/// the returned index indicate that a `set` will result
	/// in appending a value.
	pub fn push_unchecked(&mut self, value: HistoricalValue<V>) {
		self.0.push(value)
	}

	fn mut_ref(&mut self, index: usize) -> &mut V {
		&mut self.0[index].value
	}

}


/// States is both an indexed state to query values with history
/// and a committed index that indicates a point in time where
/// we cannot drop transaction layer.
/// Committed index is starting at 1, if it is 0 then there is no
/// committed index and all layer can be dropped.
/// There is a implicit pending state which is equal to the length
/// of this history.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct States(Vec<TransactionState>, usize);

impl Default for States {
	fn default() -> Self {
		States(vec![TransactionState::Pending], 0)
	}
}

impl States {
	/// Get reference of state, that is enough
	/// information to query historical
	/// data.
	pub fn as_ref(&self) -> &[TransactionState] {
		self.0.as_ref()
	}

	/// Current number of inner states.
	pub fn len(&self) -> usize {
		self.0.len()
	}

	/// Get index of committed layer, this is
	/// additional information needed to manage
	/// commit and garbage collect.
	pub fn committed(&self) -> usize {
		self.1
	}

	/// Allow to rollback to a previous committed
	/// index.
	/// This can only work if there was no eager
	/// garbage collection.
	pub fn unchecked_rollback_committed(&mut self, old_committed: usize) {
		self.1 = old_committed;
		self.discard_prospective();
	}

	/// Build any state for testing only.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn test_vector(test_states: Vec<TransactionState>, committed: usize) -> Self {
		States(test_states, committed)
	}

	/// Discard prospective changes to state.
	/// That is revert all transaction up to the committed index.
	pub fn discard_prospective(&mut self) {
		for i in self.1 .. self.0.len() {
			self.0[i] = TransactionState::Dropped;
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		self.1 = self.0.len();
		self.0.push(TransactionState::Pending);
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.0.push(TransactionState::TxPending);
	}

	/// Discard a transactional layer.
	/// A transaction is always running (history always end with pending).
	pub fn discard_transaction(&mut self) {
		let mut i = self.0.len();
		while i > self.1 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Pending => {
					self.0[i] = TransactionState::Dropped;
				},
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Dropped;
					break;
				},
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		let mut i = self.0.len();
		while i > self.1 {
			i -= 1;
			match self.0[i] {
				TransactionState::Pending
				| TransactionState::Dropped => (),
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Pending;
					break;
				},
			}
		}
		self.0.push(TransactionState::Pending);
	}

}

/// Get previous index of pending state.
/// Used to say if it is possible to drop a committed transaction
/// state value.
/// Committed index is seen as a transaction state.
pub fn find_previous_tx_start(states: &States, from: usize) -> usize {
	for i in (states.1 .. from).rev() {
		match states.0[i] {
			TransactionState::TxPending => {
				return i;
			},
			_ => (),
		}
	}
	states.1
}



impl<V> History<V> {
	/// Set a value, it uses a state history as parameter.
	/// This method uses `get_mut` and do remove pending
	/// dropped value.
	pub fn set(&mut self, states: &States, value: V) {
		if let Some(v) = self.get_mut(states) {
			if v.index == states.0.len() - 1 {
				*v.value = value;
				return;
			}
		}
		self.push_unchecked(HistoricalValue {
			value,
			index: states.0.len() - 1,
		});
	}

	/// Access to latest pending value (non dropped state).
	/// When possible please prefer `get_mut` as it can free
	/// some memory.
	pub fn get(&self, states: &[TransactionState]) -> Option<&V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoricalValue { value, index: state_index } = self.get_state(index);
			match states[state_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending =>
					return Some(value),
			}
		}
		None
	}

	/// Get latest value, consuming the historical data.
	pub fn into_pending(mut self, states: &[TransactionState]) -> Option<V> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.len() >= index);
		while index > 0 {
			index -= 1;
			let state_index = self.get_state(index).index;
			match states[state_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.value);
				},
			}
		}
		None
	}


	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_prospective(&self, states: &States) -> Option<&V> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.0.len() >= index);
		while index > states.1 {
			index -= 1;
			let HistoricalValue { value, index: state_index } = self.get_state(index);
			match states.0[state_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending =>
					return Some(value),
			}
		}
		None
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_committed(&self, states: &States) -> Option<&V> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.0.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoricalValue { value, index: state_index } = self.get_state(index);
			if state_index < states.1 {
				match states.0[state_index] {
					TransactionState::Dropped => (),
					TransactionState::Pending
					| TransactionState::TxPending =>
						return Some(value),
				}
			}
		}
		None
	}

	pub fn into_committed(mut self, states: &[TransactionState], committed: usize) -> Option<V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.len() >= index);
		while index > 0 {
			index -= 1;
			let state_index = self.get_state(index).index;
			if state_index < committed {
				match states[state_index] {
					TransactionState::Dropped => (),
					TransactionState::Pending
					| TransactionState::TxPending => {
						self.truncate(index + 1);
						return self.pop().map(|v| v.value);
					},
				}
			}
		}
		None
	}

	/// Access to latest pending value (non dropped state).
	///
	/// This method removes latest dropped values up to the latest valid value.
	pub fn get_mut(
		&mut self,
		states: &States,
	) -> Option<HistoricalValue<&mut V>> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(states.0.len() >= index);
		let mut result = None;
		let mut previous_transaction = usize::max_value();
		let mut previous_switch = None;
		while index > 0 {
			index -= 1;
			let state_index = self.get_state(index).index;
			match states.0[state_index] {
				TransactionState::TxPending => {
					if state_index >= previous_transaction {
						previous_switch = Some((index, state_index));
					} else {
						if result.is_none() {
							result = Some((index, state_index));
						}
					}
					break;
				},
				TransactionState::Pending => {
					if state_index >= previous_transaction {
						previous_switch = Some((index, state_index));
					} else {
						if result.is_none() {
							result = Some((index, state_index));
							previous_transaction = find_previous_tx_start(states, state_index);
						} else {
							break;
						}
					}
				},
				TransactionState::Dropped => (),
			}
		}
		self.clear_terminal_values(result, previous_switch, 0)
	}


	/// Method to prune regarding a full state.
	/// It also returns the last value as mutable.
	/// Internally it acts like `get_mut` with an
	/// additional cleaning capacity to clean committed
	/// state if `prune_to_commit` is set to true.
	pub fn get_mut_pruning(
		&mut self,
		states: &States,
		prune_to_commit: bool,
	) -> Option<HistoricalValue<&mut V>>  {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		let mut prune_index = 0;
		debug_assert!(states.0.len() >= index);
		let mut result = None;
		let mut previous_transaction = usize::max_value();
		let mut previous_switch = None;
		while index > 0 {
			index -= 1;
			let state_index = self.get_state(index).index;
			match states.0[state_index] {
				state @ TransactionState::TxPending
				| state @ TransactionState::Pending => {
					if state_index < states.1 && index > prune_index {
						prune_index = index;
					}

					if state_index >= previous_transaction {
						previous_switch = Some((index, state_index));
					} else {
						if result.is_none() {
							result = Some((index, state_index));
							if state == TransactionState::Pending {
								previous_transaction = find_previous_tx_start(states, state_index);
							}
						} else {
							if prune_to_commit {
								if state_index < states.1 {
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
			self.truncate_until(prune_index);
			prune_index
		} else {
			0
		};
		self.clear_terminal_values(result, previous_switch, deleted)
	}

	#[inline]
	fn clear_terminal_values(
		&mut self,
		result: Option<(usize, usize)>,
		previous_switch: Option<(usize, usize)>,
		deleted: usize,
	) -> Option<HistoricalValue<&mut V>>  {
		if let Some((index, state_index)) = result {
			if index + 1 - deleted < self.len() {
				self.truncate(index + 1 - deleted);
			}
			if let Some((switch_index, state_index)) = previous_switch {
				if let Some(mut value) = self.pop() {
					self.truncate(switch_index - deleted);
					value.index = state_index;
					self.push_unchecked(value);
				}
				Some((self.mut_ref(switch_index - deleted), state_index).into())
			} else {
				Some((self.mut_ref(index - deleted), state_index).into())
			}
		} else {
			self.0.clear();
			None
		}
	}
}
