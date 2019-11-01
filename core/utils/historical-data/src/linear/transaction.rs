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

//! Transactional layer implementation.
//! 
//! General principle of historical data (see module design)applies here.
//! Therefore we got a state and values with an history dependant on
//! a state.
//!
//! This module is defining a linear transactional state.
//!
//! ## state operation
//!
//! The state history contains multiple possible states `TransactionStates` and
//! a committed index.
//!
//! There is two pending state, both indicate a valid value, but on also indicate
//! the start of a transactional window.
//! Dropping a transaction just invalidate all state from the start of the last
//! transactional window.
//! Committing a transaction fused it transaction window with the previous transaction
//! window (changing a `TxPending` with a `Pending` state).
//!
//! The committed index is lie a upper transaction state and is considered as the start
//! of a transaction, but cannot be dropped with the same operation.
//! If dropped, all state after this index are dropped.
//! If committed its index is updated and all state prior cannot be dropped.
//!
//! ## value operation
//!
//! Here access to latest state value is a reverse iteration over history of value and
//! matching state, up to the first pending state.
//!
//! On mutable access, terminal dropped state or unneeded state values (values in a same
//! transactional window) are dropped.
//! This allows a clean state up to the latest transactional window at a small cost.
//! 
//! ** Update only occurs on a latest state **, therefore state primitives should not allow
//! access to some subset of the state (full state is used as parameter when for query a simple
//! slice is used).
//!
//! # Usage
//!
//! All the primitives for a value expect a reference to the state used to build 
//! the value. ** Wrong state usage results in undefined behavior. **


use rstd::vec::Vec;
use rstd::vec;
use crate::linear::{HistoricalValue, History};

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

/// States is both an indexed state to query values with history
/// and a committed index that indicates a point in time where
/// we cannot drop transaction layer.
/// Committed index is starting at 1, if it is 0 then there is no
/// committed index and all layer can be dropped.
/// There is a implicit pending state which is equal to the length
/// of this history.
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
	pub fn as_ref(&self) -> &[TransactionState] {
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
	/// garbage collection.
	pub fn unchecked_rollback_committed(&mut self, old_committed: usize) {
		self.commit = old_committed;
		self.discard_prospective();
	}

	/// Build any state for testing only.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn test_vector(
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

impl<V> History<V> {
	fn get_pending_unchecked(&self, states: &[TransactionState], history_index: usize)
		-> Option<HistoricalValue<&V>> {
		let HistoricalValue { value, index } = self.get_unchecked(history_index);
		match states[index] {
			TransactionState::Dropped => (),
			TransactionState::Pending
			| TransactionState::TxPending =>
				return Some(HistoricalValue { value, index }),
		}
		None
	}

	/// Set a value, it uses a state history as parameter.
	///
	/// This method uses `get_mut` and does remove pending
	/// dropped value.
	pub fn set(&mut self, states: &States, value: V) {
		let last_state_index = states.num_states() - 1;
		if let Some(v) = self.get_mut(states) {
			if v.index == last_state_index {
				*v.value = value;
				return;
			}
			debug_assert!(v.index < last_state_index, "History expects \
				only new values at the latest state");
		}
		self.push_unchecked(HistoricalValue {
			value,
			index: last_state_index,
		});
	}

	/// Access to the latest pending value (non dropped state).
	/// When possible please prefer `get_mut` as it can free
	/// some memory.
	pub fn get(&self, states: &[TransactionState]) -> Option<&V> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states, index) {
				return Some(h.value);
			}
		}
		None
	}

	/// Get latest value, consuming the historical data.
	pub fn into_pending(mut self, states: &[TransactionState]) -> Option<V> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if self.get_pending_unchecked(states, index).is_some() {
				self.truncate(index + 1);
				return self.pop().map(|v| v.value);
			}
		}
		None
	}


	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_prospective(&self, states: &States) -> Option<&V> {
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

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_committed(&self, states: &States) -> Option<&V> {
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

	pub fn into_committed(mut self, states: &[TransactionState], committed: usize) -> Option<V> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.len() >= self_len);
		for index in (0 .. self_len).rev() {
			if let Some(h) = self.get_pending_unchecked(states, index) {
				if h.index < committed {
						self.truncate(index + 1);
						return self.pop().map(|v| v.value);
				}
			}
		}
		None
	}

	/// Access to latest pending value (non dropped state).
	///
	/// This method removes latest dropped and merged values,
	/// only keeping the latest valid value.
	///
	/// Returns mutable latest pending value.
	pub fn get_mut(
		&mut self,
		states: &States,
	) -> Option<HistoricalValue<&mut V>> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		debug_assert!(states.history.len() >= self_len);
		let mut result = None;
		let mut start_transaction_window = usize::max_value();
		let mut previous_switch = None;
		for index in (0 .. self_len).rev() {
			let state_index = self.get_unchecked(index).index;
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
	pub fn get_mut_pruning(
		&mut self,
		states: &States,
		prune_to_commit: bool,
	) -> Option<HistoricalValue<&mut V>> {
		let self_len = self.len();
		if self_len == 0 {
			return None;
		}
		let mut prune_index = 0;
		debug_assert!(states.history.len() >= self_len);
		let mut result = None;
		let mut start_transaction_window = usize::max_value();
		let mut previous_switch = None;
		for index in (0 .. self_len).rev() {
			let state_index = self.get_unchecked(index).index;
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
	) -> Option<HistoricalValue<&mut V>> {
		if let Some((index, state_index)) = result {
			if index + 1 - deleted < self.len() {
				self.truncate(index + 1 - deleted);
			}
			if let Some(switch_index) = previous_switch {
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
