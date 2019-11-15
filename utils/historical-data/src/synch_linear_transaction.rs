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

//! Linear arrangement of historical data with transactional
//! support.
//!
//!
//! Described as a synchronized module as it contains historical
//! data that do not require a separated state for most operation.
//! Global state operation must therefore apply on all local values
//! with history synchronously.
//!
//! # Global state
//!
//! The only global state is a counter of overlayed transaction layer.
//! Committing or discarding a layer must use this counter.
//!
//! # Local state
//!
//! Local state is either a committed state (this is a single first independant level
//! of transaction) or a reference to the transaction counter in use in time of creation.

use crate::CleaningResult;

/// Global state is a simple counter to the current overlay layer index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States { current_layer: usize }

impl Default for States {
	fn default() -> Self {
		// we default to 1 to be able to discard this transaction.
		States { current_layer: 1 }
	}
}

impl States {

	/// Get corresponding current state.
	pub fn as_state(&self) -> State {
		State::Transaction(self.current_layer)
	}

	/// Build any state for testing only.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn test_state(
		current_layer: usize,
	) -> Self {
		States { current_layer }
	}

	/// By default the current transaction is at least 1.
	/// 0 can be use only to apply transaction change, in
	/// this case transaction need to be restored to a valid
	/// state afterward.
	pub fn finalize_discard(&mut self) {
		if self.current_layer == 0 {
			self.current_layer = 1;
		}
	}

	/// Discard prospective changes to state.
	/// It does not revert actual values.
	/// A subsequent update of all related stored history is needed.
	pub fn discard_prospective(&mut self) {
		self.current_layer = 1;
	}

	/// After a prospective was discarded, clear prospective history. 
	pub fn apply_discard_prospective<V>(value: &mut History<V>) -> CleaningResult {
		if value.0.len() == 0 {
			return CleaningResult::Cleared;
		}
		if value.0[0].index == State::Committed {
			if value.0.len() == 1 {
				return CleaningResult::Unchanged;
			}
			value.0.truncate(1);
		} else {
			value.0.clear();
		}
		CleaningResult::Changed
	}

	/// Commit prospective changes to state.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_prospective(&mut self) {
		self.current_layer = 1;
	}

	/// After a prospective was committed, commit pending value and clear existing history.
	pub fn apply_commit_prospective<V>(value: &mut History<V>) -> CleaningResult {
		if value.0.len() == 0 {
			return CleaningResult::Cleared;
		}
		if value.0.len() == 1 {
			if value.0[0].index != State::Committed {
				value.0[0].index = State::Committed;
			} else {
				return CleaningResult::Unchanged;
			}
		} else if let Some(mut v) = value.0.pop() {
			v.index = State::Committed;
			value.0.clear();
			value.0.push(v);
		}
		CleaningResult::Changed
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.current_layer += 1;
	}

	/// Discard a transactional layer.
	/// It does not revert actual values.
	/// A subsequent update of all related stored history is needed.
	pub fn discard_transaction(&mut self) {
		if self.current_layer > 0 {
			self.current_layer -= 1;
		}
	}

	/// Update a value to previous transaction.
	/// Multiple discard can be applied at the same time.
	pub fn apply_discard_transaction<V>(&self, value: &mut History<V>) -> CleaningResult {
		let init_len = value.0.len();
		for i in (0 .. value.0.len()).rev() {
			if let HistoricalValue {
				value: _,
				index: State::Transaction(ix),
			} = value.0[i] {
				if ix > self.current_layer {
					let _ = value.0.pop();
				} else { break }
			} else { break }
		}
		if value.0.len() == 0 {
			CleaningResult::Cleared
		} else if value.0.len() != init_len {
			CleaningResult::Changed
		} else {
			CleaningResult::Unchanged
		}
	}

	/// Discard a transactional layer.
	/// It does not revert actual values.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_transaction(&mut self) {
		if self.current_layer > 1 {
			self.current_layer -= 1;
		}
	}

	/// Update a value to be the best historical value
	/// after one or more `commit_transaction` calls.
	/// Multiple discard can be applied at the same time.
	pub fn apply_commit_transaction<V>(&self, value: &mut History<V>) -> CleaningResult {
		let mut new_value = None;
		for i in (0 .. value.0.len()).rev() {
			if let HistoricalValue {
				value: _,
				index: State::Transaction(ix),
			} = value.0[i] {
				if ix > self.current_layer {
					if let Some(v) = value.0.pop() {
						if new_value.is_none() {
							new_value = Some(v.value);
						}
					}
				} else if ix == self.current_layer && new_value.is_some() {
					let _ = value.0.pop();
				} else { break }
			} else { break }
		}
		if let Some(new_value) = new_value {
			value.0.push(HistoricalValue {
				value: new_value,
				index: State::Transaction(self.current_layer),
			});
			return CleaningResult::Changed;
		}
		CleaningResult::Unchanged
	}
}

/// State for a historical value in a transaction
/// synchronously managed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
	/// Committed, transactional action do not
	/// change this state.
	Committed,
	/// Value in a transaction, contains the current
	/// number of transaction at creation.
	Transaction(usize),
}

impl State {
	fn transaction_index(&self) -> Option<usize> {
		if let &State::Transaction(ix) = self {
			Some(ix)
		} else {
			None
		}
	}
}
/// An entry at a given history height.
pub type HistoricalValue<V> = crate::HistoricalValue<V, State>;

/// History of value and their state.
pub type History<V> = crate::History<V, State>;

impl<V> History<V> {

	/// Set a value, it uses a global state as parameter.
	pub fn set(&mut self, states: &States, value: V) {
		if let Some(v) = self.0.last_mut() {
			debug_assert!(v.index.transaction_index().unwrap_or(0) <= states.current_layer,
				"History expects \
				only new values at the latest state, some state has not \
				synchronized properly");
			if v.index.transaction_index() == Some(states.current_layer) {
				v.value = value;
				return;
			}
		}
		self.0.push(HistoricalValue {
			value,
			index: State::Transaction(states.current_layer),
		});
	}

	/// Access to the latest pending value.
	pub fn get(&self) -> Option<&V> {
		self.0.last().map(|h| &h.value)
	}

	/// Extracts the latest value if there is one.
	pub fn into_pending(mut self) -> Option<V> {
		if let Some(v) = self.0.pop() {
			Some(v.value)
		} else {
			None
		}
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_prospective(&self) -> Option<&V> {
		match self.0.get(0) {
			Some(HistoricalValue {
				value: _,
				index: State::Committed,
			}) => {
				if let Some(HistoricalValue {
					value,
					index: State::Transaction(_),
				}) = self.0.get(1) {
					Some(&value)
				} else {
					None
				}
			},
			Some(HistoricalValue {
				value,
				index: State::Transaction(_),
			}) => Some(&value),
			None => None,
		}
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_committed(&self) -> Option<&V> {
		if let Some(HistoricalValue {
					value,
					index: State::Committed,
				}) = self.0.get(0) {
			return Some(&value)
		} else {
			None
		}
	}

	/// Extracts the committed value if there is one.
	pub fn into_committed(mut self) -> Option<V> {
		self.0.truncate(1);
		if let Some(HistoricalValue {
					value,
					index: State::Committed,
				}) = self.0.pop() {
			return Some(value)
		} else {
			None
		}
	}

	/// Returns mutable latest pending historical value.
	pub fn get_mut(&mut self) -> Option<HistoricalValue<&mut V>> {
		self.0.last_mut().map(|h| h.as_mut())
	}

}
