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
//! This is mainly synchronous, it contains historical,
//! most operations do not require a separated state and
//! global state operation do update value synchronously
//! (to gain time on those operation a different design could
//! only change global state and apply garbage collection later).
//!
//! # Global state
//!
//! The global state is the current numbre of overlayed transaction layer.
//! Committing or discarding a layer must use this counter.
//!
//! # Local state
//!
//! Local state is eitheir defined as `Committed` or the index of the number
//! of layer at the time of creation.
//! Transaction operation does not interfere with value in `Committed` state.

use crate::CleaningResult;

/// Global state is the current number of overlay layers.
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

	/// Instantiate a random state, only for testing.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn test_state(
		current_layer: usize,
	) -> Self {
		States { current_layer }
	}

	/// Update states when discarding prospective changes.
	/// A subsequent update of all related stored history is needed.
	pub fn discard_prospective(&mut self) {
		self.current_layer = 1;
	}

	/// By default the current transaction is at least 1.
	/// 0 is a transient state used when applying transaction change,
	/// in this case transaction need to be restored to a valid state afterward.
	/// This function does restore the state.
	pub fn finalize_discard(&mut self) {
		if self.current_layer == 0 {
			self.current_layer = 1;
		}
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

	/// Update states when committing prospective.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_prospective(&mut self) {
		self.current_layer = 1;
	}

	/// After updating states to prospective, this function must be use
	/// on all values from this prospective. It commits pending value and
	/// clear existing history.
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
	/// A subsequent synchronous update of all related stored history is needed.
	pub fn discard_transaction(&mut self) {
		if self.current_layer > 0 {
			self.current_layer -= 1;
		}
	}

	/// Apply transaction discard on a historical value.
	/// Multiple calls to `discard_transaction` can be applied at once.
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

	/// Commit a transactional layer.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_transaction(&mut self) {
		if self.current_layer > 1 {
			self.current_layer -= 1;
		}
	}

	/// Apply transaction commit on a historical value.
	/// Multiple calls to `commit_transaction` can be applied at once.
	/// Committing value removes all unneeded states.
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

/// Historical value state for multiple transaction
/// with an additional commited state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
	/// Committed, transactional action do not
	/// change this state.
	Committed,
	/// Value in a transaction, contains the current
	/// number of transaction when value did change.
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

	/// Set a value, this use a global state as parameter.
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

	/// Extracts the latest pending value if there is one.
	pub fn into_pending(mut self) -> Option<V> {
		if let Some(v) = self.0.pop() {
			Some(v.value)
		} else {
			None
		}
	}

	/// Get latest prospective value, excludes
	/// committed values.
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

	/// Get latest committed value.
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

	/// Returns mutable handle on latest pending historical value.
	pub fn get_mut(&mut self) -> Option<HistoricalValue<&mut V>> {
		self.0.last_mut().map(|h| h.as_mut())
	}

}
