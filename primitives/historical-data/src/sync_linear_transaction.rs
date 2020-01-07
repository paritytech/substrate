// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Linear sequence of historical data with transactional
//! support.
//!
//! This is mainly synchronous, global transactional state operation
//! do update value synchronously (to gain time on those operation a
//! different design could be to switch to only  change global state
//! and apply garbage collection later if needed).
//!
//! # Global state
//!
//! The global state is the current number of overlayed transaction layers.
//! Committing or discarding a layer simply change this counter and a
//! synchronous local state operations should follow to update every
//! associated historical data.
//!
//! # Local state
//!
//! Local state is either defined as `Committed` or `Prospective`.
//! If in `Prospective` state, the index of the number of layesr at the time
//! of creation is also needed.
//! Transaction operation does not interfere with value in `Committed` state.

use crate::CleaningResult;

/// History of value and their state.
pub type History<V> = crate::History<V, State>;

/// An entry at a given history height.
pub type HistoricalEntry<V> = crate::HistoricalEntry<V, State>;


// We use to 1 to be able to discard this transaction.
const COMMITTED_LAYER: usize = 1;

/// Global state contains only the current number of overlay layers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States { current_layer: usize }

impl Default for States {
	fn default() -> Self {
		States { current_layer: COMMITTED_LAYER }
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

	/// Update global state for discarding prospective.
	/// A subsequent update of all related stored history is needed.
	pub fn discard_prospective(&mut self) {
		// Point to committed layer.
		self.current_layer = COMMITTED_LAYER;
	}

	/// After a prospective was discarded, clear prospective history.
	pub fn apply_discard_prospective<V>(value: &mut History<V>) -> CleaningResult {
		if value.0.is_empty() {
			return CleaningResult::Cleared;
		}
		if value.0[0].index == State::Committed {
			if value.0.len() == COMMITTED_LAYER {
				CleaningResult::Unchanged
			} else {
				value.0.truncate(COMMITTED_LAYER);
				CleaningResult::Changed
			}
		} else {
			value.0.clear();
			CleaningResult::Cleared
		}
	}

	/// Update global state for committing prospective.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_prospective(&mut self) {
		// Point to committed layer.
		self.current_layer = COMMITTED_LAYER;
	}

	/// After updating states to prospective, this function must be use
	/// on all values from this prospective. It commits pending value and
	/// clear existing history.
	pub fn apply_commit_prospective<V>(value: &mut History<V>) -> CleaningResult {
		if value.0.is_empty() {
			return CleaningResult::Cleared;
		}
		if value.0.len() == COMMITTED_LAYER {
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
		self.current_layer = self.current_layer.saturating_sub(1);
	}

	/// Apply transaction discard on a historical value.
	/// Multiple calls to `discard_transaction` can be applied at once.
	pub fn apply_discard_transaction<V>(&self, value: &mut History<V>) -> CleaningResult {
		let init_len = value.0.len();
		for i in (0 .. value.0.len()).rev() {
			if let HistoricalEntry {
				value: _,
				index: State::Transaction(ix),
			} = value.0[i] {
				if ix > self.current_layer {
					value.0.pop();
				} else {
					break;
				}
			} else {
				break;
			}
		}
		if value.0.is_empty() {
			CleaningResult::Cleared
		} else if value.0.len() != init_len {
			CleaningResult::Changed
		} else {
			CleaningResult::Unchanged
		}
	}

	/// By default the current transaction is at least 1.
	/// 0 is a transient state used when applying transaction change,
	/// in this case transaction need to be restored to a valid state afterward.
	/// This function does restore the state.
	pub fn finalize_discard(&mut self) {
		if self.current_layer == 0 {
			// Point back to committed layer.
			self.current_layer = COMMITTED_LAYER;
		}
	}

	/// Commit a transactional layer.
	/// A subsequent update of all related stored history is needed.
	pub fn commit_transaction(&mut self) {
		if self.current_layer > COMMITTED_LAYER {
			self.current_layer -= 1;
		}
	}

	/// Apply transaction commit on a historical value.
	/// Multiple calls to `commit_transaction` can be applied at once.
	/// Committing value removes all unneeded states.
	pub fn apply_commit_transaction<V>(&self, value: &mut History<V>) -> CleaningResult {
		let mut new_value = None;
		// Iterate on history to get current committed value and remove
		// unused transaction values that are between this new committed
		// value and the current transaction layer.
		for i in (0 .. value.0.len()).rev() {
			if let State::Transaction(ix) = value.0[i].index {
				if ix > self.current_layer {
					// Remove value from committed layer
					if let Some(v) = value.0.pop() {
						if new_value.is_none() {
							new_value = Some(v.value);
						}
					}
				} else if ix == self.current_layer && new_value.is_some() {
					// Remove parent layer value (will be overwritten by `new_value`.
					value.0.pop();
				} else {
					// Do not remove this is already a valid state.
					break;
				}
			} else {
				// Non transactional layer, stop removing history.
				break;
			}
		}
		if let Some(new_value) = new_value {
			value.0.push(HistoricalEntry {
				value: new_value,
				index: State::Transaction(self.current_layer),
			});
			return CleaningResult::Changed;
		}
		CleaningResult::Unchanged
	}
}

/// Historical value state of multiple transaction
/// with an alterantive committed state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
	/// Committed, in this state no action on transaction
	/// can modify this value.
	Committed,
	/// Value relates to a transaction, the state contains the current
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
		self.0.push(HistoricalEntry {
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
			Some(HistoricalEntry {
				value: _,
				index: State::Committed,
			}) => {
				if let Some(HistoricalEntry {
					value,
					index: State::Transaction(_),
				}) = self.0.get(1) {
					Some(&value)
				} else {
					None
				}
			},
			Some(HistoricalEntry {
				value,
				index: State::Transaction(_),
			}) => Some(&value),
			None => None,
		}
	}

	/// Get latest committed value.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn get_committed(&self) -> Option<&V> {
		if let Some(HistoricalEntry {
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
		self.0.truncate(COMMITTED_LAYER);
		if let Some(HistoricalEntry {
					value,
					index: State::Committed,
				}) = self.0.pop() {
			return Some(value)
		} else {
			None
		}
	}

	/// Returns mutable handle on latest pending historical value.
	pub fn get_mut(&mut self) -> Option<HistoricalEntry<&mut V>> {
		self.0.last_mut().map(|h| h.as_mut())
	}
}
