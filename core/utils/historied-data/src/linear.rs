// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use crate::State as TransactionState;
use rstd::vec::Vec;
use rstd::vec;

/// An entry at a given history height.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoriedValue<V> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: usize,
}

impl<V> From<(V, usize)> for HistoriedValue<V> {
	fn from(input: (V, usize)) -> HistoriedValue<V> {
		HistoriedValue { value: input.0, index: input.1 }
	}
}

impl<V> HistoriedValue<V> {
	fn as_ref(&self) -> HistoriedValue<&V> {
		HistoriedValue {
			value: &self.value,
			index: self.index,
		}
	}
}

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(not(feature = "std"))]
type MemoryOnly<V> = Vec<HistoriedValue<V>>;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(feature = "std")]
type MemoryOnly<V> = smallvec::SmallVec<[HistoriedValue<V>; ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
#[cfg(feature = "std")]
const ALLOCATED_HISTORY: usize = 2;

/// History of value that are related to a state history (eg field `history` of
/// an `OverlayedChangeSet`).
///
/// Values are always paired with a state history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(MemoryOnly<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Default::default())
	}
}

// Following implementation are here to isolate
// buffer specific functions.
impl<V> History<V> {

	fn get_state(&self, index: usize) -> HistoriedValue<&V> {
		self.0[index].as_ref()
	}

	#[cfg(any(test, feature = "test"))]
	/// Create an history from an existing history.
	pub fn from_iter(input: impl IntoIterator<Item = HistoriedValue<V>>) -> Self {
		let mut history = History::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	#[cfg(any(test, feature = "test"))]
	pub fn len(&self) -> usize {
		self.0.len()
	}

	#[cfg(not(any(test, feature = "test")))]
	fn len(&self) -> usize {
		self.0.len()
	}

	fn truncate(&mut self, index: usize) {
		self.0.truncate(index)
	}

	fn pop(&mut self) -> Option<HistoriedValue<V>> {
		self.0.pop()
	}

	fn remove(&mut self, index: usize) {
		let _ = self.0.remove(index);
	}

	/// Append without checking if a value already exist.
	/// If a value already exists, the history will be broken.
	/// This method shall only be call after a `get_mut` where
	/// the returned index indicate that a `set` will result
	/// in appending a value.
	pub fn push_unchecked(&mut self, value: HistoriedValue<V>) {
		self.0.push(value)
	}

	/// Set a value, it uses a state history as parameter.
	/// This method uses `get_mut` and do remove pending
	/// dropped value.
	pub fn set(&mut self, history: &[TransactionState], value: V) {
		if let Some(v) = self.get_mut(history) {
			if v.index == history.len() - 1 {
				*v.value = value;
				return;
			}
		}
		self.push_unchecked(HistoriedValue {
			value,
			index: history.len() - 1,
		});
	}

	fn mut_ref(&mut self, index: usize) -> &mut V {
		&mut self.0[index].value
	}

}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct States(Vec<TransactionState>);

impl Default for States {
	fn default() -> Self {
		States(vec![TransactionState::Pending])
	}
}

impl States {
	pub fn as_ref(&self) -> &[TransactionState] {
		self.0.as_ref()
	}

	pub fn iter<'a>(&'a self) -> impl Iterator<Item = (usize, TransactionState)> + 'a {
		self.0.iter().map(Clone::clone).enumerate()
	}
}

impl States {

	/// Build any state for testing only.
	#[cfg(any(test, feature = "test"))]
	pub fn test_vector(test_states: Vec<TransactionState>) -> Self {
		States(test_states)
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective => self.0[i] = TransactionState::Dropped,
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		debug_assert!(self.0.len() > 0);
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Prospective
				| TransactionState::TxPending
				| TransactionState::Pending => self.0[i] = TransactionState::Committed,
				| TransactionState::Committed => break,
			}
		}
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
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Prospective
				| TransactionState::Pending => self.0[i] = TransactionState::Dropped,
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Dropped;
					break;
				},
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Prospective
				| TransactionState::Dropped => (),
				TransactionState::Pending => self.0[i] = TransactionState::Prospective,
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Prospective;
					break;
				},
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Return array of `TxPending` indexes in state.
	/// This is use as an input for garbage collection.
	pub fn transaction_indexes(&self) -> Vec<usize> {
		let mut transaction_index = Vec::new();
		for (i, state) in self.0.iter().enumerate() {
			if &TransactionState::TxPending == state {
				transaction_index.push(i);
			}
		}
		transaction_index
	}


}

impl<V> History<V> {

	/// Access to latest pending value (non dropped state in history).
	/// When possible please prefer `get_mut` as it can free
	/// some memory.
	pub fn get(&self, history: &[TransactionState]) -> Option<&V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Committed =>
					return Some(value),
			}
		}
		None
	}

	/// Get latest value, consuming the historied data.
	pub fn into_pending(mut self, history: &[TransactionState]) -> Option<V> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Committed => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.value);
				},
			}
		}
		None
	}


	#[cfg(any(test, feature = "test"))]
	pub fn get_prospective(&self, history: &[TransactionState]) -> Option<&V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective =>
					return Some(value),
				TransactionState::Committed
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	#[cfg(any(test, feature = "test"))]
	pub fn get_committed(&self, history: &[TransactionState]) -> Option<&V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Committed => return Some(value),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	pub fn into_committed(mut self, history: &[TransactionState]) -> Option<V> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Committed => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.value);
				},
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	/// Access to latest pending value (non dropped state in history).
	///
	/// This method removes latest dropped values up to the latest valid value.
	pub fn get_mut(&mut self, history: &[TransactionState]) -> Option<HistoriedValue<&mut V>> {

		let mut index = self.len();
		if index == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Committed => {
					// here we could gc all preceding values but that is additional cost
					// and get_mut should stop at pending following committed.
					return Some((self.mut_ref(index), history_index).into())
				},
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective => {
					return Some((self.mut_ref(index), history_index).into())
				},
				TransactionState::Dropped => { let _ = self.pop(); },
			}
		}
		None
	}


	/// Garbage collect the history, act as a `get_mut` with additional cost.
	/// To run `eager`, a `transaction_index` parameter of all `TxPending` states
	/// must be provided, then all dropped value are removed even if it means shifting
	/// array byte. Otherwhise we mainly garbage collect up to last Commit state
	/// (truncate left size).
	pub fn get_mut_pruning(
		&mut self,
		history: &[TransactionState],
		transaction_index: Option<&[usize]>,
	) -> Option<HistoriedValue<&mut V>> {
		if let Some(mut transaction_index) = transaction_index {
			let mut index = self.len();
			if index == 0 {
				return None;
			}
			// indicates that we got a value to return up to previous
			// `TxPending` so values in between can be dropped.
			let mut below_value = usize::max_value();
			let mut result: Option<(usize, usize)> = None;
			// internal method: should be use properly
			// (history of the right overlay change set
			// is size aligned).
			debug_assert!(history.len() >= index);
			while index > 0 {
				index -= 1;
				let history_index = self.get_state(index).index;
				match history[history_index] {
					TransactionState::Committed => {
						for _ in 0..index {
							self.remove(0);
						}
						result = Some(result.map(|(i, history_index)| (i - index, history_index))
							.unwrap_or((0, history_index)));
						break;
					},
					TransactionState::Pending
					| TransactionState::Prospective => {
						if history_index >= below_value {
							self.remove(index);
							result.as_mut().map(|(i, _)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
							// move to next previous `TxPending`
							while below_value > history_index {
								// mut slice pop
								let split = transaction_index.split_last()
									.map(|(v, sl)| (*v, sl))
									.unwrap_or((0, &[]));
								below_value = split.0;
								transaction_index = split.1;
							}
						}
					},
					TransactionState::TxPending => {
						if history_index >= below_value {
							self.remove(index);
							result.as_mut().map(|(i, _)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
						}
						below_value = usize::max_value();
					},
					TransactionState::Dropped => {
						self.remove(index);
					},
				}
			}
			if let Some((index, history_index)) = result {
				Some((self.mut_ref(index), history_index).into())
			} else { None }

		} else {
			self.get_mut(history)
		}
	}

}
