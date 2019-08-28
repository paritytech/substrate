// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.	If not, see <http://www.gnu.org/licenses/>.

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

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(not(feature = "std"))]
type MemoryOnly<V> = Vec<(V, usize)>;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(feature = "std")]
type MemoryOnly<V> = smallvec::SmallVec<[(V, usize); ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
const ALLOCATED_HISTORY: usize = 2;

/// History of value that are related to a state history (eg field `history` of
/// an `OverlayedChangeSet`).
///
/// Values are always paired with a state history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(MemoryOnly<V>);


impl<V> History<V> {
	fn get_state(&self, index: usize) -> (&V, usize) {
		(&self.0[index].0, self.0[index].1)
	}
}

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Default::default()) 
	}
}

impl<V> History<V> {

	#[cfg(any(test, feature = "test"))]
	/// Create an history from an existing history.
	pub fn from_iter(input: impl IntoIterator<Item = (V, usize)>) -> Self {
		let mut history = History::default();
		for v in input {
			history.force_push(v.0, v.1);
		}
		history
	}

	#[cfg(any(test, feature = "test"))]
	/// Debugging function for test and fuzzing.
	pub fn internal_item_counts(&self) -> usize {
		self.0.len()
	}

	fn len(&self) -> usize {
		self.0.len()
	}

	fn truncate(&mut self, index: usize) {
		self.0.truncate(index)
	}

	fn pop(&mut self) -> Option<(V, usize)> {
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
	pub fn force_push(&mut self, val: V, tx_index: usize) {
		self.0.push((val, tx_index))
	}

	/// Set a value, it uses a state history as parameter.
	/// This method uses `get_mut` and do remove pending
	/// dropped value.
	pub fn set(&mut self, history: &[TransactionState], val: V) {
		if let Some((v, index)) = self.get_mut(history) {
			if index == history.len() - 1 {
				*v = val;
				return;
			}
		}
		self.force_push(val, history.len() - 1);
	}

	fn mut_ref(&mut self, index: usize) -> &mut V {
		&mut self.0[index].0
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
	pub fn test_vector(test_state: Vec<TransactionState>) -> Self {
		States(test_state)
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
			let (v, history_index) = self.get_state(index);
			match history[history_index] {
				TransactionState::Dropped => (), 
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Committed =>
					return Some(v),
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
			let (v, history_index) = self.get_state(index);
			match history[history_index] {
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective =>
					return Some(v),
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
			let (v, history_index) = self.get_state(index);
			match history[history_index] {
				TransactionState::Committed =>
					return Some(v),
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
			let history_index = self.get_state(index).1;
			match history[history_index] {
				TransactionState::Committed => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.0);
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
	/// This method remove latest dropped value up to the latest valid value.
	pub fn get_mut(&mut self, history: &[TransactionState]) -> Option<(&mut V, usize)> {

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
			let history_index = self.get_state(index).1;
			match history[history_index] {
				TransactionState::Committed => {
					// here we could gc all preceding values but that is additional cost
					// and get_mut should stop at pending following committed.
					return Some((self.mut_ref(index), history_index))
				},
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective => {
					return Some((self.mut_ref(index), history_index))
				},
				TransactionState::Dropped => { let _ = self.pop(); },
			}
		}
		None
	}


	/// Garbage collect a history, act as a `get_mut` with additional cost.
	/// If `eager` is true, all dropped value are removed even if it means shifting
	/// array byte. Otherwhise we mainly ensure collection up to last Commit state
	/// (truncate left size).
	pub fn gc(
		&mut self,
		history: &[TransactionState],
		tx_index: Option<&[usize]>,
	) -> Option<(&mut V, usize)> {
		if let Some(tx_index) = tx_index {
			let mut tx_index = &tx_index[..];
			let mut index = self.len();
			if index == 0 {
				return None;
			}
			let mut bellow_value = usize::max_value();
			let mut result: Option<(usize, usize)> = None;
			// internal method: should be use properly
			// (history of the right overlay change set
			// is size aligned).
			debug_assert!(history.len() >= index); 
			while index > 0 {
				index -= 1;
				let history_index = self.get_state(index).1;
				match history[history_index] {
					TransactionState::Committed => {
						for _ in 0..index {
							self.remove(0);
						}
						result = Some(result.map(|(i, hi)| (i - index, hi)).unwrap_or((0, history_index)));
						index = 0;
					},
					TransactionState::Pending
					| TransactionState::Prospective => {
						if history_index >= bellow_value {
							self.remove(index);
							result.as_mut().map(|(i, _hi)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
							while bellow_value > history_index {
								// bellow_value = pop
								let split = tx_index.split_last()
									.map(|(v, sl)| (*v, sl))
									.unwrap_or((0, &[]));
								bellow_value = split.0;
								tx_index = split.1;
							}
						}
					},
					TransactionState::TxPending => {
						if history_index >= bellow_value {
							self.remove(index);
							result.as_mut().map(|(i, _hi)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
						}
						bellow_value = usize::max_value();
					},
					TransactionState::Dropped => {
						self.remove(index);
					},
				}
			}
			if let Some((index, history_index)) = result {
				Some((self.mut_ref(index), history_index))
			} else { None }

		} else {
			return self.get_mut(history);
		}
	}
}


