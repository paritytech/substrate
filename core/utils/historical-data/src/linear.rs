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

//! Linear historical state container.


/// An entry at a given history height.
pub type HistoricalValue<V> = crate::HistoricalValue<V, usize>;

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
pub struct History<V>(pub(crate) MemoryOnly<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Default::default())
	}
}

// Following implementation are here to isolate
// buffer specific functions.
impl<V> History<V> {
	pub(crate) fn get_unchecked(&self, index: usize) -> HistoricalValue<&V> {
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

	pub(crate) fn truncate(&mut self, index: usize) {
		self.0.truncate(index)
	}

	pub(crate) fn remove_until(&mut self, index: usize) {
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

	pub(crate) fn pop(&mut self) -> Option<HistoricalValue<V>> {
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

	pub(crate) fn mut_ref(&mut self, index: usize) -> &mut V {
		&mut self.0[index].value
	}
}
