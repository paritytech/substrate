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

//! Data storage containing multiple states for a value.
//! This is used to store historical information for an item.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod synch_linear_transaction;

/// An entry at a given history index.
#[derive(Debug, Clone, PartialEq)]
pub struct HistoricalValue<V, I> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: I,
}

impl<V, I> From<(V, I)> for HistoricalValue<V, I> {
	fn from(input: (V, I)) -> HistoricalValue<V, I> {
		HistoricalValue { value: input.0, index: input.1 }
	}
}

impl<V, I: Clone> HistoricalValue<V, I> {
	fn as_mut(&mut self) -> HistoricalValue<&mut V, I> {
		HistoricalValue { value: &mut self.value, index: self.index.clone() }
	}
}

#[derive(Debug, PartialEq)]
/// The results from cleaning a historical value.
/// It should be used to update the calling context,
/// for instance if the historical value was stored
/// into a hashmap then it should be removed for
/// a `Cleared` result.
pub enum CleaningResult {
	/// No inner data was changed, even technical
	/// data, therefore no update is needed.
	Unchanged,
	/// Any data got modified, therefore an
	/// update may be needed.
	Changed,
	/// No data is stored anymore in this historical
	/// value, it can be dropped.
	Cleared,
}

/// History of value, this is used to keep trace of all changes
/// that occures on a value.
/// The different states for this value, are ordered by change time
/// in a simple stack.
#[derive(Debug, Clone, PartialEq)]
pub struct History<V, I>(pub(crate) smallvec::SmallVec<[HistoricalValue<V, I>; ALLOCATED_HISTORY]>);

impl<V, I> Default for History<V, I> {
	fn default() -> Self {
		History(Default::default())
	}
}

/// Size of preallocated history per element.
/// Current size is set to two, it is related to a use case
/// where value got two initial state by default (committed and prospective).
const ALLOCATED_HISTORY: usize = 2;

impl<V, I> History<V, I> {
	#[cfg(any(test, feature = "test-helpers"))]
	/// Get current number of stored historical values.
	pub fn len(&self) -> usize {
		self.0.len()
	}

	#[cfg(any(test, feature = "test-helpers"))]
	/// Create an history from a sequence of historical values.
	pub fn from_iter(input: impl IntoIterator<Item = HistoricalValue<V, I>>) -> Self {
		let mut history = History::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	/// Push a value without checking if it can overwrite the current
	/// state.
	/// This should only use after checking the state is correct
	/// (last item of historical value got a smaller index than
	/// the new one).
	pub fn push_unchecked(&mut self, item: HistoricalValue<V, I>) {
		self.0.push(item);
	}
}
