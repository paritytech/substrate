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

//! Data storage containing multiple state for a value.
//! This is use to store historical information for an item,
//! and does have to include any proof.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod synch_linear_transaction;

/// An entry at a given history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
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

#[derive(PartialEq)]
#[cfg_attr(any(test, feature = "test"), derive(Debug))]
/// Results from cleaning a data with history.
/// It should be use to update from the calling context,
/// for instance remove this data from a map if it was cleared.
pub enum CleaningResult {
	Unchanged,
	Changed,
	Cleared,
}

/// History of value and their state.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct History<V, I>(pub(crate) smallvec::SmallVec<[HistoricalValue<V, I>; ALLOCATED_HISTORY]>);

impl<V, I> Default for History<V, I> {
	fn default() -> Self {
		History(Default::default())
	}
}

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
#[cfg(feature = "std")]
const ALLOCATED_HISTORY: usize = 2;

impl<V, I> History<V, I> {
	/// Get current number of stored historical values.
	pub fn len(&self) -> usize {
		self.0.len()
	}

	#[cfg(any(test, feature = "test-helpers"))]
	/// Create an history from an existing history.
	pub fn from_iter(input: impl IntoIterator<Item = HistoricalValue<V, I>>) -> Self {
		let mut history = History::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	/// Push a value without checking if it can overwrite the current
	/// state.
	pub fn push_unchecked(&mut self, item: HistoricalValue<V, I>) {
		self.0.push(item);
	}
}
