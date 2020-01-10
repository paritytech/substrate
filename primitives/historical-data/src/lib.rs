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

//! Data storage containing multiple states of a value.
//! This is used to store historical information for an item.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod sync_linear_transaction;

/// Stack of values in different transactional layers.
#[derive(Debug, Clone, PartialEq)]
pub struct Layers<V>(pub(crate) smallvec::SmallVec<[LayerEntry<V>; ALLOCATED_HISTORY]>);

/// Size of preallocated history per element.
/// Current size is two, that is currently related to the use case
/// where value got `committed` and `prospective` initial state by default.
const ALLOCATED_HISTORY: usize = 2;

impl<V> Default for Layers<V> {
	fn default() -> Self {
		Layers(Default::default())
	}
}

/// An value entry in a given indexed transactional layer.
#[derive(Debug, Clone, PartialEq)]
pub struct LayerEntry<V> {
	/// The stored value.
	pub value: V,
	/// The transactional layer index.
	pub index: usize,
}

impl<V> From<(V, usize)> for LayerEntry<V> {
	fn from(input: (V, usize)) -> LayerEntry<V> {
		LayerEntry { value: input.0, index: input.1 }
	}
}

impl<V> LayerEntry<V> {
	fn as_mut(&mut self) -> LayerEntry<&mut V> {
		LayerEntry { value: &mut self.value, index: self.index }
	}
}

/// The results from changing a historical value.
/// It should be used to apply subsequent update the calling context.
/// For instance if the historical value was stored into a hashmap,
/// then it should be removed from it on a `Cleared` result.
#[derive(Debug, PartialEq)]
pub enum LayeredOpsResult {
	/// No inner data was changed, even technical
	/// data, therefore no update is needed.
	Unchanged,
	/// Historical representation did change.
	/// This includes cleaning of deprecated historic values.
	Changed,
	/// No historical data is stored anymore, it can be dropped.
	Cleared,
}

impl<V> Layers<V> {
	/// Push a value without checking if it can overwrite the current
	/// state.
	/// This should only use after checking the state is correct
	/// (last item of historical value got a smaller index than
	/// the new one).
	pub fn push_unchecked(&mut self, item: LayerEntry<V>) {
		self.0.push(item);
	}
}

#[cfg(any(test, feature = "test-helpers"))]
impl<V> Layers<V> {
	/// Get current number of stored historical values.
	pub fn len(&self) -> usize {
		self.0.len()
	}

	/// Create an history from a sequence of historical values.
	pub fn from_iter(input: impl IntoIterator<Item = LayerEntry<V>>) -> Self {
		let mut history = Layers::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}
}
