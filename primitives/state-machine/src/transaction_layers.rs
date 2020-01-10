// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Types and method for managing a stack of transactional values.

/// Stack of values at different transactional layers.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Layers<V>(pub(crate) smallvec::SmallVec<[LayerEntry<V>; ALLOCATED_HISTORY]>);

/// Index of reserved layer for commited values.
pub(crate) const COMMITTED_LAYER: usize = 0;

/// Start transaction stack layer at a size of two,
/// to only allocate at first transaction (we always
/// have a fix committed layer).
const ALLOCATED_HISTORY: usize = 2;

impl<V> Default for Layers<V> {
	fn default() -> Self {
		Layers(Default::default())
	}
}

/// An value entry of a indexed transactional layer.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct LayerEntry<V> {
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

/// Possible results when updating `Layers` after a
/// transaction operation.
#[derive(Debug, PartialEq)]
pub(crate) enum LayeredOpsResult {
	/// No inner data was changed, even technical
	/// data, therefore no update is needed.
	Unchanged,
	/// Byte representation did change.
	Changed,
	/// No data is stored anymore, `Layers` can be dropped.
	Cleared,
}

impl<V> Layers<V> {
	/// Push a value without checking without transactional layer
	/// consistency.
	pub(crate) fn push_unchecked(&mut self, item: LayerEntry<V>) {
		self.0.push(item);
	}

	/// Discard all prospective values, keeping previous committed value
	/// only.
	pub(crate) fn discard_prospective(&mut self) -> LayeredOpsResult {
		if self.0.is_empty() {
			return LayeredOpsResult::Cleared;
		}
		if self.0[0].index == COMMITTED_LAYER {
			if self.0.len() == 1 {
				LayeredOpsResult::Unchanged
			} else {
				self.0.truncate(1);
				LayeredOpsResult::Changed
			}
		} else {
			self.0.clear();
			LayeredOpsResult::Cleared
		}
	}

	/// Commits latest transaction pending value and clear existing transaction history.
	pub fn commit_prospective(&mut self) -> LayeredOpsResult {
		if self.0.is_empty() {
			return LayeredOpsResult::Cleared;
		}
		if self.0.len() == 1 {
			if self.0[0].index != COMMITTED_LAYER {
				self.0[0].index = COMMITTED_LAYER;
			} else {
				return LayeredOpsResult::Unchanged;
			}
		} else if let Some(mut v) = self.0.pop() {
			v.index = COMMITTED_LAYER;
			self.0.clear();
			self.0.push(v);
		}
		LayeredOpsResult::Changed
	}

	/// Access to the latest transactional value.
	pub(crate) fn get(&self) -> Option<&V> {
		self.0.last().map(|h| &h.value)
	}

	/// Returns mutable handle on latest pending historical value.
	pub(crate) fn get_mut(&mut self) -> Option<LayerEntry<&mut V>> {
		self.0.last_mut().map(|h| h.as_mut())
	}

	/// Set a new value, this function expect that
	/// `number_transactions` is a valid state (can fail
	/// otherwhise).
	pub(crate) fn set(&mut self, number_transactions: usize, value: V) {
		if let Some(v) = self.0.last_mut() {
			debug_assert!(v.index <= number_transactions,
				"Layers expects \
				only new values at the latest transaction \
				this indicates some unsynchronized layer value.");
			if v.index == number_transactions {
				v.value = value;
				return;
			}
		}
		self.0.push(LayerEntry {
			value,
			index: number_transactions,
		});
	}

	/// Extracts the committed value if there is one.
	pub fn into_committed(mut self) -> Option<V> {
		self.0.truncate(COMMITTED_LAYER + 1);
		if let Some(LayerEntry {
					value,
					index: COMMITTED_LAYER,
				}) = self.0.pop() {
			return Some(value)
		} else {
			None
		}
	}

	/// Commit all transaction layer that are stacked
	/// over the layer at `number_transaction`.
	pub fn commit_transaction(&mut self, number_transaction: usize) -> LayeredOpsResult {
		let mut new_value = None;
		// Iterate on layers to get latest layered value and remove
		// unused layered values inbetween.
		for i in (0 .. self.0.len()).rev() {
			if self.0[i].index > COMMITTED_LAYER {
				if self.0[i].index > number_transaction {
					// Remove value from committed layer
					if let Some(v) = self.0.pop() {
						if new_value.is_none() {
							new_value = Some(v.value);
						}
					}
				} else if self.0[i].index == number_transaction && new_value.is_some() {
					// Remove parent layer value (will be overwritten by `new_value`.
					self.0.pop();
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
			self.0.push(LayerEntry {
				value: new_value,
				index: number_transaction,
			});
			return LayeredOpsResult::Changed;
		}
		LayeredOpsResult::Unchanged
	}

	/// Discard value from transactional layers that are stacked over
	/// the layer at `number_transaction`.
	pub fn discard_transaction(&mut self, number_transaction: usize) -> LayeredOpsResult {
		let init_len = self.0.len();
		let truncate_index = self.0.iter().rev()
			.position(|entry| entry.index <= number_transaction)
			.unwrap_or(init_len);
		self.0.truncate(init_len - truncate_index);
		if self.0.is_empty() {
			LayeredOpsResult::Cleared
		} else if self.0.len() != init_len {
			LayeredOpsResult::Changed
		} else {
			LayeredOpsResult::Unchanged
		}
	}
}

#[cfg(any(test, feature = "test-helpers"))]
impl<V> Layers<V> {
	/// Get current number of stored historical values.
	pub fn len(&self) -> usize {
		self.0.len()
	}
}

#[cfg(test)]
impl<V> Layers<V> {
	/// Create an history from a sequence of historical values.
	pub fn from_iter(input: impl IntoIterator<Item = LayerEntry<V>>) -> Self {
		let mut history = Layers::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	/// Get latest prospective value, excludes
	/// committed values.
	pub(crate) fn get_prospective(&self) -> Option<&V> {
		match self.0.get(0) {
			Some(entry) if entry.index == COMMITTED_LAYER => {
				if let Some(entry) = self.0.get(1) {
					if entry.index > COMMITTED_LAYER {
						Some(&entry.value)
					} else {
						None
					}
				} else {
					None
				}
			},
			Some(entry) => Some(&entry.value),
			None => None,
		}
	}

	/// Get latest committed value.
	pub(crate) fn get_committed(&self) -> Option<&V> {
		if let Some(entry) = self.0.get(0) {
			if entry.index == COMMITTED_LAYER {
				return Some(&entry.value)
			} else {
				None
			}
		} else {
			None
		}
	}
}
