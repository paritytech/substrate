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

/// Base code for fuzzing.
#[cfg(any(test, feature = "test-helpers"))]
pub mod fuzz {
	use crate::overlayed_changes::OverlayedChanges;
	use std::collections::HashMap;
	use super::Layers;

	/// Size of key, max 255
	const KEY_SPACE: u8 = 20;

	/// Size of key, max 255
	const VALUE_SPACE: u8 = 50;

	impl<V> Layers<V> {
		/// Get current number of stored historical values.
		pub fn len(&self) -> usize {
			self.0.len()
		}
	}

	/// Fuzz input against a stack of hash map reference implementation.
	/// `check_compactness` add a check in the number of stored entry.
	pub fn fuzz_transactions_inner(input: &[u8], check_compactness: bool) {
		let mut input_index: usize = 0;
		let mut overlayed = OverlayedChanges::default();
		let mut ref_overlayed = RefOverlayedChanges::default();

		let mut actions = Vec::new();
		let mut values = Vec::new();
		loop {
			let action: Actions = if let Some(v) = input.get(input_index) {
				input_index += 1;
				(*v).into()
			} else { break };
			//println!("{:?}", action);

			actions.push(action);
			match action {
				Actions::CommitProspective => {
					overlayed.commit_prospective();
					ref_overlayed.commit_prospective();
				},
				Actions::DropProspective => {
					overlayed.discard_prospective();
					ref_overlayed.discard_prospective();
				},
				Actions::NewTransaction => {
					overlayed.start_transaction();
					ref_overlayed.start_transaction();
				},
				Actions::CommitTransaction => {
					overlayed.commit_transaction();
					ref_overlayed.commit_transaction();
				},
				Actions::DropTransaction => {
					overlayed.discard_transaction();
					ref_overlayed.discard_transaction();
				},
				Actions::Insert => {
					let key = if let Some(v) = input.get(input_index) {
						input_index += 1;
						v % KEY_SPACE
					} else { break };
					let value = if let Some(v) = input.get(input_index) {
						input_index += 1;
						v % VALUE_SPACE
					} else { break };
					values.push((key, value));
					overlayed.set_storage(vec![key], Some(vec![value]));
					ref_overlayed.set_storage(vec![key], Some(vec![value]));
				}
			}

		}

		let mut success = true;

		let (check_value, len) = check_values(&overlayed, &ref_overlayed);
		success &= check_value;

		if check_compactness {
			let reference_size = ref_overlayed.total_length();
			let size = overlayed.top_count_keyvalue_pair();
			if reference_size != size {
				println!("inconsistent gc {} {}", size, reference_size);
				success = false;
			}
			let (check_value, len_compactness) = check_values(&overlayed, &ref_overlayed);
			success &= check_value;
			success &= len_compactness == len;
		}
		ref_overlayed.commit_prospective();
		let ref_len = ref_overlayed.committed.len();
		if len != ref_len {
			println!("inconsistent length {} {}", len, ref_len);
			success = false;
		}
		if !success {
			println!("fuzzing: \n {:x?}", (&actions, &values));
			println!("input: \n {:?}", &input);
		}

		assert!(success);
	}

	fn check_values(overlayed: &OverlayedChanges, ref_overlayed: &RefOverlayedChanges) -> (bool, usize) {
		let mut len = 0;
		let mut success = true;
		for (key, value) in overlayed.iter_values(None) {
			let ref_value = ref_overlayed.storage(key);
			if Some(value) != ref_value {
				println!("at {:x?} different values {:x?} {:x?}", key, Some(value), ref_value);
				success = false;
			}
			len += 1;
		}
		(success, len)
	}

	#[derive(Clone, Copy, Debug)]
	enum Actions {
		Insert,
		// Delete, same as an insert do not test.
		CommitProspective,
		DropProspective,
		NewTransaction,
		CommitTransaction,
		DropTransaction,
	}

	impl From<u8> for Actions {
		fn from(v: u8) -> Self {
			match (v as usize) * 100 / 255 {
				v if v <= 5 => Actions::CommitProspective,
				v if v <= 10 => Actions::DropProspective,
				v if v <= 20 => Actions::NewTransaction,
				v if v <= 30 => Actions::CommitTransaction,
				v if v <= 40 => Actions::DropTransaction,
				_ => Actions::Insert,
			}
		}
	}

	/// A simple implementation of overlayed change
	/// to use as a comparision.
	/// It is partly incomplete (no child trie support, no change trie).
	#[derive(Debug, Clone, Default)]
	struct RefOverlayedChanges {
		committed: HashMap<Vec<u8>, Vec<u8>>,
		prospective: HashMap<Vec<u8>, Vec<u8>>,
		transactions: Vec<HashMap<Vec<u8>, Vec<u8>>>,
	}

	impl RefOverlayedChanges {
		fn discard_prospective(&mut self) {
			self.transactions.clear();
			self.prospective.clear();
		}

		fn commit_prospective(&mut self) {
			for _ in 0 .. self.transactions.len() {
				self.commit_transaction();
			}
			self.committed.extend(self.prospective.drain());
		}

		fn start_transaction(&mut self) {
			self.transactions.push(Default::default());
		}

		fn discard_transaction(&mut self) {
			if self.transactions.len() == 0 {
				// clear prospective on no transaction started.
				self.prospective.clear();
			} else {
				let _ = self.transactions.pop();
			}
		}

		/// Commit a transactional layer.
		fn commit_transaction(&mut self) {
			match self.transactions.len() {
				0 => (),
				1 => self.prospective.extend(
					self.transactions.pop().expect("length just checked").into_iter()
				),
				_ => {
					let t = self.transactions.pop().expect("length just checked");
					self.transactions.last_mut().expect("length just checked")
						.extend(t.into_iter());
				}
			}
		}

		fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
			if self.transactions.len() > 0 {
				self.transactions.last_mut().expect("length just checked")
					.insert(key, val.expect("fuzzer do not delete"));
			} else {
				self.prospective.insert(key, val.expect("fuzzer do not delete"));
			}
		}

		fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
			for t in self.transactions.iter().rev() {
				if let Some(v) = t.get(key) {
					return Some(Some(v));
				}
			}
			if let Some(v) = self.prospective.get(key) {
				return Some(Some(v));
			}
			if let Some(v) = self.committed.get(key) {
				return Some(Some(v));
			}
			None
		}

		fn total_length(&self) -> usize {
			let tr_len: usize = self.transactions.iter()
				.map(|l| l.len()).sum();
			self.committed.len() + self.prospective.len() + tr_len
		}
	}

	// Those are samples which found error during fuzzing.
	// They are kept as a low cust rust test for non regression purpose.
	#[test]
	fn previous_fuzzed_error() {
		let inputs = [
			vec![0x2,0xee,0xee,0x12,0x2,0x16,0x67,0xee,0xee,0xee,],
			vec![50, 208, 50, 38, 46, 58, 209, 50, 216, 255, 255],
			vec![0x98,0x98,0xf6,0x12,0xee,0x98,0xf9,],
			vec![0xf1,0x0,0x0,0x1,0x38,0xb2,0x0,0x67,],
			vec![238, 0, 36, 43, 50, 46, 38, 211, 0, 0, 61],
			vec![50, 255, 38, 38, 186, 35, 46, 43, 46, 35, 255, 255, 102, 67],
			vec![0x6e, 0xff, 0xf7, 0x0, 0x6e, 0xff, 0xff, 0x2d, 0xff, 0xff, 0xff, 0xe],
			vec![0x2e,0x6e,0x22,0x32,0x2e,0x6e,0x22,0x32,0x3f,0x2e,],
			vec![0xd9,0xff,0xfd,0x0,0xff,0xff,0xf8,0x1,0x92,0xff,0xbf,0x14,],
			vec![0xef,0xdf,0xc1,0x0,0xc1,0xdf,0xc1,0x2b,0xf3,0xf3,0xb0,0x18,
				0xef,0xdf,0x2e,0x3a,0xef,0xdf,0x0,0xc1,0xf3,0x30,0x18,0xef,0xdf,
				0xc1,0x2b,0xf3,0xf3,0x30,0x17,0x0,0xdf,],
		];
		for input in inputs.iter() {
			fuzz_transactions_inner(&input[..], true);
		}
	}
}
