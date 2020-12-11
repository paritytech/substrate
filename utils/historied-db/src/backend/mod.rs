// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Linear backend structures for historied data storage.

use crate::historied::HistoriedValue;
use sp_std::ops::Range;
use crate::InitFrom;

/// Data stored as rust structs in memory.
pub mod in_memory;

#[cfg(feature = "encoded-array-backend")]
/// Items encoded in a byte buffer, without intermediate
/// data structures.
pub mod encoded_array;

/// Historied values are be split between multiple encoded
/// array of nodes.
pub mod nodes;

/// Backend for linear storage of item, with access optimized for last indexes.
///
/// This is the building block for this crate data structures.
/// Values are addressed by their contiguous integer index position.
///
/// The api map this integer index with an opaque internal backend index
/// that would be use with this api, accessing this internal index
/// is done with either `last` or `lookup` method.
///
/// Implementation should always favor last index access over random lookup.
pub trait LinearStorage<V, S>: InitFrom {
	/// Internal index over a location in the storage.
	/// Access to data when using this internal index should
	/// be direct, allowing to iterate efficiently on data
	/// with this index.
	type Index: Copy;
	/// Get reference to last item.
	fn last(&self) -> Option<Self::Index>;
	/// Index here are only existing index.
	fn previous_index(&self, index: Self::Index) -> Option<Self::Index>;
	/// Lookup for internal index, from an integer index.
	fn lookup(&self, index: usize) -> Option<Self::Index>;
	/// Reverse iteration on internal indexes.
	fn rev_index_iter(&self) -> RevIter<V, S, Self> {
		let first = self.last();
		RevIter(self, first, Default::default())
	}
	/// This does not need to be very efficient as it is mainly for
	/// garbage collection.
	fn truncate_until(&mut self, split_off: usize);
	/// Number of element for different S.
	fn len(&self) -> usize;
	/// Array like get.
	fn get(&self, index: Self::Index) -> HistoriedValue<V, S>;
	/// Array like get using a index lookup.
	fn get_lookup(&self, index: usize) -> Option<HistoriedValue<V, S>> {
		self.lookup(index).map(|index| self.get(index))
	}
	/// Entry.
	fn entry<'a>(&'a mut self, index: usize) -> Entry<'a, V, S, Self> {
		let index = self.lookup(index);
		let value = index.clone().map(|index| self.get(index));
		let insert = value.is_none();
		Entry {
			value,
			index,
			storage: self,
			changed: false,
			insert,
		}
	}
	/// Array like get.
	fn get_state(&self, index: Self::Index) -> S;
	/// Array like get.
	fn get_state_lookup(&self, index: usize) -> Option<S> {
		self.lookup(index).map(|index| self.get_state(index))
	}
	/// Vec like push.
	fn push(&mut self, value: HistoriedValue<V, S>);
	/// Vec like insert, this is mainly use in tree implementation.
	/// So when used as tree branch container, a efficient implementation
	/// shall be use.
	fn insert(&mut self, index: Self::Index, value: HistoriedValue<V, S>);
	/// Insert with a lookup.
	fn insert_lookup(&mut self, index: usize, value: HistoriedValue<V, S>) {
		if let Some(index) = self.lookup(index) {
			self.insert(index, value)
		} else {
			self.push(value)
		}
	}
	/// Vec like remove, this is mainly use in tree branch implementation.
	fn remove(&mut self, index: Self::Index);
	/// Remove value with a lookup.
	fn remove_lookup(&mut self, index: usize) {
		self.lookup(index).map(|index| self.remove(index));
	}
	/// Efficient removal of last item.
	fn pop(&mut self) -> Option<HistoriedValue<V, S>>;
	/// Clear all item, putting the backend in an empty state.
	fn clear(&mut self);
	/// Truncate items after this location (same semantic as std `Vec`).
	fn truncate(&mut self, at: usize);
	/// Replace a value at a given index.
	/// Note that for some backend this can be slow.
	fn emplace(&mut self, index: Self::Index, value: HistoriedValue<V, S>);
	/// Emplace with lookup.
	fn emplace_lookup(&mut self, at: usize, value: HistoriedValue<V, S>) {
		self.lookup(at).map(|index| self.emplace(index, value));
	}
}

/// Backend for linear storage with inmemory reference.
pub trait LinearStorageMem<V, S>: LinearStorage<V, S> {
	/// Unchecked access to value pointer and state.
	fn get_ref(&self, index: Self::Index) -> HistoriedValue<&V, S>;
	/// Unchecked access to value mutable pointer and state.
	fn get_ref_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut V, S>;
}

/// Backend for linear storage with inmemory reference to a slice of bytes.
pub trait LinearStorageSlice<V: AsRef<[u8]>, S>: LinearStorage<V, S> {
	/// Unchecked access to value slice and state.
	fn get_slice(&self, index: Self::Index) -> HistoriedValue<&[u8], S>;
	/// Unchecked mutable access to mutable value slice and state.
	fn get_slice_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut [u8], S>;
}

/// Technical trait to use for composing without
/// the lifetime issue that can occurs with `LinearStorageSlice`.
pub trait LinearStorageRange<'a, V, S>: LinearStorage<V, S> {
	/// Instantiate from an existing slice.
	fn from_slice_owned(slice: &[u8]) -> Option<Self>;
	/// Instantiate from an existing slice, keeping
	/// its lifetime and potentially not copying its
	/// data.
	fn from_slice_ref(slice: &'a [u8]) -> Option<Self>;
	/// Return the range for the value in slice.
	fn get_range(&self, index: Self::Index) -> HistoriedValue<Range<usize>, S>;
	/// Get the range from a slice without using a `LinearStorageRange` instance.
	fn get_range_from_slice(slice: &'a [u8], index: Self::Index) -> Option<HistoriedValue<Range<usize>, S>> {
		Self::from_slice_ref(slice).map(|inner| inner.get_range(index))
	}
}

/// Iterator over the internal index stored in a backend stoarge.
/// This allow to iterate over value without relying on unsafe code,
/// since accessing an item with internal state should be cheap.
pub struct RevIter<'a, V, S, D: LinearStorage<V, S>>(
	&'a D,
	Option<D::Index>,
	sp_std::marker::PhantomData<(V, S)>,
);

impl<'a, V, S, D: LinearStorage<V, S>>  Iterator for RevIter<'a, V, S, D> {
	type Item = <D as LinearStorage<V, S>>::Index;
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(index) = self.1.take() {
			self.1 = self.0.previous_index(index);
			Some(index)
		} else {
			None
		}
	}
}

/// Entry for a backend.
///
/// Actual change get commited on drop.
pub struct Entry<'a, V, S, D: LinearStorage<V, S>> {
	value: Option<HistoriedValue<V, S>>,
	index: Option<D::Index>,
	storage: &'a mut D,
	changed: bool,
	insert: bool,
}

impl<'a, V, S, D: LinearStorage<V, S>> Entry<'a, V, S, D> {
	/// Similar to `Vaccant` enum of rust std lib flavored entries.
	pub fn is_vaccant(&self) -> bool {
		self.insert
	}
	/// Access current value
	pub fn value(&self) -> Option<&HistoriedValue<V, S>> {
		self.value.as_ref()
	}
	/// Change current value.
	pub fn and_modify<F>(mut self, f: impl FnOnce(&mut HistoriedValue<V, S>)) -> Self {
		self.value.as_mut().map(f);
		self.changed |= self.value.is_some();
		self
	}
	/// Context a value for vaccant entry.
	pub fn or_insert(mut self, default: HistoriedValue<V, S>) -> Self {
		if self.value.is_none() {
			self.changed = true;
			self.value = Some(default);
		}
		self
	}
	/// Lazy `or_insert`.
	pub fn or_insert_with(mut self, default: impl FnOnce() -> HistoriedValue<V, S>) -> Self {
		if self.value.is_none() {
			self.changed = true;
			self.value = Some(default());
		}
		self
	}
	/// Remove entry.
	pub fn and_delete(mut self) -> Self {
		if self.value.is_some() {
			self.changed = true;
			self.value = None;
		}
		self
	}
}

impl<'a, V, S, D: LinearStorage<V, S>> Drop for Entry<'a, V, S, D> {
	fn drop(&mut self) {
		if self.changed {
			if let Some(change) = self.value.take() {
				if let Some(index) = self.index {
					if self.insert {
						self.storage.insert(index, change);
					} else {
						self.storage.emplace(index, change);
					}
				} else {
					self.storage.push(change);
				}
			} else {
				if self.changed && !self.insert {
					if let Some(index) = self.index {
						self.storage.remove(index);
					}
				}
			}
		}
	}
}


#[cfg(test)]
mod test {
	use super::*;
	pub(crate) type State = u64;
	pub(crate) type Value = Vec<u8>;

	// basic test for linear storage usage
	pub(crate) fn test_linear_storage<L: LinearStorage<Value, State> + Clone>(storage: &mut L) {
		// empty storage
		assert!(storage.pop().is_none());
		assert!(storage.get_state_lookup(0).is_none());
		assert!(storage.get_state_lookup(10).is_none());
		assert!(storage.get_lookup(0).is_none());
		assert!(storage.get_lookup(10).is_none());
		assert!(storage.len() == 0);
		storage.truncate(0);
		storage.truncate(10);
		storage.truncate_until(0);
		storage.truncate_until(10);
		// single element
		let h: HistoriedValue<Value, State> = (vec![5], 5).into();
		storage.push(h.clone());
		assert_eq!(storage.get_state_lookup(0), Some(5));
		assert_eq!(storage.get_lookup(0), Some(h.clone()));
		assert!(storage.get_lookup(1).is_none());
		let h: HistoriedValue<Value, State> = (vec![2], 2).into();
		storage.insert_lookup(0, h);
		assert_eq!(storage.get_state_lookup(0), Some(2));
		assert_eq!(storage.get_state_lookup(1), Some(5));
		storage.remove_lookup(0);
		assert_eq!(storage.get_state_lookup(0), Some(5));
		assert!(storage.get_lookup(1).is_none());
		storage.clear();
		for i in 0usize..30 {
			let h: HistoriedValue<Value, State> = (vec![i as u8], i as State).into();
			storage.push(h);
		}
		for i in 0usize..30 {
			assert_eq!(storage.get_state_lookup(i), Some(i as State));
		}
		for i in 0usize..30 {
			let mut storage2 = storage.clone();
			storage2.truncate(i);
			for j in 0usize..i {
				assert_eq!(storage2.get_state_lookup(j), Some(j as State));
			}
			for j in i..30 {
				assert_eq!(storage2.get_state_lookup(j), None);
			}
		}
		for i in 0usize..30 {
			let mut storage2 = storage.clone();
			storage2.truncate_until(i);
			for j in 0usize..30 - i {
				assert_eq!(storage2.get_state_lookup(j), Some(j as State + i as State));
			}
			for j in 30 - i..30 {
				assert_eq!(storage2.get_state_lookup(j), None);
			}
		}
		for i in 0usize..30 {
			let mut storage2 = storage.clone();
			storage2.remove_lookup(i);
			for j in 0usize..i {
				assert_eq!(storage2.get_state_lookup(j), Some(j as State));
			}
			for j in i..29 {
				assert_eq!(storage2.get_state_lookup(j), Some(j as State + 1));
			}
			assert_eq!(storage2.get_state_lookup(29), None);
		}

		storage.truncate_until(5);
		for i in 0usize..25 {
			assert_eq!(storage.get_state_lookup(i), Some(i as State + 5));
		}
		assert!(storage.get_lookup(25).is_none());
		storage.truncate(20);
		for i in 0usize..20 {
			assert_eq!(storage.get_state_lookup(i), Some(i as State + 5));
		}
		assert!(storage.get_lookup(20).is_none());
		storage.remove_lookup(10);
		for i in 0usize..10 {
			assert_eq!(storage.get_state_lookup(i), Some(i as State + 5));
		}
		for i in 10usize..19 {
			assert_eq!(storage.get_state_lookup(i), Some(i as State + 6));
		}
		assert!(storage.get_lookup(19).is_none());
		storage.emplace_lookup(18, (vec![1], 1).into());
		storage.emplace_lookup(17, (vec![2], 2).into());
		storage.emplace_lookup(0, (vec![3], 3).into());
		assert_eq!(storage.get_state_lookup(18), Some(1 as State));
		assert_eq!(storage.get_state_lookup(17), Some(2 as State));
		assert_eq!(storage.get_state_lookup(0), Some(3 as State));
	}
}
