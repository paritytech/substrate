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

/// Data encoded in a byte buffer, no unserialized
/// stractures.
pub mod encoded_array;

/// Content can be split between multiple nodes.
pub mod nodes;

// TODO this implementation uses a index and does not allow
// performant implementation, it should (at least when existing
// value) use a associated type index depending on backend
// (slice index of encoded array, pointer of in_memory, pointer
// of node inner value for nodes). Also not puting value in memory.
pub struct Entry<'a, V, S, D: LinearStorage<V, S>> {
	value: Option<HistoriedValue<V, S>>,
	index: usize,
	storage: &'a mut D,
	changed: bool,
	insert: bool,
}

impl<'a, V, S, D: LinearStorage<V, S>> Entry<'a, V, S, D> {
	/// ~ Vaccant enum of rust std lib.
	/// Occupied is the negation of this.
	pub fn is_vaccant(&self) -> bool {
		self.insert
	}
	/// Access current value
	pub fn value(&self) -> Option<&HistoriedValue<V, S>> {
		self.value.as_ref()
	}
	/// Change value.
	pub fn and_modify<F>(mut self, f: impl FnOnce(&mut HistoriedValue<V, S>)) -> Self {
		self.value.as_mut().map(f);
		self.changed |= self.value.is_some();
		self
	}
	/// Init a value for vaccant entry.
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

impl<'a, V, S, D: LinearStorage<V, S>> Drop for Entry<'a, V, S, D>
{
	fn drop(&mut self) {
		if self.changed {
			if let Some(change) = self.value.take() {
				if self.insert {
					self.storage.insert_lookup(self.index, change);
				} else {
					self.storage.emplace_lookup(self.index, change);
				}
			} else {
				if self.changed && !self.insert {
					self.storage.remove_lookup(self.index);
				}
			}
		}
	}
}
#[derive(Copy, Clone)]
pub struct DummyIndex;
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

/// Backend for linear storage.
pub trait LinearStorage<V, S>: InitFrom {
	/// Internal index over a location in the storage.
	/// Implementations need to provide direct to data
	/// with it.
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
	/// Entry. TODO Entry on linear is not very interesting (consider removal).
	/// Aka either delete or use Index internaly.
	fn entry<'a>(&'a mut self, index: usize) -> Entry<'a, V, S, Self> {
		let value = self.lookup(index).map(|index| self.get(index));
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
	fn pop(&mut self) -> Option<HistoriedValue<V, S>>;
	fn clear(&mut self);
	fn truncate(&mut self, at: usize);
	/// This can be slow, only define in migrate.
	fn emplace(&mut self, index: Self::Index, value: HistoriedValue<V, S>);
	/// Emplace with lookup.
	fn emplace_lookup(&mut self, at: usize, value: HistoriedValue<V, S>) {
		self.lookup(at).map(|index| self.emplace(index, value));
	}
}

/// Backend for linear storage with inmemory reference.
pub trait LinearStorageSlice<V: AsRef<[u8]> + AsMut<[u8]>, S>: LinearStorage<V, S> {
	/// Unchecked access to value slice and state.
	fn get_slice(&self, index: Self::Index) -> HistoriedValue<&[u8], S>;
	/// Unchecked mutable access to mutable value slice and state.
	fn get_slice_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut [u8], S>;
}

/// Backend for linear storage with inmemory reference.
pub trait LinearStorageMem<V, S>: LinearStorage<V, S> {
	/// Unchecked access to value pointer and state.
	fn get_ref(&self, index: Self::Index) -> HistoriedValue<&V, S>;
	/// Unchecked access to value mutable pointer and state.
	fn get_ref_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut V, S>;
}

pub trait LinearStorageRange<V, S>: LinearStorage<V, S> {
	// TODO rename to use get_range as get_range_from_slice also try again pure slice implementation.
	/// Array like get.
	fn get_range(&self, index: Self::Index) -> HistoriedValue<Range<usize>, S>;
	fn get_range_from_slice(slice: &[u8], index: Self::Index) -> Option<HistoriedValue<Range<usize>, S>> {
		Self::from_slice(slice).map(|inner|	inner.get_range(index))
	}
	fn from_slice(slice: &[u8]) -> Option<Self>;
}

#[cfg(test)]
mod test {
	use super::*;
	pub(crate) type State = u32;
	pub(crate) type Value = Vec<u8>;

	// basic test for linear storage usage
	pub(crate) fn test_linear_storage<L: LinearStorage<Value, State>>(storage: &mut L) {
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
