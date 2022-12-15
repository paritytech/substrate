// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::{
	collections::HashMap,
	sync::{
		atomic::{AtomicIsize, Ordering as AtomicOrdering},
		Arc,
	},
};

/// Something that can report its size.
pub trait Size {
	fn size(&self) -> usize;
}

/// Map with size tracking.
///
/// Size reported might be slightly off and only approximately true.
#[derive(Debug)]
pub struct TrackedMap<K, V> {
	index: Arc<RwLock<HashMap<K, V>>>,
	bytes: AtomicIsize,
	length: AtomicIsize,
}

impl<K, V> Default for TrackedMap<K, V> {
	fn default() -> Self {
		Self { index: Arc::new(HashMap::default().into()), bytes: 0.into(), length: 0.into() }
	}
}

impl<K, V> TrackedMap<K, V> {
	/// Current tracked length of the content.
	pub fn len(&self) -> usize {
		std::cmp::max(self.length.load(AtomicOrdering::Relaxed), 0) as usize
	}

	/// Current sum of content length.
	pub fn bytes(&self) -> usize {
		std::cmp::max(self.bytes.load(AtomicOrdering::Relaxed), 0) as usize
	}

	/// Lock map for read.
	pub fn read(&self) -> TrackedMapReadAccess<K, V> {
		TrackedMapReadAccess { inner_guard: self.index.read() }
	}

	/// Lock map for write.
	pub fn write(&self) -> TrackedMapWriteAccess<K, V> {
		TrackedMapWriteAccess {
			inner_guard: self.index.write(),
			bytes: &self.bytes,
			length: &self.length,
		}
	}
}

impl<K: Clone, V: Clone> TrackedMap<K, V> {
	/// Clone the inner map.
	pub fn clone_map(&self) -> HashMap<K, V> {
		self.index.read().clone()
	}
}

pub struct TrackedMapReadAccess<'a, K, V> {
	inner_guard: RwLockReadGuard<'a, HashMap<K, V>>,
}

impl<'a, K, V> TrackedMapReadAccess<'a, K, V>
where
	K: Eq + std::hash::Hash,
{
	/// Returns true if map contains key.
	pub fn contains_key(&self, key: &K) -> bool {
		self.inner_guard.contains_key(key)
	}

	/// Returns reference to the contained value by key, if exists.
	pub fn get(&self, key: &K) -> Option<&V> {
		self.inner_guard.get(key)
	}

	/// Returns iterator over all values.
	pub fn values(&self) -> std::collections::hash_map::Values<K, V> {
		self.inner_guard.values()
	}
}

pub struct TrackedMapWriteAccess<'a, K, V> {
	bytes: &'a AtomicIsize,
	length: &'a AtomicIsize,
	inner_guard: RwLockWriteGuard<'a, HashMap<K, V>>,
}

impl<'a, K, V> TrackedMapWriteAccess<'a, K, V>
where
	K: Eq + std::hash::Hash,
	V: Size,
{
	/// Insert value and return previous (if any).
	pub fn insert(&mut self, key: K, val: V) -> Option<V> {
		let new_bytes = val.size();
		self.bytes.fetch_add(new_bytes as isize, AtomicOrdering::Relaxed);
		self.length.fetch_add(1, AtomicOrdering::Relaxed);
		self.inner_guard.insert(key, val).map(|old_val| {
			self.bytes.fetch_sub(old_val.size() as isize, AtomicOrdering::Relaxed);
			self.length.fetch_sub(1, AtomicOrdering::Relaxed);
			old_val
		})
	}

	/// Remove value by key.
	pub fn remove(&mut self, key: &K) -> Option<V> {
		let val = self.inner_guard.remove(key);
		if let Some(size) = val.as_ref().map(Size::size) {
			self.bytes.fetch_sub(size as isize, AtomicOrdering::Relaxed);
			self.length.fetch_sub(1, AtomicOrdering::Relaxed);
		}
		val
	}

	/// Returns mutable reference to the contained value by key, if exists.
	pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
		self.inner_guard.get_mut(key)
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	impl Size for i32 {
		fn size(&self) -> usize {
			*self as usize / 10
		}
	}

	#[test]
	fn basic() {
		let map = TrackedMap::default();
		map.write().insert(5, 10);
		map.write().insert(6, 20);

		assert_eq!(map.bytes(), 3);
		assert_eq!(map.len(), 2);

		map.write().insert(6, 30);

		assert_eq!(map.bytes(), 4);
		assert_eq!(map.len(), 2);

		map.write().remove(&6);
		assert_eq!(map.bytes(), 1);
		assert_eq!(map.len(), 1);
	}
}
