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

use linked_hash_set::LinkedHashSet;
use std::{hash::Hash, num::NonZeroUsize};

/// Wrapper around `LinkedHashSet` which grows bounded.
///
/// In the limit, for each element inserted the oldest existing element will be removed.
#[derive(Debug, Clone)]
pub(crate) struct LruHashSet<T: Hash + Eq> {
	set: LinkedHashSet<T>,
	limit: NonZeroUsize
}

impl<T: Hash + Eq> LruHashSet<T> {
	/// Create a new `LruHashSet` with the given limit.
	pub(crate) fn new(limit: NonZeroUsize) -> Self {
		Self { set: LinkedHashSet::new(), limit }
	}

	/// Insert element into the set.
	///
	/// Returns `true` if this is a new element to the set, `false` otherwise.
	/// Maintains the limit of the set by removing the oldest entry if necessary.
	pub(crate) fn insert(&mut self, e: T) -> bool {
		if self.set.len() == usize::from(self.limit) {
			if self.set.contains(&e) {
				return false
			}
			self.set.pop_front(); // remove oldest entry
		}
		self.set.insert(e)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn maintains_limit() {
		let two = NonZeroUsize::new(2).unwrap();
		let mut set = LruHashSet::new(two);

		// First element.
		assert!(set.insert(1u8));
		assert_eq!(1, set.set.len());
		assert!(set.set.contains(&1));

		// Inserting the same element multiple times has no effect.
		assert!(!set.insert(1u8));
		assert_eq!(1, set.set.len());
		assert!(set.set.contains(&1));

		// Second element.
		assert!(set.insert(2u8));
		assert_eq!(2, set.set.len());
		assert!(set.set.contains(&1));
		assert!(set.set.contains(&2));

		// Inserting the same element multiple times has no effect.
		assert!(!set.insert(2u8));
		assert_eq!(2, set.set.len());
		assert!(set.set.contains(&1));
		assert!(set.set.contains(&2));

		// We reached the limit. The next element forces the oldest one out.
		assert!(set.insert(3u8));
		assert_eq!(2, set.set.len());
		assert!(set.set.contains(&2));
		assert!(set.set.contains(&3));

		// Inserting the same element multiple times has no effect.
		assert!(!set.insert(3u8));
		assert_eq!(2, set.set.len());
		assert!(set.set.contains(&2));
		assert!(set.set.contains(&3));
	}
}
