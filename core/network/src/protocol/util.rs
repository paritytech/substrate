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
	/// Create a new `LruHashSet` with the given (exclusive) limit.
	pub(crate) fn new(limit: NonZeroUsize) -> Self {
		Self { set: LinkedHashSet::new(), limit }
	}

	/// Insert element into the set.
	///
	/// Returns `true` if this is a new element to the set, `false` otherwise.
	/// Maintains the limit of the set by removing the oldest entry if necessary.
	/// Inserting the same element will update its LRU position.
	pub(crate) fn insert(&mut self, e: T) -> bool {
		if self.set.insert(e) {
			if self.set.len() == usize::from(self.limit) {
				self.set.pop_front(); // remove oldest entry
			}
			return true
		}
		false
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn maintains_limit() {
		let three = NonZeroUsize::new(3).unwrap();
		let mut set = LruHashSet::<u8>::new(three);

		// First element.
		assert!(set.insert(1));
		assert_eq!(vec![&1], set.set.iter().collect::<Vec<_>>());

		// Second element.
		assert!(set.insert(2));
		assert_eq!(vec![&1, &2], set.set.iter().collect::<Vec<_>>());

		// Inserting the same element updates its LRU position.
		assert!(!set.insert(1));
		assert_eq!(vec![&2, &1], set.set.iter().collect::<Vec<_>>());

		// We reached the limit. The next element forces the oldest one out.
		assert!(set.insert(3));
		assert_eq!(vec![&1, &3], set.set.iter().collect::<Vec<_>>());
	}
}
