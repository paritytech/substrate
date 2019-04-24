// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
