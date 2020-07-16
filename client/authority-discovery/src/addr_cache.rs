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

use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};
use std::{
	clone::Clone,
	cmp::{Eq, Ord, PartialEq},
	collections::BTreeMap,
	convert::AsRef,
	hash::Hash,
};

/// The maximum number of authority connections initialized through the authority discovery module.
///
/// In other words the maximum size of the `authority` peer set priority group.
const MAX_NUM_AUTHORITY_CONN: usize = 10;

/// Cache of Multiaddresses of authority nodes or their sentry nodes.
//
// The network peerset interface for priority groups lets us only set an entire group, but we
// retrieve the addresses of other authorities one by one from the network. To use the peerset
// interface we need to cache the addresses and always overwrite the entire peerset priority
// group. To ensure this map doesn't grow indefinitely `purge_old_authorities_from_cache`
// function is called each time we add a new entry.
pub(super) struct AddrCache<Id, Addr> {
	cache: BTreeMap<Id, Vec<Addr>>,

	/// Random number to seed address selection RNG.
	///
	/// A node should only try to connect to a subset of all authorities. To choose this subset one
	/// uses randomness. The choice should differ between nodes to prevent hot spots, but not within
	/// each node between each update to prevent connection churn. Thus before each selection we
	/// seed an RNG with the same seed.
	rand_addr_selection_seed: u64,
}

impl<Id, Addr> AddrCache<Id, Addr>
where
	Id: Clone + Eq + Hash + Ord,
	Addr: Clone + PartialEq + AsRef<[u8]>,
{
	pub fn new() -> Self {
		AddrCache {
			cache: BTreeMap::new(),
			rand_addr_selection_seed: rand::thread_rng().gen(),
		}
	}

	pub fn insert(&mut self, id: Id, mut addresses: Vec<Addr>) {
		if addresses.is_empty() {
			return;
		}

		addresses.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));
		self.cache.insert(id, addresses);
	}

	/// Returns the number of authority IDs in the cache.
	pub fn num_ids(&self) -> usize {
		self.cache.len()
	}

	// Each node should connect to a subset of all authorities. In order to prevent hot spots, this
	// selection is based on randomness. Selecting randomly each time we alter the address cache
	// would result in connection churn. To reduce this churn a node generates a seed on startup and
	// uses this seed for a new rng on each update. (One could as well use ones peer id as a seed.
	// Given that the peer id is publicly known, it would make this process predictable by others,
	// which might be used as an attack.)
	pub fn get_subset(&self) -> Vec<Addr> {
		let mut rng = StdRng::seed_from_u64(self.rand_addr_selection_seed);

		let mut addresses = self
			.cache
			.iter()
			.map(|(_peer_id, addresses)| {
				addresses
					.choose(&mut rng)
					.expect("an empty address vector is never inserted into the cache")
			})
			.cloned()
			.collect::<Vec<Addr>>();

		addresses.dedup();
		addresses.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));

		addresses
			.choose_multiple(&mut rng, MAX_NUM_AUTHORITY_CONN)
			.cloned()
			.collect()
	}

	pub fn retain_ids(&mut self, ids: &Vec<Id>) {
		let to_remove = self
			.cache
			.iter()
			.filter(|(id, _addresses)| !ids.contains(id))
			.map(|entry| entry.0)
			.cloned()
			.collect::<Vec<Id>>();

		for key in to_remove {
			self.cache.remove(&key);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use quickcheck::{QuickCheck, TestResult};

	#[test]
	fn returns_addresses_of_same_authorities_on_repeated_calls() {
		fn property(input: Vec<(u32, Vec<String>)>) -> TestResult {
			// Expect less than 1000 authorities.
			if input.len() > 1000 {
				return TestResult::discard();
			}

			// Expect less than 100 addresses per authority.
			for i in &input {
				if i.1.len() > 100 {
					return TestResult::discard();
				}
			}

			let mut c = AddrCache::new();

			for (id, addresses) in input {
				c.insert(id, addresses);
			}

			let result = c.get_subset();
			assert!(result.len() <= MAX_NUM_AUTHORITY_CONN);

			for _ in 1..100 {
				assert_eq!(c.get_subset(), result);
			}

			TestResult::passed()
		}

		QuickCheck::new()
			.max_tests(10)
			.quickcheck(property as fn(Vec<(u32, Vec<String>)>) -> TestResult)
	}

	#[test]
	fn returns_same_addresses_of_first_authority_when_second_authority_changes() {
		let mut c = AddrCache::new();

		// Insert addresses of first authority.
		let addresses = (1..100)
			.map(|i| format!("{:?}", i))
			.collect::<Vec<String>>();
		c.insert(1, addresses);
		let first_subset = c.get_subset();
		assert_eq!(1, first_subset.len());

		// Insert address of second authority.
		c.insert(2, vec!["a".to_string()]);
		let second_subset = c.get_subset();
		assert_eq!(2, second_subset.len());

		// Expect same address of first authority.
		assert!(second_subset.contains(&first_subset[0]));

		// Alter address of second authority.
		c.insert(2, vec!["b".to_string()]);
		let second_subset = c.get_subset();
		assert_eq!(2, second_subset.len());

		// Expect same address of first authority.
		assert!(second_subset.contains(&first_subset[0]));
	}

	#[test]
	fn retains_only_entries_of_provided_ids() {
		let mut cache = AddrCache::new();

		cache.insert(1, vec![vec![10]]);
		cache.insert(2, vec![vec![20]]);
		cache.insert(3, vec![vec![30]]);

		cache.retain_ids(&vec![1, 3]);

		let mut subset = cache.get_subset();
		subset.sort();

		assert_eq!(vec![vec![10], vec![30]], subset);
	}
}
