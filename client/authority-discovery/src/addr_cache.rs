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

#![warn(missing_docs)]

use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};
use std::collections::HashMap;

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
	cache: HashMap<Id, Vec<Addr>>,

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
	// TODO: Import std above.
	Id: std::cmp::Eq + std::hash::Hash,
	Addr: std::clone::Clone + std::cmp::PartialEq + std::convert::AsRef<[u8]>,
{
	pub fn new() -> Self {
		AddrCache {
			cache: HashMap::new(),
			rand_addr_selection_seed: rand::thread_rng().gen(),
		}
	}

	pub fn insert(&mut self, id: Id, mut addresses: Vec<Addr>) {
		// TODO: Handle unwrap
		addresses.sort_by(|a, b| a.as_ref().partial_cmp(b.as_ref()).unwrap());
		self.cache.insert(id, addresses);
	}

	// Each node should connect to a subset of all authorities. In order to prevent hot spots, this
	// selection is based on randomness. Selecting randomly each time we change the address cache
	// would result in connection churn. Instead a node generates a seed on startup and uses this
	// seed for a new rng on each update. (One could as well use ones peer id as a seed. Given that
	// the peer id is publicly known, it would make this process predictable by others, which might
	// be used as an attack.)
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
		// TODO: Handle unwrap
		addresses.sort_by(|a, b| a.as_ref().partial_cmp(b.as_ref()).unwrap());

		addresses
			.choose_multiple(&mut rng, MAX_NUM_AUTHORITY_CONN)
			.cloned()
			.collect()
	}

	pub fn retain_ids(&mut self, ids: &Vec<Id>) {
		self.cache.retain(|id, _addresses| ids.contains(id))
	}
}
