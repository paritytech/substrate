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

use libp2p::core::multiaddr::{Multiaddr, Protocol};
use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};
use std::{
	clone::Clone,
	collections::{BTreeMap, HashMap},
	convert::AsRef,
};

use sp_authority_discovery::AuthorityId;
use sc_network::PeerId;

/// The maximum number of authority connections initialized through the authority discovery module.
///
/// In other words the maximum size of the `authority` peer set priority group.
const MAX_NUM_AUTHORITY_CONN: usize = 10;

/// Cache of Multiaddresses of authority nodes or their sentry nodes.
pub(super) struct AddrCache {
	authority_id_to_addresses: BTreeMap<AuthorityId, Vec<Multiaddr>>,
	// TODO: Make sure to clean this one up on authority set change. As in add tests!
	peer_id_to_authority_id: HashMap<PeerId, AuthorityId>,

	/// Random number to seed address selection RNG.
	///
	/// A node should only try to connect to a subset of all authorities. To choose this subset one
	/// uses randomness. The choice should differ between nodes to prevent hot spots, but not within
	/// each node between each update to prevent connection churn. Thus before each selection we
	/// seed an RNG with the same seed.
	//
	// TODO: Probably better to use something larger.
	rand_addr_selection_seed: u64,
}

impl AddrCache {
	pub fn new() -> Self {
		AddrCache {
			authority_id_to_addresses: BTreeMap::new(),
			peer_id_to_authority_id: HashMap::new(),
			rand_addr_selection_seed: rand::thread_rng().gen(),
		}
	}

	pub fn insert(&mut self, authority_id: AuthorityId, mut addresses: Vec<Multiaddr>) {
		if addresses.is_empty() {
			return;
		}

		// Insert into `self.peer_id_to_authority_id`.
		let peer_ids = addresses.iter()
			.map(|a| peer_id_from_multiaddr(a))
			.filter_map(|peer_id| peer_id);
		for peer_id in  peer_ids {
			self.peer_id_to_authority_id.insert(peer_id, authority_id.clone());
		}

		// Insert into `self.authority_id_to_addresses`.
		addresses.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));
		self.authority_id_to_addresses.insert(authority_id, addresses);
	}

	/// Returns the number of authority IDs in the cache.
	pub fn num_ids(&self) -> usize {
		self.authority_id_to_addresses.len()
	}

	// TODO: How about authority_id_to_address instead?
	pub fn get_addresses(&self, id: &AuthorityId) -> Option<&Vec<Multiaddr>> {
		self.authority_id_to_addresses.get(&id)
	}

	// Each node should connect to a subset of all authorities. In order to prevent hot spots, this
	// selection is based on randomness. Selecting randomly each time we alter the address cache
	// would result in connection churn. To reduce this churn a node generates a seed on startup and
	// uses this seed for a new rng on each update. (One could as well use ones peer id as a seed.
	// Given that the peer id is publicly known, it would make this process predictable by others,
	// which might be used as an attack.)
	//
	// Note: This is still subject to churn when the number of authorities in
	// `self.authority_id_to_addresses` changes.
	pub fn get_subset(&self) -> Vec<Multiaddr> {
		let mut rng = StdRng::seed_from_u64(self.rand_addr_selection_seed);

		let mut addresses = self
			.authority_id_to_addresses
			.iter()
			.map(|(_authority_id, addresses)| {
				addresses
					.choose(&mut rng)
					// TODO: Reassure that this assumption is correct.
					.expect("an empty address vector is never inserted into the cache")
			})
			.cloned()
			.collect::<Vec<Multiaddr>>();

		addresses.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));
		addresses.dedup();

		addresses
			.choose_multiple(&mut rng, MAX_NUM_AUTHORITY_CONN)
			.cloned()
			.collect()
	}

	pub fn retain_ids(&mut self, authority_ids: &Vec<AuthorityId>) {
		// The below logic could be replaced by `BtreeMap::drain_filter` once it stabilized.
		let authority_ids_to_remove = self.authority_id_to_addresses.iter()
			.filter(|(id, _addresses)| !authority_ids.contains(id))
			.map(|entry| entry.0)
			.cloned()
			.collect::<Vec<AuthorityId>>();

		for authority_id_to_remove in authority_ids_to_remove {
			// Remove other entries from `self.authority_id_to_addresses`.
			let addresses = self.authority_id_to_addresses.remove(&authority_id_to_remove);

			// Remove other entries from `self.peer_id_to_authority_id`.
			let peer_ids = addresses.iter()
				.flatten()
				.map(|a| peer_id_from_multiaddr(a))
				.filter_map(|peer_id| peer_id);
			for peer_id in peer_ids {
				if let Some(id) = self.peer_id_to_authority_id.remove(&peer_id) {
					debug_assert_eq!(authority_id_to_remove, id);
				}
			}
		}
	}
}

fn peer_id_from_multiaddr(addr: &Multiaddr) -> Option<PeerId> {
	addr.iter().last().and_then(|protocol| if let Protocol::P2p(multihash) = protocol {
		PeerId::from_multihash(multihash).ok()
	} else {
		None
	})
}

#[cfg(test)]
mod tests {
	use super::*;

	use libp2p::multihash;
	use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

	use sp_authority_discovery::{AuthorityId, AuthorityPair};
	use sp_core::crypto::Pair;

	#[derive(Clone, Debug)]
	struct TestAuthorityId(AuthorityId);

	impl Arbitrary for TestAuthorityId {
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			let seed: [u8; 32] = g.gen();
			TestAuthorityId(AuthorityPair::from_seed_slice(&seed).unwrap().public())
		}
	}

	#[derive(Clone, Debug)]
	struct TestMultiaddr(Multiaddr);

	impl Arbitrary for TestMultiaddr {
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			let seed: [u8; 32] = g.gen();
			let peer_id = PeerId::from_multihash(
				multihash::wrap(multihash::Code::Sha2_256, &seed)
			).unwrap();
			let multiaddr = "/ip6/2001:db8:0:0:0:0:0:2/tcp/30333".parse::<Multiaddr>()
				.unwrap()
				.with(Protocol::P2p(peer_id.into()));

			TestMultiaddr(multiaddr)
		}
	}

	#[test]
	fn returns_addresses_of_same_authorities_on_repeated_calls() {
		fn property(input: Vec<(TestAuthorityId, Vec<TestMultiaddr>)>) -> TestResult {
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
				c.insert(id.0, addresses.into_iter().map(|a| a.0).collect());
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
			.quickcheck(property as fn(_) -> TestResult)
	}

	#[test]
	fn returns_same_addresses_of_first_authority_when_second_authority_changes() {
		fn property(
			first: (TestAuthorityId, Vec<TestMultiaddr>),
			second: (TestAuthorityId, Vec<TestMultiaddr>),
			second_altered_addresses: Vec<TestMultiaddr>,
		) -> TestResult {
			// Unwrap from `TestXXX` types.
			let first = ((first.0).0, first.1.into_iter().map(|a| a.0).collect::<Vec<_>>());
			let second = ((second.0).0, second.1.into_iter().map(|a| a.0).collect::<Vec<_>>());
			let second_altered_addresses = second_altered_addresses.into_iter()
				.map(|a| a.0)
				.collect::<Vec<_>>();

			if first.1.is_empty() || second.1.is_empty() || second_altered_addresses.is_empty() {
				return TestResult::discard();
			}

			let mut c = AddrCache::new();

			// Insert addresses of first and second authority.
			c.insert(first.0.clone(), first.1.clone());
			c.insert(second.0.clone(), second.1);
			assert_eq!(2, c.authority_id_to_addresses.len());

			let first_subset = c.get_subset();
			let first_subset_str = format!("{:?}", first_subset);
			assert_eq!(2, first_subset.len());
			let chosen_first_authority_address = first_subset.into_iter()
				.filter(|a| first.1.contains(a))
				.collect::<Vec<_>>()
				.pop()
				.expect("Subset to contain one address of first authority.");

			// Alter address of second authority.
			c.insert(second.0.clone(), second_altered_addresses);
			assert_eq!(2, c.authority_id_to_addresses.len());

			let second_subset = c.get_subset();
			assert_eq!(2, second_subset.len());

			assert!(
				second_subset.contains(&chosen_first_authority_address),
				"\nExpect second subset {:?} \nto contain same chosen address {:?} \nof first authority {:?} \nas in previous subset {:?}.\n",
				second_subset, chosen_first_authority_address, first.1, first_subset_str,
			);

			TestResult::passed()
		}

		QuickCheck::new()
			.max_tests(10)
			.quickcheck(property as fn(_, _, _) -> TestResult)
	}

	#[test]
	fn retains_only_entries_of_provided_ids() {
		fn property(
			first: (TestAuthorityId, TestMultiaddr),
			second: (TestAuthorityId, TestMultiaddr),
			third: (TestAuthorityId, TestMultiaddr),
		) -> TestResult {
			let first: (AuthorityId, Multiaddr) = ((first.0).0, (first.1).0);
			let second: (AuthorityId, Multiaddr) = ((second.0).0, (second.1).0);
			let third: (AuthorityId, Multiaddr) = ((third.0).0, (third.1).0);

			let mut cache = AddrCache::new();

			cache.insert(first.0.clone(), vec![first.1.clone()]);
			cache.insert(second.0.clone(), vec![second.1.clone()]);
			cache.insert(third.0.clone(), vec![third.1.clone()]);

			let subset = cache.get_subset();
			assert!(
				subset.contains(&first.1) && subset.contains(&second.1) && subset.contains(&third.1),
				"Expect initial subset to contain all authorities.",
			);

			cache.retain_ids(&vec![first.0, second.0]);

			let subset = cache.get_subset();
			assert!(
				subset.contains(&first.1) || subset.contains(&second.1),
				"Expected both first and second authority."
			);
			assert!(!subset.contains(&third.1), "Did not expect third authority");

			// TODO: Also ensure the peerid -> authority id matching is cleaned up.

			TestResult::passed()
		}

		QuickCheck::new()
			.max_tests(10)
			.quickcheck(property as fn(_, _, _) -> TestResult)
	}
}
