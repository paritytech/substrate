// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use libp2p::core::multiaddr::{Multiaddr, Protocol};

use lru::LruCache;
use sc_network::PeerId;
use sp_authority_discovery::AuthorityId;
use std::collections::{hash_map::Entry, HashMap, HashSet};

/// Cache for [`AuthorityId`] -> [`Vec<Multiaddr>`] and [`PeerId`] -> [`AuthorityId`] mappings.
pub(super) struct AddrCache {
	/// The addresses found in `authority_id_to_addresses` are guaranteed to always match
	/// the peerids found in `peer_id_to_authority_id`. In other words, these two maps
	/// are similar to a bi-directional map. As both are lru maps, we ensure that only inserts
	/// update the position in the lru and any other access doesn't update the position of a
	/// requested item.
	authority_id_to_addresses: LruCache<AuthorityId, HashSet<Multiaddr>>,
	peer_id_to_authority_id: HashMap<PeerId, HashSet<AuthorityId>>,
	/// The maximum number of authority ids that should be cached.
	max_authority_ids: usize,
}

impl AddrCache {
	pub fn new() -> Self {
		AddrCache {
			authority_id_to_addresses: LruCache::unbounded(),
			peer_id_to_authority_id: HashMap::default(),
			max_authority_ids: 0,
		}
	}

	/// Inserts the given [`AuthorityId`] and [`Vec<Multiaddr>`] pair for future lookups by
	/// [`AuthorityId`] or [`PeerId`].
	pub fn insert(&mut self, authority_id: AuthorityId, addresses: Vec<Multiaddr>) {
		let addresses = addresses.into_iter().collect::<HashSet<_>>();
		let peer_ids = addresses_to_peer_ids(&addresses);

		let old_addresses = self.authority_id_to_addresses.put(authority_id.clone(), addresses);
		let old_peer_ids = addresses_to_peer_ids(&old_addresses.unwrap_or_default());

		// Add the new peer ids
		peer_ids.difference(&old_peer_ids).for_each(|new_peer_id| {
			self.peer_id_to_authority_id
				.entry(*new_peer_id)
				.or_default()
				.insert(authority_id.clone());
		});

		// Remove the old peer ids
		self.remove_authority_id_from_peer_ids(&authority_id, old_peer_ids.difference(&peer_ids));

		while self.authority_id_to_addresses.len() > self.max_authority_ids {
			match self.authority_id_to_addresses.pop_lru() {
				Some((authority_id, addresses)) => {
					self.remove_authority_id_from_peer_ids(
						&authority_id,
						addresses_to_peer_ids(&addresses).iter(),
					);
				},
				None => break,
			}
		}
	}

	/// Remove the given `authority_id` from the `peer_id` to `authority_ids` mapping.
	///
	/// If a `peer_id` doesn't have any `authority_id` assigned anymore, it is removed.
	fn remove_authority_id_from_peer_ids<'a>(
		&mut self,
		authority_id: &AuthorityId,
		peer_ids: impl Iterator<Item = &'a PeerId>,
	) {
		peer_ids.for_each(|peer_id| {
			if let Entry::Occupied(mut e) = self.peer_id_to_authority_id.entry(*peer_id) {
				e.get_mut().remove(authority_id);

				// If there are no more entries, remove the peer id.
				if e.get().is_empty() {
					e.remove();
				}
			}
		})
	}

	/// Returns the number of authority IDs in the cache.
	pub fn num_authority_ids(&self) -> usize {
		self.authority_id_to_addresses.len()
	}

	/// Returns the addresses for the given [`AuthorityId`].
	pub fn get_addresses_by_authority_id(
		&self,
		authority_id: &AuthorityId,
	) -> Option<&HashSet<Multiaddr>> {
		self.authority_id_to_addresses.peek(authority_id)
	}

	/// Returns the [`AuthorityId`]s for the given [`PeerId`].
	///
	/// As the authority id can change between sessions, one [`PeerId`] can be mapped to
	/// multiple authority ids.
	pub fn get_authority_ids_by_peer_id(&self, peer_id: &PeerId) -> Option<&HashSet<AuthorityId>> {
		self.peer_id_to_authority_id.get(peer_id)
	}

	/// Set the maximum number of [`AuthorityId`]s to cache.
	///
	/// The new maximum will be taken in account the next time [`Self::insert`] is called.
	pub fn set_max_authority_ids(&mut self, max: usize) {
		self.max_authority_ids = max;
	}
}

fn peer_id_from_multiaddr(addr: &Multiaddr) -> Option<PeerId> {
	addr.iter().last().and_then(|protocol| {
		if let Protocol::P2p(multihash) = protocol {
			PeerId::from_multihash(multihash).ok()
		} else {
			None
		}
	})
}

fn addresses_to_peer_ids(addresses: &HashSet<Multiaddr>) -> HashSet<PeerId> {
	addresses
		.iter()
		.filter_map(|a| peer_id_from_multiaddr(a))
		.collect::<HashSet<_>>()
}

#[cfg(test)]
mod tests {
	use super::*;

	use libp2p::multihash::{self, Multihash};
	use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

	use sp_authority_discovery::{AuthorityId, AuthorityPair};
	use sp_core::crypto::Pair;

	#[derive(Clone, Debug)]
	struct TestAuthorityId(AuthorityId);

	impl Arbitrary for TestAuthorityId {
		fn arbitrary(g: &mut Gen) -> Self {
			let seed = (0..32).map(|_| u8::arbitrary(g)).collect::<Vec<_>>();
			TestAuthorityId(AuthorityPair::from_seed_slice(&seed).unwrap().public())
		}
	}

	#[derive(Clone, Debug)]
	struct TestMultiaddr(Multiaddr);

	impl Arbitrary for TestMultiaddr {
		fn arbitrary(g: &mut Gen) -> Self {
			let seed = (0..32).map(|_| u8::arbitrary(g)).collect::<Vec<_>>();
			let peer_id = PeerId::from_multihash(
				Multihash::wrap(multihash::Code::Sha2_256.into(), &seed).unwrap(),
			)
			.unwrap();
			let multiaddr = "/ip6/2001:db8:0:0:0:0:0:2/tcp/30333"
				.parse::<Multiaddr>()
				.unwrap()
				.with(Protocol::P2p(peer_id.into()));

			TestMultiaddr(multiaddr)
		}
	}

	#[derive(Clone, Debug)]
	struct TestMultiaddrsSamePeerCombo(Multiaddr, Multiaddr);

	impl Arbitrary for TestMultiaddrsSamePeerCombo {
		fn arbitrary(g: &mut Gen) -> Self {
			let seed = (0..32).map(|_| u8::arbitrary(g)).collect::<Vec<_>>();
			let peer_id = PeerId::from_multihash(
				Multihash::wrap(multihash::Code::Sha2_256.into(), &seed).unwrap(),
			)
			.unwrap();
			let multiaddr1 = "/ip6/2001:db8:0:0:0:0:0:2/tcp/30333"
				.parse::<Multiaddr>()
				.unwrap()
				.with(Protocol::P2p(peer_id.into()));
			let multiaddr2 = "/ip6/2002:db8:0:0:0:0:0:2/tcp/30133"
				.parse::<Multiaddr>()
				.unwrap()
				.with(Protocol::P2p(peer_id.into()));
			TestMultiaddrsSamePeerCombo(multiaddr1, multiaddr2)
		}
	}

	#[test]
	fn last_inserted_authority_id_is_purged() {
		fn property(
			first: (TestAuthorityId, TestMultiaddr),
			second: (TestAuthorityId, TestMultiaddr),
			third: (TestAuthorityId, TestMultiaddr),
		) -> TestResult {
			let first: (AuthorityId, Multiaddr) = ((first.0).0, (first.1).0);
			let second: (AuthorityId, Multiaddr) = ((second.0).0, (second.1).0);
			let third: (AuthorityId, Multiaddr) = ((third.0).0, (third.1).0);

			let mut cache = AddrCache::new();

			cache.set_max_authority_ids(2);
			cache.insert(first.0.clone(), vec![first.1.clone()]);
			cache.insert(second.0.clone(), vec![second.1.clone()]);

			assert_eq!(
				Some(&HashSet::from([first.1.clone()])),
				cache.get_addresses_by_authority_id(&first.0),
				"Expect `get_addresses_by_authority_id` to return addresses of first authority."
			);
			assert_eq!(
				Some(&HashSet::from([first.0.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&first.1).unwrap()),
				"Expect `get_authority_id_by_peer_id` to return `AuthorityId` of first authority."
			);

			cache.insert(third.0.clone(), vec![third.1.clone()]);

			assert_eq!(
				None,
				cache.get_addresses_by_authority_id(&first.0),
				"Expect `get_addresses_by_authority_id` to not return `None` for first authority."
			);
			assert_eq!(
				None,
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&first.1).unwrap()),
				"Expect `get_authority_id_by_peer_id` to return `None` for first authority."
			);

			TestResult::passed()
		}

		QuickCheck::new()
			.max_tests(10)
			.quickcheck(property as fn(_, _, _) -> TestResult)
	}

	#[test]
	fn purges_authority_id_cache_properly() {
		fn property(
			authority1: TestAuthorityId,
			authority2: TestAuthorityId,
			multiaddr1: TestMultiaddr,
			multiaddr2: TestMultiaddr,
			multiaddr3: TestMultiaddrsSamePeerCombo,
		) -> TestResult {
			let authority1 = authority1.0;
			let authority2 = authority2.0;
			let multiaddr1 = multiaddr1.0;
			let multiaddr2 = multiaddr2.0;
			let TestMultiaddrsSamePeerCombo(multiaddr3, multiaddr4) = multiaddr3;

			let mut cache = AddrCache::new();
			// Only allow one authority id to be stored.
			cache.set_max_authority_ids(2);

			cache.insert(authority1.clone(), vec![multiaddr1.clone()]);
			cache.insert(
				authority1.clone(),
				vec![multiaddr2.clone(), multiaddr3.clone(), multiaddr4.clone()],
			);

			assert_eq!(
				None,
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr1).unwrap())
			);
			assert_eq!(
				Some(&HashSet::from([authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr2).unwrap())
			);
			assert_eq!(
				Some(&HashSet::from([authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr3).unwrap())
			);
			assert_eq!(
				Some(&HashSet::from([authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr4).unwrap())
			);

			cache.insert(authority2.clone(), vec![multiaddr2.clone()]);

			assert_eq!(
				Some(&HashSet::from([authority2.clone(), authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr2).unwrap())
			);
			assert_eq!(
				Some(&HashSet::from([authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr3).unwrap())
			);
			assert_eq!(cache.get_addresses_by_authority_id(&authority1).unwrap().len(), 3);

			cache.insert(authority2.clone(), vec![multiaddr2.clone(), multiaddr3.clone()]);

			assert_eq!(
				Some(&HashSet::from([authority2.clone(), authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr2).unwrap())
			);
			assert_eq!(
				Some(&HashSet::from([authority2.clone(), authority1.clone()])),
				cache.get_authority_ids_by_peer_id(&peer_id_from_multiaddr(&multiaddr3).unwrap())
			);
			assert_eq!(
				&HashSet::from([multiaddr2.clone(), multiaddr3.clone(), multiaddr4.clone()]),
				cache.get_addresses_by_authority_id(&authority1).unwrap(),
			);

			TestResult::passed()
		}

		QuickCheck::new()
			.max_tests(10)
			.quickcheck(property as fn(_, _, _, _, _) -> TestResult)
	}

	/// As the runtime gives us the current + next authority ids, it can happen that some
	/// authority changed its session keys. Changing the sessions keys leads to having two
	/// authority ids that map to the same `PeerId` & addresses.
	#[test]
	fn adding_two_authority_ids_for_the_same_peer_id() {
		let mut addr_cache = AddrCache::new();
		addr_cache.set_max_authority_ids(10);

		let peer_id = PeerId::random();
		let addr = Multiaddr::empty().with(Protocol::P2p(peer_id.into()));

		let authority_id0 = AuthorityPair::generate().0.public();
		let authority_id1 = AuthorityPair::generate().0.public();

		addr_cache.insert(authority_id0.clone(), vec![addr.clone()]);
		addr_cache.insert(authority_id1.clone(), vec![addr.clone()]);

		assert_eq!(2, addr_cache.num_authority_ids());
		assert_eq!(
			&HashSet::from([addr.clone()]),
			addr_cache.get_addresses_by_authority_id(&authority_id0).unwrap()
		);
		assert_eq!(
			&HashSet::from([addr]),
			addr_cache.get_addresses_by_authority_id(&authority_id1).unwrap()
		);
	}
}
