// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Logic for keeping track of BEEFY peers.

// TODO (issue #12296): replace this naive peer tracking with generic one that infers data
// from multiple network protocols.

use sc_network::PeerId;
use sp_runtime::traits::{Block, NumberFor, Zero};
use std::collections::{HashMap, VecDeque};

struct PeerData<B: Block> {
	last_voted_on: NumberFor<B>,
}

impl<B: Block> Default for PeerData<B> {
	fn default() -> Self {
		PeerData { last_voted_on: Zero::zero() }
	}
}

/// Keep a simple map of connected peers
/// and the most recent voting round they participated in.
pub struct KnownPeers<B: Block> {
	live: HashMap<PeerId, PeerData<B>>,
}

impl<B: Block> KnownPeers<B> {
	pub fn new() -> Self {
		Self { live: HashMap::new() }
	}

	/// Note vote round number for `peer`.
	pub fn note_vote_for(&mut self, peer: PeerId, round: NumberFor<B>) {
		let data = self.live.entry(peer).or_default();
		data.last_voted_on = round.max(data.last_voted_on);
	}

	/// Remove connected `peer`.
	pub fn remove(&mut self, peer: &PeerId) {
		self.live.remove(peer);
	}

	/// Return _filtered and cloned_ list of peers that have voted on higher than `block`.
	pub fn further_than(&self, block: NumberFor<B>) -> VecDeque<PeerId> {
		self.live
			.iter()
			.filter_map(|(k, v)| (v.last_voted_on > block).then_some(k))
			.cloned()
			.collect()
	}

	/// Answer whether `peer` is part of `KnownPeers` set.
	pub fn contains(&self, peer: &PeerId) -> bool {
		self.live.contains_key(peer)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_track_known_peers_progress() {
		let (alice, bob, charlie) = (PeerId::random(), PeerId::random(), PeerId::random());
		let mut peers = KnownPeers::<sc_network_test::Block>::new();
		assert!(peers.live.is_empty());

		// 'Tracked' Bob seen voting for 5.
		peers.note_vote_for(bob, 5);
		// Previously unseen Charlie now seen voting for 10.
		peers.note_vote_for(charlie, 10);

		assert_eq!(peers.live.len(), 2);
		assert!(!peers.contains(&alice));
		assert!(peers.contains(&bob));
		assert!(peers.contains(&charlie));

		// Get peers at block > 4
		let further_than_4 = peers.further_than(4);
		// Should be Bob and Charlie
		assert_eq!(further_than_4.len(), 2);
		assert!(further_than_4.contains(&bob));
		assert!(further_than_4.contains(&charlie));

		// 'Tracked' Alice seen voting for 10.
		peers.note_vote_for(alice, 10);

		// Get peers at block > 9
		let further_than_9 = peers.further_than(9);
		// Should be Charlie and Alice
		assert_eq!(further_than_9.len(), 2);
		assert!(further_than_9.contains(&charlie));
		assert!(further_than_9.contains(&alice));

		// Remove Alice
		peers.remove(&alice);
		assert_eq!(peers.live.len(), 2);
		assert!(!peers.contains(&alice));

		// Get peers at block >= 9
		let further_than_9 = peers.further_than(9);
		// Now should be just Charlie
		assert_eq!(further_than_9.len(), 1);
		assert!(further_than_9.contains(&charlie));
	}
}
