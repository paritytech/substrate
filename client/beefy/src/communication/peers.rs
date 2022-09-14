// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

	/// Add new connected `peer`.
	pub fn add_new(&mut self, peer: PeerId) {
		self.live.entry(peer).or_default();
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

	/// Return _filtered and cloned_ list of peers that have voted on `block` or higher.
	pub fn peers_at_least_at_block(&self, block: NumberFor<B>) -> VecDeque<PeerId> {
		self.live
			.iter()
			.filter_map(|(k, v)| if v.last_voted_on >= block { Some(k) } else { None })
			.cloned()
			.collect()
	}

	/// Answer whether `peer` is part of `KnownPeers` set.
	pub fn contains(&self, peer: &PeerId) -> bool {
		self.live.contains_key(peer)
	}
}
