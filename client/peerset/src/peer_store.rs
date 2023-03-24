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

use libp2p::PeerId;
use partial_sort::PartialSort;
use std::{
	cmp::{Ord, Ordering, PartialOrd},
	collections::{HashMap, HashSet},
};

/// We don't accept nodes whose reputation is under this value.
const BANNED_THRESHOLD: i32 = 82 * (i32::MIN / 100);
/// Reputation change for a node when we get disconnected from it.
const DISCONNECT_REPUTATION_CHANGE: i32 = -256;
/// Relative decrement of a reputation that is applied every second. I.e., for inverse decrement of
/// 50 we decrease absolute value of the reputation by 1/50. This corresponds to a factor of `k =
/// 0.98`. It takes `ln(0.5) / ln(k)` seconds to reduce the reputation by half, or 34.3 seconds for
/// the values above. In this setup the maximum allowed absolute value of `i32::MAX` becomes 0 in
/// ~1100 seconds, and this is the maximun time records live in the hash map if they are not
/// updated.
const INVERSE_DECREMENT: i32 = 50;

pub trait PeerReputationProvider {
	/// Check whether the peer is banned.
	fn is_banned(&self, peer_id: PeerId) -> bool;

	/// Report the peer disconnect for reputation adjustement.
	fn report_disconnect(&self, peer_id: PeerId);

	/// Get the candidates for initiating outgoing connections.
	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId>;
}

pub struct PeerStoreHandle {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Reputation(i32);

impl Default for Reputation {
	fn default() -> Self {
		Reputation(0)
	}
}

impl Ord for Reputation {
	// We define reverse order for reputation values.
	fn cmp(&self, other: &Self) -> Ordering {
		self.0.cmp(&other.0).reverse()
	}
}

impl PartialOrd for Reputation {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Reputation {
	fn is_banned(&self) -> bool {
		self.0 < BANNED_THRESHOLD
	}

	fn add_reputation(&mut self, increment: i32) {
		self.0 = self.0.saturating_add(increment);
	}

	fn decay(&mut self, seconds_passed: u32) {
		let reputation = &mut self.0;

		for _ in 0..seconds_passed {
			let mut diff = *reputation / INVERSE_DECREMENT;
			if diff == 0 && *reputation < 0 {
				diff = -1;
			} else if diff == 0 && *reputation > 0 {
				diff = 1;
			}

			*reputation = reputation.saturating_sub(diff);

			if *reputation == 0 {
				break
			}
		}
	}
}

struct PeerStoreInner {
	reputations: HashMap<PeerId, Reputation>,
}

impl PeerStoreInner {
	fn is_banned(&self, peer_id: &PeerId) -> bool {
		self.reputations.get(peer_id).cloned().unwrap_or_default().is_banned()
	}

	fn report_disconnect(&mut self, peer_id: PeerId) {
		self.reputations
			.entry(peer_id)
			.or_default()
			.add_reputation(DISCONNECT_REPUTATION_CHANGE);
	}

	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId> {
		let mut candidates = self
			.reputations
			.iter()
			.filter_map(|(peer_id, reputation)| {
				(!reputation.is_banned() && !ignored.contains(peer_id))
					.then_some((*peer_id, *reputation))
			})
			.collect::<Vec<_>>();
		candidates.partial_sort(count, |(_, rep1), (_, rep2)| rep1.cmp(rep2));
		candidates.iter().take(count).map(|(peer_id, _)| *peer_id).collect()

		// FIXME: depending on usage patterns, it might be more efficient to always maintain peers
		// sorted.
	}
}
