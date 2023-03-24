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
	sync::{Arc, Mutex},
	time::{Duration, Instant},
};
use wasm_timer::Delay;

use crate::ReputationChange;

/// We don't accept nodes whose reputation is under this value.
const BANNED_THRESHOLD: i32 = 82 * (i32::MIN / 100);
/// Reputation change for a node when we get disconnected from it.
const DISCONNECT_REPUTATION_CHANGE: i32 = -256;
/// Relative decrement of a reputation value that is applied every second. I.e., for inverse
/// decrement of 50 we decrease absolute value of the reputation by 1/50. This corresponds to a
/// factor of `k = 0.98`. It takes `ln(0.5) / ln(k)` seconds to reduce the reputation by half, or
/// 34.3 seconds for the values above. In this setup the maximum allowed absolute value of
/// `i32::MAX` becomes 0 in ~1100 seconds, and this is the maximun time records live in the hash map
/// if they are not updated.
const INVERSE_DECREMENT: i32 = 50;

pub trait PeerReputationProvider {
	/// Check whether the peer is banned.
	fn is_banned(&self, peer_id: &PeerId) -> bool;

	/// Report the peer disconnect for reputation adjustement.
	fn report_disconnect(&mut self, peer_id: PeerId);

	/// Adjust peer reputation value.
	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange);

	/// Get peer reputation value.
	fn peer_reputation(&self, peer_id: &PeerId) -> i32;

	/// Get the candidates for initiating outgoing connections.
	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId>;
}

pub struct PeerStoreHandle {
	inner: Arc<Mutex<PeerStoreInner>>,
}

impl PeerReputationProvider for PeerStoreHandle {
	fn is_banned(&self, peer_id: &PeerId) -> bool {
		self.inner.lock().unwrap().is_banned(peer_id)
	}

	fn report_disconnect(&mut self, peer_id: PeerId) {
		self.inner.lock().unwrap().report_disconnect(peer_id)
	}

	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange) {
		self.inner.lock().unwrap().report_peer(peer_id, change)
	}

	fn peer_reputation(&self, peer_id: &PeerId) -> i32 {
		self.inner.lock().unwrap().peer_reputation(peer_id)
	}

	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId> {
		self.inner.lock().unwrap().outgoing_candidates(count, ignored)
	}
}

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

	fn value(&self) -> i32 {
		self.0
	}

	fn decay(&mut self, seconds_passed: u64) {
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

	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange) {
		self.reputations.entry(peer_id).or_default().add_reputation(change.value);
	}

	fn peer_reputation(&self, peer_id: &PeerId) -> i32 {
		self.reputations.get(peer_id).cloned().unwrap_or(Reputation::default()).0
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

		// FIXME: depending on the usage patterns, it might be more efficient to always maintain
		// peers sorted.
	}

	fn progress_time(&mut self, seconds_passed: u64) {
		if seconds_passed == 0 {
			return
		}

		self.reputations
			.iter_mut()
			.for_each(|(_, reputation)| reputation.decay(seconds_passed));
		self.reputations.retain(|_, reputation| reputation.value() != 0);

		// TODO: we likely need to also account for another condition when removing nodes, like it
		// was done in `PeerSet` with `last_connected_or_discovered` and `FORGET_AFTER`. Otherwise,
		// bootnodes will be deleted at startup without a chance of being connected. As another
		// alternative, we can give bootnodes some initial reputation, enough for them to get
		// connected. This alternative is questionable, because we are limited to 1100 seconds of
		// reputation decay even for max reputation, which is less than one hour of lifetime in the
		// original `PeerSet`.
	}
}

struct PeerStore {
	inner: Arc<Mutex<PeerStoreInner>>,
}

impl PeerStore {
	/// Create new empty peer store.
	pub fn new() -> Self {
		// TODO: pass bootnodes.
		PeerStore { inner: Arc::new(Mutex::new(PeerStoreInner { reputations: HashMap::new() })) }
	}

	/// Get `PeerStoreHandle`.
	pub fn handle(&self) -> PeerStoreHandle {
		PeerStoreHandle { inner: self.inner.clone() }
	}

	/// Drive the `PeerStore`, decaying reputation values over time and removing expired entries.
	pub async fn run(self) {
		let started = Instant::now();
		let mut latest_time_update = started;
		loop {
			let now = Instant::now();
			// We basically do `(now - self.latest_update).as_secs()`, except that by the way we do
			// it we know that we're not going to miss seconds because of rounding to integers.
			let seconds_passed = {
				let elapsed_latest = latest_time_update - started;
				let elapsed_now = now - started;
				latest_time_update = now;
				elapsed_now.as_secs() - elapsed_latest.as_secs()
			};
			self.inner.lock().unwrap().progress_time(seconds_passed);
			let _ = Delay::new(Duration::from_secs(1)).await;
		}
	}
}
