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

//! [`PeerStore`] manages peer reputations and provides connection candidates to
//! [`crate::protocol_controller::ProtocolController`].

use libp2p::PeerId;
use log::trace;
use parking_lot::Mutex;
use partial_sort::PartialSort;
use sc_network_common::types::ReputationChange;
use std::{
	cmp::{Ord, Ordering, PartialOrd},
	collections::{hash_map::Entry, HashMap, HashSet},
	fmt::Debug,
	sync::Arc,
	time::{Duration, Instant},
};
use wasm_timer::Delay;

use crate::protocol_controller::ProtocolHandle;

/// Log target for this file.
pub const LOG_TARGET: &str = "peerset";

/// We don't accept nodes whose reputation is under this value.
pub const BANNED_THRESHOLD: i32 = 82 * (i32::MIN / 100);
/// Reputation change for a node when we get disconnected from it.
const DISCONNECT_REPUTATION_CHANGE: i32 = -256;
/// Relative decrement of a reputation value that is applied every second. I.e., for inverse
/// decrement of 50 we decrease absolute value of the reputation by 1/50. This corresponds to a
/// factor of `k = 0.98`. It takes ~ `ln(0.5) / ln(k)` seconds to reduce the reputation by half,
/// or 34.3 seconds for the values above. In this setup the maximum allowed absolute value of
/// `i32::MAX` becomes 0 in ~1100 seconds (actually less due to integer arithmetic).
const INVERSE_DECREMENT: i32 = 50;
/// Amount of time between the moment we last updated the [`PeerStore`] entry and the moment we
/// remove it, once the reputation value reaches 0.
const FORGET_AFTER: Duration = Duration::from_secs(3600);

/// Trait providing peer reputation management and connection candidates.
pub trait PeerStoreProvider: Debug + Send {
	/// Check whether the peer is banned.
	fn is_banned(&self, peer_id: &PeerId) -> bool;

	/// Register a protocol handle to disconnect peers whose reputation drops below the threshold.
	fn register_protocol(&self, protocol_handle: ProtocolHandle);

	/// Report peer disconnection for reputation adjustment.
	fn report_disconnect(&mut self, peer_id: PeerId);

	/// Adjust peer reputation.
	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange);

	/// Get peer reputation.
	fn peer_reputation(&self, peer_id: &PeerId) -> i32;

	/// Get candidates with highest reputations for initiating outgoing connections.
	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId>;
}

/// Actual implementation of peer reputations and connection candidates provider.
#[derive(Debug, Clone)]
pub struct PeerStoreHandle {
	inner: Arc<Mutex<PeerStoreInner>>,
}

impl PeerStoreProvider for PeerStoreHandle {
	fn is_banned(&self, peer_id: &PeerId) -> bool {
		self.inner.lock().is_banned(peer_id)
	}

	fn register_protocol(&self, protocol_handle: ProtocolHandle) {
		self.inner.lock().register_protocol(protocol_handle);
	}

	fn report_disconnect(&mut self, peer_id: PeerId) {
		self.inner.lock().report_disconnect(peer_id)
	}

	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange) {
		self.inner.lock().report_peer(peer_id, change)
	}

	fn peer_reputation(&self, peer_id: &PeerId) -> i32 {
		self.inner.lock().peer_reputation(peer_id)
	}

	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId> {
		self.inner.lock().outgoing_candidates(count, ignored)
	}
}

impl PeerStoreHandle {
	/// Get the number of known peers.
	///
	/// This number might not include some connected peers in rare cases when their reputation
	/// was not updated for one hour, because their entries in [`PeerStore`] were dropped.
	pub fn num_known_peers(&self) -> usize {
		self.inner.lock().peers.len()
	}

	/// Add known peer.
	pub fn add_known_peer(&mut self, peer_id: PeerId) {
		self.inner.lock().add_known_peer(peer_id);
	}
}

#[derive(Debug, Clone, Copy)]
struct PeerInfo {
	reputation: i32,
	last_updated: Instant,
}

impl Default for PeerInfo {
	fn default() -> Self {
		Self { reputation: 0, last_updated: Instant::now() }
	}
}

impl PartialEq for PeerInfo {
	fn eq(&self, other: &Self) -> bool {
		self.reputation == other.reputation
	}
}

impl Eq for PeerInfo {}

impl Ord for PeerInfo {
	// We define reverse order by reputation values.
	fn cmp(&self, other: &Self) -> Ordering {
		self.reputation.cmp(&other.reputation).reverse()
	}
}

impl PartialOrd for PeerInfo {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl PeerInfo {
	fn is_banned(&self) -> bool {
		self.reputation < BANNED_THRESHOLD
	}

	fn add_reputation(&mut self, increment: i32) {
		self.reputation = self.reputation.saturating_add(increment);
		self.bump_last_updated();
	}

	fn decay_reputation(&mut self, seconds_passed: u64) {
		// Note that decaying the reputation value happens "on its own",
		// so we don't do `bump_last_updated()`.
		for _ in 0..seconds_passed {
			let mut diff = self.reputation / INVERSE_DECREMENT;
			if diff == 0 && self.reputation < 0 {
				diff = -1;
			} else if diff == 0 && self.reputation > 0 {
				diff = 1;
			}

			self.reputation = self.reputation.saturating_sub(diff);

			if self.reputation == 0 {
				break
			}
		}
	}

	fn bump_last_updated(&mut self) {
		self.last_updated = Instant::now();
	}
}

#[derive(Debug)]
struct PeerStoreInner {
	peers: HashMap<PeerId, PeerInfo>,
	protocols: Vec<ProtocolHandle>,
}

impl PeerStoreInner {
	fn is_banned(&self, peer_id: &PeerId) -> bool {
		self.peers.get(peer_id).map_or(false, |info| info.is_banned())
	}

	fn register_protocol(&mut self, protocol_handle: ProtocolHandle) {
		self.protocols.push(protocol_handle);
	}

	fn report_disconnect(&mut self, peer_id: PeerId) {
		let peer_info = self.peers.entry(peer_id).or_default();
		peer_info.add_reputation(DISCONNECT_REPUTATION_CHANGE);

		log::trace!(
			target: LOG_TARGET,
			"Peer {} disconnected, reputation: {:+} to {}",
			peer_id,
			DISCONNECT_REPUTATION_CHANGE,
			peer_info.reputation,
		);
	}

	fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange) {
		let peer_info = self.peers.entry(peer_id).or_default();
		peer_info.add_reputation(change.value);

		if peer_info.reputation < BANNED_THRESHOLD {
			self.protocols.iter().for_each(|handle| handle.disconnect_peer(peer_id));

			log::trace!(
				target: LOG_TARGET,
				"Report {}: {:+} to {}. Reason: {}. Banned, disconnecting.",
				peer_id,
				change.value,
				peer_info.reputation,
				change.reason,
			);
		} else {
			log::trace!(
				target: LOG_TARGET,
				"Report {}: {:+} to {}. Reason: {}.",
				peer_id,
				change.value,
				peer_info.reputation,
				change.reason,
			);
		}
	}

	fn peer_reputation(&self, peer_id: &PeerId) -> i32 {
		self.peers.get(peer_id).map_or(0, |info| info.reputation)
	}

	fn outgoing_candidates(&self, count: usize, ignored: HashSet<&PeerId>) -> Vec<PeerId> {
		let mut candidates = self
			.peers
			.iter()
			.filter_map(|(peer_id, info)| {
				(!info.is_banned() && !ignored.contains(peer_id)).then_some((*peer_id, *info))
			})
			.collect::<Vec<_>>();
		let count = std::cmp::min(count, candidates.len());
		candidates.partial_sort(count, |(_, info1), (_, info2)| info1.cmp(info2));
		candidates.iter().take(count).map(|(peer_id, _)| *peer_id).collect()

		// TODO: keep the peers sorted (in a "bi-multi-map"?) to not repeat sorting every time.
	}

	fn progress_time(&mut self, seconds_passed: u64) {
		if seconds_passed == 0 {
			return
		}

		// Drive reputation values towards 0.
		self.peers
			.iter_mut()
			.for_each(|(_, info)| info.decay_reputation(seconds_passed));

		// Retain only entries with non-zero reputation values or not expired ones.
		let now = Instant::now();
		self.peers
			.retain(|_, info| info.reputation != 0 || info.last_updated + FORGET_AFTER > now);
	}

	fn add_known_peer(&mut self, peer_id: PeerId) {
		match self.peers.entry(peer_id) {
			Entry::Occupied(mut e) => {
				trace!(
					target: LOG_TARGET,
					"Trying to add an already known peer {peer_id}, bumping `last_updated`.",
				);
				e.get_mut().bump_last_updated();
			},
			Entry::Vacant(e) => {
				trace!(target: LOG_TARGET, "Adding a new known peer {peer_id}.");
				e.insert(PeerInfo::default());
			},
		}
	}
}

/// Worker part of [`PeerStoreHandle`]
#[derive(Debug)]
pub struct PeerStore {
	inner: Arc<Mutex<PeerStoreInner>>,
}

impl PeerStore {
	/// Create a new peer store from the list of bootnodes.
	pub fn new(bootnodes: Vec<PeerId>) -> Self {
		PeerStore {
			inner: Arc::new(Mutex::new(PeerStoreInner {
				peers: bootnodes
					.into_iter()
					.map(|peer_id| (peer_id, PeerInfo::default()))
					.collect(),
				protocols: Vec::new(),
			})),
		}
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

			self.inner.lock().progress_time(seconds_passed);
			let _ = Delay::new(Duration::from_secs(1)).await;
		}
	}
}

#[cfg(test)]
mod tests {
	use super::PeerInfo;

	#[test]
	fn decaying_zero_reputation_yields_zero() {
		let mut peer_info = PeerInfo::default();
		assert_eq!(peer_info.reputation, 0);

		peer_info.decay_reputation(1);
		assert_eq!(peer_info.reputation, 0);

		peer_info.decay_reputation(100_000);
		assert_eq!(peer_info.reputation, 0);
	}

	#[test]
	fn decaying_positive_reputation_decreases_it() {
		const INITIAL_REPUTATION: i32 = 100;

		let mut peer_info = PeerInfo::default();
		peer_info.reputation = INITIAL_REPUTATION;

		peer_info.decay_reputation(1);
		assert!(peer_info.reputation >= 0);
		assert!(peer_info.reputation < INITIAL_REPUTATION);
	}

	#[test]
	fn decaying_negative_reputation_increases_it() {
		const INITIAL_REPUTATION: i32 = -100;

		let mut peer_info = PeerInfo::default();
		peer_info.reputation = INITIAL_REPUTATION;

		peer_info.decay_reputation(1);
		assert!(peer_info.reputation <= 0);
		assert!(peer_info.reputation > INITIAL_REPUTATION);
	}

	#[test]
	fn decaying_max_reputation_finally_yields_zero() {
		const INITIAL_REPUTATION: i32 = i32::MAX;
		const SECONDS: u64 = 1000;

		let mut peer_info = PeerInfo::default();
		peer_info.reputation = INITIAL_REPUTATION;

		peer_info.decay_reputation(SECONDS / 2);
		assert!(peer_info.reputation > 0);

		peer_info.decay_reputation(SECONDS / 2);
		assert_eq!(peer_info.reputation, 0);
	}

	#[test]
	fn decaying_min_reputation_finally_yields_zero() {
		const INITIAL_REPUTATION: i32 = i32::MIN;
		const SECONDS: u64 = 1000;

		let mut peer_info = PeerInfo::default();
		peer_info.reputation = INITIAL_REPUTATION;

		peer_info.decay_reputation(SECONDS / 2);
		assert!(peer_info.reputation < 0);

		peer_info.decay_reputation(SECONDS / 2);
		assert_eq!(peer_info.reputation, 0);
	}
}
