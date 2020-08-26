// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! Peer Set Manager (PSM). Contains the strategy for choosing which nodes the network should be
//! connected to.

mod peersstate;

use std::{collections::{HashSet, HashMap}, collections::VecDeque};
use futures::prelude::*;
use log::{debug, error, trace};
use serde_json::json;
use std::{pin::Pin, task::{Context, Poll}, time::Duration};
use wasm_timer::Instant;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};

pub use libp2p::PeerId;

/// We don't accept nodes whose reputation is under this value.
const BANNED_THRESHOLD: i32 = 82 * (i32::min_value() / 100);
/// Reputation change for a node when we get disconnected from it.
const DISCONNECT_REPUTATION_CHANGE: i32 = -256;
/// Reserved peers group ID
const RESERVED_NODES: &'static str = "reserved";
/// Amount of time between the moment we disconnect from a node and the moment we remove it from
/// the list.
const FORGET_AFTER: Duration = Duration::from_secs(3600);

#[derive(Debug)]
enum Action {
	AddReservedPeer(PeerId),
	RemoveReservedPeer(PeerId),
	SetReservedPeers(HashSet<PeerId>),
	SetReservedOnly(bool),
	ReportPeer(PeerId, ReputationChange),
	SetPriorityGroup(String, HashSet<PeerId>),
	AddToPriorityGroup(String, PeerId),
	RemoveFromPriorityGroup(String, PeerId),
}

/// Description of a reputation adjustment for a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReputationChange {
	/// Reputation delta.
	pub value: i32,
	/// Reason for reputation change.
	pub reason: &'static str,
}

impl ReputationChange {
	/// New reputation change with given delta and reason.
	pub const fn new(value: i32, reason: &'static str) -> ReputationChange {
		ReputationChange { value, reason }
	}

	/// New reputation change that forces minimum possible reputation.
	pub const fn new_fatal(reason: &'static str) -> ReputationChange {
		ReputationChange { value: i32::min_value(), reason }
	}
}

/// Shared handle to the peer set manager (PSM). Distributed around the code.
#[derive(Debug, Clone)]
pub struct PeersetHandle {
	tx: TracingUnboundedSender<Action>,
}

impl PeersetHandle {
	/// Adds a new reserved peer. The peerset will make an effort to always remain connected to
	/// this peer.
	///
	/// Has no effect if the node was already a reserved peer.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for this node,
	/// >			otherwise it will not be able to connect to it.
	pub fn add_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::AddReservedPeer(peer_id));
	}

	/// Remove a previously-added reserved peer.
	///
	/// Has no effect if the node was not a reserved peer.
	pub fn remove_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::RemoveReservedPeer(peer_id));
	}

	/// Sets whether or not the peerset only has connections .
	pub fn set_reserved_only(&self, reserved: bool) {
		let _ = self.tx.unbounded_send(Action::SetReservedOnly(reserved));
	}
	
	/// Set reserved peers to the new set.
	pub fn set_reserved_peers(&self, peer_ids: HashSet<PeerId>) {
		let _ = self.tx.unbounded_send(Action::SetReservedPeers(peer_ids));
	}

	/// Reports an adjustment to the reputation of the given peer.
	pub fn report_peer(&self, peer_id: PeerId, score_diff: ReputationChange) {
		let _ = self.tx.unbounded_send(Action::ReportPeer(peer_id, score_diff));
	}

	/// Modify a priority group.
	pub fn set_priority_group(&self, group_id: String, peers: HashSet<PeerId>) {
		let _ = self.tx.unbounded_send(Action::SetPriorityGroup(group_id, peers));
	}

	/// Add a peer to a priority group.
	pub fn add_to_priority_group(&self, group_id: String, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::AddToPriorityGroup(group_id, peer_id));
	}

	/// Remove a peer from a priority group.
	pub fn remove_from_priority_group(&self, group_id: String, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::RemoveFromPriorityGroup(group_id, peer_id));
	}
}

/// Message that can be sent by the peer set manager (PSM).
#[derive(Debug, PartialEq)]
pub enum Message {
	/// Request to open a connection to the given peer. From the point of view of the PSM, we are
	/// immediately connected.
	Connect(PeerId),

	/// Drop the connection to the given peer, or cancel the connection attempt after a `Connect`.
	Drop(PeerId),

	/// Equivalent to `Connect` for the peer corresponding to this incoming index.
	Accept(IncomingIndex),

	/// Equivalent to `Drop` for the peer corresponding to this incoming index.
	Reject(IncomingIndex),
}

/// Opaque identifier for an incoming connection. Allocated by the network.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct IncomingIndex(pub u64);

impl From<u64> for IncomingIndex {
	fn from(val: u64) -> IncomingIndex {
		IncomingIndex(val)
	}
}

/// Configuration to pass when creating the peer set manager.
#[derive(Debug)]
pub struct PeersetConfig {
	/// Maximum number of ingoing links to peers.
	pub in_peers: u32,

	/// Maximum number of outgoing links to peers.
	pub out_peers: u32,

	/// List of bootstrap nodes to initialize the peer with.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// >			otherwise it will not be able to connect to them.
	pub bootnodes: Vec<PeerId>,

	/// If true, we only accept nodes in [`PeersetConfig::priority_groups`].
	pub reserved_only: bool,

	/// Lists of nodes we should always be connected to.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// >			otherwise it will not be able to connect to them.
	pub priority_groups: Vec<(String, HashSet<PeerId>)>,
}

/// Side of the peer set manager owned by the network. In other words, the "receiving" side.
///
/// Implements the `Stream` trait and can be polled for messages. The `Stream` never ends and never
/// errors.
#[derive(Debug)]
pub struct Peerset {
	/// Underlying data structure for the nodes's states.
	data: peersstate::PeersState,
	/// If true, we only accept reserved nodes.
	reserved_only: bool,
	/// Lists of nodes that don't occupy slots and that we should try to always be connected to.
	/// Is kept in sync with the list of reserved nodes in [`Peerset::data`].
	priority_groups: HashMap<String, HashSet<PeerId>>,
	/// Receiver for messages from the `PeersetHandle` and from `tx`.
	rx: TracingUnboundedReceiver<Action>,
	/// Sending side of `rx`.
	tx: TracingUnboundedSender<Action>,
	/// Queue of messages to be emitted when the `Peerset` is polled.
	message_queue: VecDeque<Message>,
	/// When the `Peerset` was created.
	created: Instant,
	/// Last time when we updated the reputations of connected nodes.
	latest_time_update: Instant,
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> (Peerset, PeersetHandle) {
		let (tx, rx) = tracing_unbounded("mpsc_peerset_messages");

		let handle = PeersetHandle {
			tx: tx.clone(),
		};

		let now = Instant::now();

		let mut peerset = Peerset {
			data: peersstate::PeersState::new(config.in_peers, config.out_peers),
			tx,
			rx,
			reserved_only: config.reserved_only,
			priority_groups: config.priority_groups.clone().into_iter().collect(),
			message_queue: VecDeque::new(),
			created: now,
			latest_time_update: now,
		};

		for node in config.priority_groups.into_iter().flat_map(|(_, l)| l) {
			peerset.data.add_no_slot_node(node);
		}

		for peer_id in config.bootnodes {
			if let peersstate::Peer::Unknown(entry) = peerset.data.peer(&peer_id) {
				entry.discover();
			} else {
				debug!(target: "peerset", "Duplicate bootnode in config: {:?}", peer_id);
			}
		}

		peerset.alloc_slots();
		(peerset, handle)
	}

	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		self.on_add_to_priority_group(RESERVED_NODES, peer_id);
	}

	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.on_remove_from_priority_group(RESERVED_NODES, peer_id);
	}
	
	fn on_set_reserved_peers(&mut self, peer_ids: HashSet<PeerId>) {
		self.on_set_priority_group(RESERVED_NODES, peer_ids);
	}

	fn on_set_reserved_only(&mut self, reserved_only: bool) {
		self.reserved_only = reserved_only;

		if self.reserved_only {
			// Disconnect all the nodes that aren't reserved.
			for peer_id in self.data.connected_peers().cloned().collect::<Vec<_>>().into_iter() {
				if self.priority_groups.get(RESERVED_NODES).map_or(false, |g| g.contains(&peer_id)) {
					continue;
				}

				let peer = self.data.peer(&peer_id).into_connected()
					.expect("We are enumerating connected peers, therefore the peer is connected; qed");
				peer.disconnect();
				self.message_queue.push_back(Message::Drop(peer_id));
			}

		} else {
			self.alloc_slots();
		}
	}

	fn on_set_priority_group(&mut self, group_id: &str, peers: HashSet<PeerId>) {
		// Determine the difference between the current group and the new list.
		let (to_insert, to_remove) = {
			let current_group = self.priority_groups.entry(group_id.to_owned()).or_default();
			let to_insert = peers.difference(current_group)
				.cloned().collect::<Vec<_>>();
			let to_remove = current_group.difference(&peers)
				.cloned().collect::<Vec<_>>();
			(to_insert, to_remove)
		};

		// Enumerate elements in `peers` not in `current_group`.
		for peer_id in &to_insert {
			// We don't call `on_add_to_priority_group` here in order to avoid calling
			// `alloc_slots` all the time.
			self.priority_groups.entry(group_id.to_owned()).or_default().insert(peer_id.clone());
			self.data.add_no_slot_node(peer_id.clone());
		}

		// Enumerate elements in `current_group` not in `peers`.
		for peer in to_remove {
			self.on_remove_from_priority_group(group_id, peer);
		}

		if !to_insert.is_empty() {
			self.alloc_slots();
		}
	}

	fn on_add_to_priority_group(&mut self, group_id: &str, peer_id: PeerId) {
		self.priority_groups.entry(group_id.to_owned()).or_default().insert(peer_id.clone());
		self.data.add_no_slot_node(peer_id);
		self.alloc_slots();
	}

	fn on_remove_from_priority_group(&mut self, group_id: &str, peer_id: PeerId) {
		if let Some(priority_group) = self.priority_groups.get_mut(group_id) {
			if !priority_group.remove(&peer_id) {
				// `PeerId` wasn't in the group in the first place.
				return;
			}
		} else {
			// Group doesn't exist, so the `PeerId` can't be in it.
			return;
		}

		// If that `PeerId` isn't in any other group, then it is no longer no-slot-occupying.
		if !self.priority_groups.values().any(|l| l.contains(&peer_id)) {
			self.data.remove_no_slot_node(&peer_id);
		}

		// Disconnect the peer if necessary.
		if group_id != RESERVED_NODES && self.reserved_only {
			if let peersstate::Peer::Connected(peer) = self.data.peer(&peer_id) {
				peer.disconnect();
				self.message_queue.push_back(Message::Drop(peer_id));
			}
		}
	}

	fn on_report_peer(&mut self, peer_id: PeerId, change: ReputationChange) {
		// We want reputations to be up-to-date before adjusting them.
		self.update_time();

		match self.data.peer(&peer_id) {
			peersstate::Peer::Connected(mut peer) => {
				peer.add_reputation(change.value);
				if peer.reputation() < BANNED_THRESHOLD {
					debug!(target: "peerset", "Report {}: {:+} to {}. Reason: {}, Disconnecting",
						peer_id, change.value, peer.reputation(), change.reason
					);
					peer.disconnect();
					self.message_queue.push_back(Message::Drop(peer_id));
				} else {
					trace!(target: "peerset", "Report {}: {:+} to {}. Reason: {}",
						peer_id, change.value, peer.reputation(), change.reason
					);
				}
			},
			peersstate::Peer::NotConnected(mut peer) => peer.add_reputation(change.value),
			peersstate::Peer::Unknown(peer) => peer.discover().add_reputation(change.value),
		}
	}

	/// Updates the value of `self.latest_time_update` and performs all the updates that happen
	/// over time, such as reputation increases for staying connected.
	fn update_time(&mut self) {
		let now = Instant::now();

		// We basically do `(now - self.latest_update).as_secs()`, except that by the way we do it
		// we know that we're not going to miss seconds because of rounding to integers.
		let secs_diff = {
			let elapsed_latest = self.latest_time_update - self.created;
			let elapsed_now = now - self.created;
			self.latest_time_update = now;
			elapsed_now.as_secs() - elapsed_latest.as_secs()
		};

		// For each elapsed second, move the node reputation towards zero.
		// If we multiply each second the reputation by `k` (where `k` is between 0 and 1), it
		// takes `ln(0.5) / ln(k)` seconds to reduce the reputation by half. Use this formula to
		// empirically determine a value of `k` that looks correct.
		for _ in 0..secs_diff {
			for peer_id in self.data.peers().cloned().collect::<Vec<_>>() {
				// We use `k = 0.98`, so we divide by `50`. With that value, it takes 34.3 seconds
				// to reduce the reputation by half.
				fn reput_tick(reput: i32) -> i32 {
					let mut diff = reput / 50;
					if diff == 0 && reput < 0 {
						diff = -1;
					} else if diff == 0 && reput > 0 {
						diff = 1;
					}
					reput.saturating_sub(diff)
				}
				match self.data.peer(&peer_id) {
					peersstate::Peer::Connected(mut peer) => {
						let before = peer.reputation();
						let after = reput_tick(before);
						trace!(target: "peerset", "Fleeting {}: {} -> {}", peer_id, before, after);
						peer.set_reputation(after)
					}
					peersstate::Peer::NotConnected(mut peer) => {
						if peer.reputation() == 0 &&
							peer.last_connected_or_discovered() + FORGET_AFTER < now
						{
							peer.forget_peer();
						} else {
							let before = peer.reputation();
							let after = reput_tick(before);
							trace!(target: "peerset", "Fleeting {}: {} -> {}", peer_id, before, after);
							peer.set_reputation(after)
						}
					}
					peersstate::Peer::Unknown(_) => unreachable!("We iterate over known peers; qed")
				};
			}
		}
	}

	/// Try to fill available out slots with nodes.
	fn alloc_slots(&mut self) {
		self.update_time();

		// Try to connect to all the reserved nodes that we are not connected to.
		loop {
			let next = {
				let data = &mut self.data;
				self.priority_groups
					.get(RESERVED_NODES)
					.into_iter()
					.flatten()
					.filter(move |n| {
						data.peer(n).into_connected().is_none()
					})
					.next()
					.cloned()
			};

			let next = match next {
				Some(n) => n,
				None => break,
			};

			let next = match self.data.peer(&next) {
				peersstate::Peer::Unknown(n) => n.discover(),
				peersstate::Peer::NotConnected(n) => n,
				peersstate::Peer::Connected(_) => {
					debug_assert!(false, "State inconsistency: not connected state");
					break;
				}
			};

			match next.try_outgoing() {
				Ok(conn) => self.message_queue.push_back(Message::Connect(conn.into_peer_id())),
				Err(_) => break,	// No more slots available.
			}
		}

		// Nothing more to do if we're in reserved mode.
		if self.reserved_only {
			return;
		}

		// Try to connect to all the nodes in priority groups and that we are not connected to.
		loop {
			let next = {
				let data = &mut self.data;
				self.priority_groups
					.values()
					.flatten()
					.filter(move |n| {
						data.peer(n).into_connected().is_none()
					})
					.next()
					.cloned()
			};

			let next = match next {
				Some(n) => n,
				None => break,
			};

			let next = match self.data.peer(&next) {
				peersstate::Peer::Unknown(n) => n.discover(),
				peersstate::Peer::NotConnected(n) => n,
				peersstate::Peer::Connected(_) => {
					debug_assert!(false, "State inconsistency: not connected state");
					break;
				}
			};

			match next.try_outgoing() {
				Ok(conn) => self.message_queue.push_back(Message::Connect(conn.into_peer_id())),
				Err(_) => break,	// No more slots available.
			}
		}

		// Now, we try to connect to non-priority nodes.
		loop {
			// Try to grab the next node to attempt to connect to.
			let next = match self.data.highest_not_connected_peer() {
				Some(p) => p,
				None => break,	// No known node to add.
			};

			// Don't connect to nodes with an abysmal reputation.
			if next.reputation() < BANNED_THRESHOLD {
				break;
			}

			match next.try_outgoing() {
				Ok(conn) => self.message_queue.push_back(Message::Connect(conn.into_peer_id())),
				Err(_) => break,	// No more slots available.
			}
		}
	}

	/// Indicate that we received an incoming connection. Must be answered either with
	/// a corresponding `Accept` or `Reject`, except if we were already connected to this peer.
	///
	/// Note that this mechanism is orthogonal to `Connect`/`Drop`. Accepting an incoming
	/// connection implicitly means `Connect`, but incoming connections aren't cancelled by
	/// `dropped`.
	///
	// Implementation note: because of concurrency issues, it is possible that we push a `Connect`
	// message to the output channel with a `PeerId`, and that `incoming` gets called with the same
	// `PeerId` before that message has been read by the user. In this situation we must not answer.
	pub fn incoming(&mut self, peer_id: PeerId, index: IncomingIndex) {
		trace!(target: "peerset", "Incoming {:?}", peer_id);
		self.update_time();

		if self.reserved_only {
			if !self.priority_groups.get(RESERVED_NODES).map_or(false, |n| n.contains(&peer_id)) {
				self.message_queue.push_back(Message::Reject(index));
				return;
			}
		}

		let not_connected = match self.data.peer(&peer_id) {
			// If we're already connected, don't answer, as the docs mention.
			peersstate::Peer::Connected(_) => return,
			peersstate::Peer::NotConnected(mut entry) => {
				entry.bump_last_connected_or_discovered();
				entry
			},
			peersstate::Peer::Unknown(entry) => entry.discover(),
		};

		if not_connected.reputation() < BANNED_THRESHOLD {
			self.message_queue.push_back(Message::Reject(index));
			return
		}

		match not_connected.try_accept_incoming() {
			Ok(_) => self.message_queue.push_back(Message::Accept(index)),
			Err(_) => self.message_queue.push_back(Message::Reject(index)),
		}
	}

	/// Indicate that we dropped an active connection with a peer, or that we failed to connect.
	///
	/// Must only be called after the PSM has either generated a `Connect` message with this
	/// `PeerId`, or accepted an incoming connection with this `PeerId`.
	pub fn dropped(&mut self, peer_id: PeerId) {
		trace!(target: "peerset", "Dropping {:?}", peer_id);

		// We want reputations to be up-to-date before adjusting them.
		self.update_time();

		match self.data.peer(&peer_id) {
			peersstate::Peer::Connected(mut entry) => {
				// Decrease the node's reputation so that we don't try it again and again and again.
				entry.add_reputation(DISCONNECT_REPUTATION_CHANGE);
				entry.disconnect();
			}
			peersstate::Peer::NotConnected(_) | peersstate::Peer::Unknown(_) =>
				error!(target: "peerset", "Received dropped() for non-connected node"),
		}

		self.alloc_slots();
	}

	/// Adds discovered peer ids to the PSM.
	///
	/// > **Note**: There is no equivalent "expired" message, meaning that it is the responsibility
	/// >			of the PSM to remove `PeerId`s that fail to dial too often.
	pub fn discovered<I: IntoIterator<Item = PeerId>>(&mut self, peer_ids: I) {
		let mut discovered_any = false;

		for peer_id in peer_ids {
			if let peersstate::Peer::Unknown(entry) = self.data.peer(&peer_id) {
				entry.discover();
				discovered_any = true;
			}
		}

		if discovered_any {
			self.alloc_slots();
		}
	}

	/// Reports an adjustment to the reputation of the given peer.
	pub fn report_peer(&mut self, peer_id: PeerId, score_diff: ReputationChange) {
		// We don't immediately perform the adjustments in order to have state consistency. We
		// don't want the reporting here to take priority over messages sent using the
		// `PeersetHandle`.
		let _ = self.tx.unbounded_send(Action::ReportPeer(peer_id, score_diff));
	}

	/// Produces a JSON object containing the state of the peerset manager, for debugging purposes.
	pub fn debug_info(&mut self) -> serde_json::Value {
		self.update_time();

		json!({
			"nodes": self.data.peers().cloned().collect::<Vec<_>>().into_iter().map(|peer_id| {
				let state = match self.data.peer(&peer_id) {
					peersstate::Peer::Connected(entry) => json!({
						"connected": true,
						"reputation": entry.reputation()
					}),
					peersstate::Peer::NotConnected(entry) => json!({
						"connected": false,
						"reputation": entry.reputation()
					}),
					peersstate::Peer::Unknown(_) =>
						unreachable!("We iterate over the known peers; QED")
				};

				(peer_id.to_base58(), state)
			}).collect::<HashMap<_, _>>(),
			"reserved_only": self.reserved_only,
			"message_queue": self.message_queue.len(),
		})
	}

	/// Returns the number of peers that we have discovered.
	pub fn num_discovered_peers(&self) -> usize {
		self.data.peers().len()
	}

	/// Returns the content of a priority group.
	pub fn priority_group(&self, group_id: &str) -> Option<impl ExactSizeIterator<Item = &PeerId>> {
		self.priority_groups.get(group_id).map(|l| l.iter())
	}
}

impl Stream for Peerset {
	type Item = Message;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		loop {
			if let Some(message) = self.message_queue.pop_front() {
				return Poll::Ready(Some(message));
			}

			let action = match Stream::poll_next(Pin::new(&mut self.rx), cx) {
				Poll::Pending => return Poll::Pending,
				Poll::Ready(Some(event)) => event,
				Poll::Ready(None) => return Poll::Pending,
			};

			match action {
				Action::AddReservedPeer(peer_id) =>
					self.on_add_reserved_peer(peer_id),
				Action::RemoveReservedPeer(peer_id) =>
					self.on_remove_reserved_peer(peer_id),
				Action::SetReservedPeers(peer_ids) =>
					self.on_set_reserved_peers(peer_ids),
				Action::SetReservedOnly(reserved) =>
					self.on_set_reserved_only(reserved),
				Action::ReportPeer(peer_id, score_diff) =>
					self.on_report_peer(peer_id, score_diff),
				Action::SetPriorityGroup(group_id, peers) =>
					self.on_set_priority_group(&group_id, peers),
				Action::AddToPriorityGroup(group_id, peer_id) =>
					self.on_add_to_priority_group(&group_id, peer_id),
				Action::RemoveFromPriorityGroup(group_id, peer_id) =>
					self.on_remove_from_priority_group(&group_id, peer_id),
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use libp2p::PeerId;
	use futures::prelude::*;
	use super::{PeersetConfig, Peerset, Message, IncomingIndex, ReputationChange, BANNED_THRESHOLD};
	use std::{pin::Pin, task::Poll, thread, time::Duration};

	fn assert_messages(mut peerset: Peerset, messages: Vec<Message>) -> Peerset {
		for expected_message in messages {
			let (message, p) = next_message(peerset).expect("expected message");
			assert_eq!(message, expected_message);
			peerset = p;
		}
		peerset
	}

	fn next_message(mut peerset: Peerset) -> Result<(Message, Peerset), ()> {
		let next = futures::executor::block_on_stream(&mut peerset).next();
		let message = next.ok_or_else(|| ())?;
		Ok((message, peerset))
	}

	#[test]
	fn test_peerset_add_reserved_peer() {
		let bootnode = PeerId::random();
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 2,
			bootnodes: vec![bootnode],
			reserved_only: true,
			priority_groups: Vec::new(),
		};

		let (peerset, handle) = Peerset::from_config(config);
		handle.add_reserved_peer(reserved_peer.clone());
		handle.add_reserved_peer(reserved_peer2.clone());

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(reserved_peer2)
		]);
	}

	#[test]
	fn test_peerset_incoming() {
		let bootnode = PeerId::random();
		let incoming = PeerId::random();
		let incoming2 = PeerId::random();
		let incoming3 = PeerId::random();
		let ii = IncomingIndex(1);
		let ii2 = IncomingIndex(2);
		let ii3 = IncomingIndex(3);
		let ii4 = IncomingIndex(3);
		let config = PeersetConfig {
			in_peers: 2,
			out_peers: 1,
			bootnodes: vec![bootnode.clone()],
			reserved_only: false,
			priority_groups: Vec::new(),
		};

		let (mut peerset, _handle) = Peerset::from_config(config);
		peerset.incoming(incoming.clone(), ii);
		peerset.incoming(incoming.clone(), ii4);
		peerset.incoming(incoming2.clone(), ii2);
		peerset.incoming(incoming3.clone(), ii3);

		assert_messages(peerset, vec![
			Message::Connect(bootnode.clone()),
			Message::Accept(ii),
			Message::Accept(ii2),
			Message::Reject(ii3),
		]);
	}

	#[test]
	fn test_peerset_reject_incoming_in_reserved_only() {
		let incoming = PeerId::random();
		let ii = IncomingIndex(1);
		let config = PeersetConfig {
			in_peers: 50,
			out_peers: 50,
			bootnodes: vec![],
			reserved_only: true,
			priority_groups: vec![],
		};

		let (mut peerset, _) = Peerset::from_config(config);
		peerset.incoming(incoming.clone(), ii);

		assert_messages(peerset, vec![
			Message::Reject(ii),
		]);
	}

	#[test]
	fn test_peerset_discovered() {
		let bootnode = PeerId::random();
		let discovered = PeerId::random();
		let discovered2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 2,
			bootnodes: vec![bootnode.clone()],
			reserved_only: false,
			priority_groups: vec![],
		};

		let (mut peerset, _handle) = Peerset::from_config(config);
		peerset.discovered(Some(discovered.clone()));
		peerset.discovered(Some(discovered.clone()));
		peerset.discovered(Some(discovered2));

		assert_messages(peerset, vec![
			Message::Connect(bootnode),
			Message::Connect(discovered),
		]);
	}

	#[test]
	fn test_peerset_banned() {
		let (mut peerset, handle) = Peerset::from_config(PeersetConfig {
			in_peers: 25,
			out_peers: 25,
			bootnodes: vec![],
			reserved_only: false,
			priority_groups: vec![],
		});

		// We ban a node by setting its reputation under the threshold.
		let peer_id = PeerId::random();
		handle.report_peer(peer_id.clone(), ReputationChange::new(BANNED_THRESHOLD - 1, ""));

		let fut = futures::future::poll_fn(move |cx| {
			// We need one polling for the message to be processed.
			assert_eq!(Stream::poll_next(Pin::new(&mut peerset), cx), Poll::Pending);

			// Check that an incoming connection from that node gets refused.
			peerset.incoming(peer_id.clone(), IncomingIndex(1));
			if let Poll::Ready(msg) = Stream::poll_next(Pin::new(&mut peerset), cx) {
				assert_eq!(msg.unwrap(), Message::Reject(IncomingIndex(1)));
			} else {
				panic!()
			}

			// Wait a bit for the node's reputation to go above the threshold.
			thread::sleep(Duration::from_millis(1500));

			// Try again. This time the node should be accepted.
			peerset.incoming(peer_id.clone(), IncomingIndex(2));
			while let Poll::Ready(msg) = Stream::poll_next(Pin::new(&mut peerset), cx) {
				assert_eq!(msg.unwrap(), Message::Accept(IncomingIndex(2)));
			}

			Poll::Ready(())
		});

		futures::executor::block_on(fut);
	}
}
