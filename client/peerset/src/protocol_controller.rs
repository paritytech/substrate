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

use futures::{FutureExt, StreamExt};
use libp2p::PeerId;
use log::{error, info, trace};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	time::{Duration, Instant},
};
use wasm_timer::Delay;

use crate::{DropReason, IncomingIndex, Message, PeersetHandle, SetConfig, SetId};

#[derive(Debug)]
enum Action {
	AddReservedPeer(PeerId),
	RemoveReservedPeer(PeerId),
	SetReservedPeers(HashSet<PeerId>),
	SetReservedOnly(bool),
	AddPeer(PeerId),
	RemovePeer(PeerId),
	IncomingConnection(PeerId, IncomingIndex),
	Dropped(PeerId, DropReason),
}

/// Shared handle to [`ProtocolController`]. Distributed around the code outside of the
/// protocol implementation.
pub struct ProtocolHandle {
	to_controller: TracingUnboundedSender<Action>,
}

impl ProtocolHandle {
	/// Adds a new reserved peer. [`ProtocolController`] will make an effort
	/// to always remain connected to this peer.
	///
	/// Has no effect if the node was already a reserved peer.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for this node,
	/// > otherwise it will not be able to connect to it.
	pub fn add_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::AddReservedPeer(peer_id));
	}

	/// Remove a previously-added reserved peer.
	///
	/// Has no effect if the node was not a reserved peer.
	pub fn remove_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::RemoveReservedPeer(peer_id));
	}

	/// Set reserved peers to the new set.
	pub fn set_reserved_peers(&self, peer_ids: HashSet<PeerId>) {
		let _ = self.to_controller.unbounded_send(Action::SetReservedPeers(peer_ids));
	}

	/// Sets whether or not [`ProtocolController`] only has connections with nodes marked
	/// as reserved for the given set.
	pub fn set_reserved_only(&self, reserved: bool) {
		let _ = self.to_controller.unbounded_send(Action::SetReservedOnly(reserved));
	}

	/// Add a peer to a set of peers we try to connect to.
	pub fn add_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::AddPeer(peer_id));
	}

	/// Remove a peer from a set of peers we try to connect to and disconnect the peer.
	pub fn remove_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::RemovePeer(peer_id));
	}

	/// Notify about incoming connection. [`ProtocolController`] will either accept or reject it.
	pub fn incoming_connection(&self, peer_id: PeerId, incoming_index: IncomingIndex) {
		let _ = self
			.to_controller
			.unbounded_send(Action::IncomingConnection(peer_id, incoming_index));
	}

	/// Notify that connection was dropped (eithere refused or disconnected).
	pub fn dropped(&self, peer_id: PeerId, reason: DropReason) {
		let _ = self.to_controller.unbounded_send(Action::Dropped(peer_id, reason));
	}
}

/// Direction of a connection
#[derive(Debug)]
enum Direction {
	Inbound,
	Outbound,
}

/// Status of a connection with a peer.
#[derive(Debug)]
enum PeerState {
	/// We are connected to the peer.
	Connected(Direction),
	/// We are not connected.
	NotConnected,
}

impl PeerState {
	/// Returns true if we are connected with the node.
	fn is_connected(&self) -> bool {
		matches!(self, PeerState::Connected(_))
	}
}

impl Default for PeerState {
	fn default() -> PeerState {
		PeerState::NotConnected
	}
}

/// Side of [`ProtocolHandle`] responsible for all the logic. Currently all instances are
/// owned by [`crate::Peerset`], but they should eventually be moved to corresponding protocols.
#[derive(Debug)]
pub struct ProtocolController {
	/// Set id to use when sending connect/drop requests to `Notifications`.
	// Will likely be replaced by `ProtocolName` in the future.
	set_id: SetId,
	/// Receiver for messages from [`ProtocolHandle`].
	from_handle: TracingUnboundedReceiver<Action>,
	/// Number of occupied slots for incoming connections.
	num_in: u32,
	/// Number of occupied slots for outgoing connections.
	num_out: u32,
	/// Maximum number of slots for incoming connections.
	max_in: u32,
	/// Maximum number of slots for outgoing connections.
	max_out: u32,
	/// Reserved nodes.
	reserved_nodes: HashSet<PeerId>,
	/// Connect only to reserved nodes.
	reserved_only: bool,
	/// Peers and their connection states (including reserved nodes).
	nodes: HashMap<PeerId, PeerState>,
	/// Next time to allocate slots. This is done once per second.
	next_periodic_alloc_slots: Instant,
	/// Outgoing channel for messages to `Notifications`.
	to_notifications: TracingUnboundedSender<Message>,
	/// Peerset handle for checking peer reputation values and getting connection candidates
	/// with highest reputation.
	peerset_handle: PeersetHandle,
}

impl ProtocolController {
	/// Construct new [`ProtocolController`].
	pub fn new(
		set_id: SetId,
		config: SetConfig,
		to_notifications: TracingUnboundedSender<Message>,
		peerset_handle: PeersetHandle,
	) -> (ProtocolHandle, ProtocolController) {
		let (to_controller, from_handle) = tracing_unbounded("mpsc_protocol_controller", 10_000);
		let handle = ProtocolHandle { to_controller };
		let nodes = config
			.reserved_nodes
			.union(&config.bootnodes.into_iter().collect())
			.map(|p| (*p, PeerState::NotConnected))
			.collect::<HashMap<PeerId, PeerState>>();
		let controller = ProtocolController {
			set_id,
			from_handle,
			num_in: 0,
			num_out: 0,
			max_in: config.in_peers,
			max_out: config.out_peers,
			reserved_nodes: config.reserved_nodes,
			reserved_only: config.reserved_only,
			nodes,
			next_periodic_alloc_slots: Instant::now(),
			to_notifications,
			peerset_handle,
		};
		(handle, controller)
	}

	/// Drive [`ProtocolController`]. This function returns when all instances of
	/// [`ProtocolHandle`] are dropped.
	pub async fn run(mut self) {
		while self.next_action().await {}
	}

	/// Perform one action. Returns `true` if it should be called again.
	///
	/// Intended for tests only. Use `run` for driving [`ProtocolController`].
	pub async fn next_action(&mut self) -> bool {
		let action = loop {
			let mut next_alloc_slots = Delay::new_at(self.next_periodic_alloc_slots).fuse();
			futures::select! {
				action = self.from_handle.next() => match action {
					Some(action) => break action,
					None => return false,
				},
				_ = next_alloc_slots => {
					self.alloc_slots();
					self.next_periodic_alloc_slots = Instant::now() + Duration::new(1, 0);
				},
			}
		};

		match action {
			Action::AddReservedPeer(peer_id) => self.on_add_reserved_peer(peer_id),
			Action::RemoveReservedPeer(peer_id) => self.on_remove_reserved_peer(peer_id),
			Action::SetReservedPeers(peer_ids) => self.on_set_reserved_peers(peer_ids),
			Action::SetReservedOnly(reserved_only) => self.on_set_reserved_only(reserved_only),
			Action::AddPeer(peer_id) => self.on_add_peer(peer_id),
			Action::RemovePeer(peer_id) => self.on_remove_peer(peer_id),
			Action::IncomingConnection(peer_id, index) =>
				self.on_incoming_connection(peer_id, index),
			Action::Dropped(peer_id, reason) => self.on_peer_dropped(peer_id, reason),
		}
		true
	}

	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		if !self.reserved_nodes.insert(peer_id) {
			return
		}
		// Discount occupied slots or connect to the node.
		match self.nodes.entry(peer_id).or_insert(PeerState::NotConnected) {
			PeerState::Connected(Direction::Inbound) => self.num_in -= 1,
			PeerState::Connected(Direction::Outbound) => self.num_out -= 1,
			PeerState::NotConnected => self.alloc_slots(),
		}
	}

	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		if !self.reserved_nodes.remove(&peer_id) {
			return
		}

		match self.nodes.entry(peer_id) {
			Entry::Occupied(mut node) => {
				if !node.get().is_connected() {
					return
				}

				if self.reserved_only {
					// If we are in reserved-only mode, the removed reserved node
					// should be disconnected.
					*node.get_mut() = PeerState::NotConnected;
					let _ = self.to_notifications.unbounded_send(Message::Drop {
						set_id: self.set_id,
						peer_id: *node.key(),
					});
					info!(
						target: "peerset",
						"Disconnecting previously reserved node {} on {:?}.",
						node.key(), self.set_id
					);
				} else {
					// Otherwise, just count occupied slots for the node.
					match node.get() {
						PeerState::Connected(Direction::Inbound) => self.num_in += 1,
						PeerState::Connected(Direction::Outbound) => self.num_out += 1,
						PeerState::NotConnected => {},
					}
				}
			},
			Entry::Vacant(_) => {
				debug_assert!(false, "Reserved node not in the list of known nodes.");
				error!(
					target: "peerset",
					"Invalid state: reserved node {} not in the list of known nodes.",
					peer_id,
				);
			},
		}
	}

	fn on_set_reserved_peers(&mut self, peer_ids: HashSet<PeerId>) {
		// Determine the difference between the current group and the new list.
		let to_insert = peer_ids.difference(&self.reserved_nodes).cloned().collect::<Vec<_>>();
		let to_remove = self.reserved_nodes.difference(&peer_ids).cloned().collect::<Vec<_>>();

		for node in to_insert {
			self.on_add_reserved_peer(node);
		}

		for node in to_remove {
			self.on_remove_reserved_peer(node);
		}
	}

	fn on_set_reserved_only(&mut self, reserved_only: bool) {
		self.reserved_only = reserved_only;

		if reserved_only {
			// Disconnect all non-reserved peers.
			for (peer_id, state) in self.nodes.iter_mut() {
				match state {
					PeerState::Connected(d) => {
						match d {
							Direction::Inbound => self.num_in -= 1,
							Direction::Outbound => self.num_out -= 1,
						}
						*state = PeerState::NotConnected;
						let _ = self.to_notifications.unbounded_send(Message::Drop {
							set_id: self.set_id,
							peer_id: *peer_id,
						});
					},
					PeerState::NotConnected => {},
				}
			}
		} else {
			// Try connecting to non-reserved peers.
			self.alloc_slots();
		}
	}

	fn on_add_peer(&mut self, peer_id: PeerId) {
		if self.nodes.insert(peer_id, PeerState::NotConnected).is_none() {
			self.alloc_slots();
		}
	}

	fn on_remove_peer(&mut self, peer_id: PeerId) {
		// Don't do anything if the node is reserved.
		if self.reserved_nodes.contains(&peer_id) {
			return
		}

		match self.nodes.remove(&peer_id) {
			Some(state) => match state {
				PeerState::Connected(d) => {
					match d {
						Direction::Inbound => self.num_in -= 1,
						Direction::Outbound => self.num_out -= 1,
					}
					let _ = self
						.to_notifications
						.unbounded_send(Message::Drop { set_id: self.set_id, peer_id });
				},
				PeerState::NotConnected => {},
			},
			None => {
				trace!(
					target: "peerset",
					"Trying to remove unknown peer {} from {:?}",
					peer_id, self.set_id,
				);
			},
		}
	}

	fn on_incoming_connection(&mut self, peer_id: PeerId, incoming_index: IncomingIndex) {
		if self.reserved_only && !self.reserved_nodes.contains(&peer_id) {
			let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
			return
		}

		// Adding incoming peer to our set of peers even before we decide whether to accept
		// it is questionable, but this is how it was implemented in the original `Peerset`.
		let state = self.nodes.entry(peer_id).or_insert(PeerState::NotConnected);
		match state {
			// If we're already connected, don't answer, as the docs mention.
			PeerState::Connected(_) => return,
			PeerState::NotConnected => {
				if self.peerset_handle.is_banned(peer_id) {
					let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
					return
				}

				let is_no_slot_occupy = self.reserved_nodes.contains(&peer_id);
				// Note that it is possible for num_in to be strictly superior to the max, in case
				// we were connected to a reserved node then marked it as not reserved.
				if self.num_in >= self.max_in && !is_no_slot_occupy {
					let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
					return
				}

				if !is_no_slot_occupy {
					self.num_in += 1;
				}
				*state = PeerState::Connected(Direction::Inbound);
				let _ = self.to_notifications.unbounded_send(Message::Accept(incoming_index));
			},
		}
	}

	fn on_peer_dropped(&mut self, peer_id: PeerId, reason: DropReason) {
		match self.nodes.entry(peer_id) {
			Entry::Occupied(mut node) => match node.get_mut() {
				PeerState::Connected(d) => {
					if !self.reserved_nodes.contains(&peer_id) {
						match d {
							Direction::Inbound => self.num_in -= 1,
							Direction::Outbound => self.num_out -= 1,
						}
					}
					self.peerset_handle.report_disconnect(peer_id);
					if let DropReason::Refused = reason {
						node.remove();
					} else {
						*node.get_mut() = PeerState::NotConnected;
					}
				},
				PeerState::NotConnected => {
					debug_assert!(false, "Received on_peer_dropped() for non-connected peer.");
					error!(
						target: "peerset",
						"Received on_peer_dropped() for non-connected peer {} on {:?}.",
						peer_id, self.set_id,
					)
				},
			},
			Entry::Vacant(_) => {
				debug_assert!(false, "Received on_peer_dropped() for unknown peer.");
				error!(
					target: "peerset",
					"Received on_peer_dropped() for unknown peer {} on {:?}.",
					peer_id, self.set_id,
				)
			},
		}
	}

	fn alloc_slots(&mut self) {
		todo!(
			"Count the number of slots we need to fill and request that number of peers from `Peerset`,
		     also passing the list of already connected peers to eliminate them from the list."
		);
	}
}
