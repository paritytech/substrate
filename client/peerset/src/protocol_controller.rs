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

//! Protocol Controller. Generic implementation of peer management for protocols.
//! Responsible for accepting/rejecting incoming connections and initiating outgoing connections,
//! respecting the inbound and outbound peer slot counts. Communicates with `Peerset` to get and
//! update peer reputation values and sends commands to `Notifications`.

// TODO: remove this line.
#![allow(unused)]

use futures::{FutureExt, StreamExt};
use libp2p::PeerId;
use log::{error, info, trace};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_arithmetic::traits::SaturatedConversion;
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
	DisconnectPeer(PeerId),
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

	/// Demotes reserved peer to non-reserved. Does not disconnect the peer.
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

	/// Disconnect peer. You should remove the `PeerId` from the `Peerset` first
	/// to not connect to the peer again during the next slot allocation.
	pub fn disconnect_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::DisconnectPeer(peer_id));
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
#[derive(Clone, Copy, Debug)]
enum Direction {
	Inbound,
	Outbound,
}

/// Status of a connection with a peer.
#[derive(Clone, Debug)]
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
	/// Connected regular nodes.
	nodes: HashMap<PeerId, Direction>,
	/// Reserved nodes. Should be always connected and do not occupy peer slots.
	reserved_nodes: HashMap<PeerId, PeerState>,
	/// Connect only to reserved nodes.
	reserved_only: bool,
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
		let reserved_nodes =
			config.reserved_nodes.iter().map(|p| (*p, PeerState::NotConnected)).collect();
		let controller = ProtocolController {
			set_id,
			from_handle,
			num_in: 0,
			num_out: 0,
			max_in: config.in_peers,
			max_out: config.out_peers,
			nodes: HashMap::new(),
			reserved_nodes,
			reserved_only: config.reserved_only,
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
			Action::DisconnectPeer(peer_id) => self.on_disconnect_peer(peer_id),
			Action::IncomingConnection(peer_id, index) =>
				self.on_incoming_connection(peer_id, index),
			Action::Dropped(peer_id, reason) =>
				self.on_peer_dropped(peer_id, reason).unwrap_or_else(|peer_id| {
					debug_assert!(false, "Received Action::Dropped for non-connected peer.");
					error!(
						target: "peerset",
						"Received Action::Dropped for non-connected peer {} on {:?}.",
						peer_id, self.set_id,
					)
				}),
		}
		true
	}

	/// Send "accept" message to `Notifications`.
	fn accept_connection(&self, incoming_index: IncomingIndex) {
		let _ = self.to_notifications.unbounded_send(Message::Accept(incoming_index));
	}

	/// Send "reject" message to `Notifications`.
	fn reject_connection(&self, incoming_index: IncomingIndex) {
		let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
	}

	/// Send "connect" message to `Notifications`.
	fn start_connection(&self, peer_id: PeerId) {
		let _ = self
			.to_notifications
			.unbounded_send(Message::Connect { set_id: self.set_id, peer_id });
	}

	/// Send "drop" message to `Notifications`.
	fn drop_connection(&self, peer_id: PeerId) {
		let _ = self
			.to_notifications
			.unbounded_send(Message::Drop { set_id: self.set_id, peer_id });
	}

	/// Report peer disconnect event to `Peerset` for it to update peer's reputation accordingly.
	fn report_disconnect(&self, peer_id: PeerId, reason: DropReason) {
		self.peerset_handle.report_disconnect(peer_id, reason);
	}

	/// Ask `Peerset` if the peer has a reputation value not sufficent for connection with it.
	fn is_banned(&self, peer_id: PeerId) -> bool {
		self.peerset_handle.is_banned(peer_id)
	}

	/// Add the peer to the set of reserved peers. [`ProtocolCOntroller`] will try to always maintain
	/// connections with such peers.
	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		if self.reserved_nodes.contains_key(&peer_id) {
			return
		}

		// Get the peer out of non-reserved peers if it's there.
		let state = match self.nodes.remove(&peer_id) {
			Some(d) => PeerState::Connected(d),
			None => PeerState::NotConnected,
		};

		self.reserved_nodes.insert(peer_id, state.clone());

		// Discount occupied slots or connect to the node.
		match state {
			PeerState::Connected(Direction::Inbound) => self.num_in -= 1,
			PeerState::Connected(Direction::Outbound) => self.num_out -= 1,
			PeerState::NotConnected => self.alloc_slots(),
		}
	}

	/// Remove the peer from the set of reserved peers. The peer is moved to the set of regular nodes.
	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		let mut state = match self.reserved_nodes.remove(&peer_id) {
			Some(state) => state,
			None => return,
		};

		if let PeerState::Connected(direction) = state {
			if self.reserved_only {
				// Disconnect the node.
				info!(
					target: "peerset",
					"Disconnecting previously reserved node {} on {:?}.",
					peer_id, self.set_id
				);
				self.drop_connection(peer_id);
			} else {
				// Count connections as of regular node.
				match direction {
					Direction::Inbound => self.num_in += 1,
					Direction::Outbound => self.num_out += 1,
				}
			}
			// Put the node into the list of regular nodes.
			let prev = self.nodes.insert(peer_id, direction);
			assert!(prev.is_none(), "Corrupted state: reserved node was also non-reserved.");
		}
	}

	/// Replace the set of reserved peers.
	fn on_set_reserved_peers(&mut self, peer_ids: HashSet<PeerId>) {
		// Determine the difference between the current group and the new list.
		let current = self.reserved_nodes.keys().cloned().collect();
		let to_insert = peer_ids.difference(&current).cloned().collect::<Vec<_>>();
		let to_remove = current.difference(&peer_ids).cloned().collect::<Vec<_>>();

		for node in to_insert {
			self.on_add_reserved_peer(node);
		}

		for node in to_remove {
			self.on_remove_reserved_peer(node);
		}
	}

	/// Change "reserved only" flag. In "reserved only" mode we connect and accept connections to
	/// reserved nodes only.
	fn on_set_reserved_only(&mut self, reserved_only: bool) {
		self.reserved_only = reserved_only;

		if !reserved_only {
			return self.alloc_slots()
		}

		// Disconnect all non-reserved peers.
		self.nodes.keys().for_each(|peer_id| self.drop_connection(*peer_id));
	}

	/// Disconnect the peer.
	fn on_disconnect_peer(&mut self, peer_id: PeerId) {
		// Don't do anything if the node is reserved.
		if self.reserved_nodes.contains_key(&peer_id) {
			return
		}

		match self.nodes.remove(&peer_id) {
			Some(direction) => {
				match direction {
					Direction::Inbound => self.num_in -= 1,
					Direction::Outbound => self.num_out -= 1,
				}
				self.drop_connection(peer_id);
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

	/// Indicate that we received an incoming connection. Must be answered either with
	/// a corresponding `Accept` or `Reject`, except if we were already connected to this peer.
	///
	/// Note that this mechanism is orthogonal to `Connect`/`Drop`. Accepting an incoming
	/// connection implicitly means `Connect`, but incoming connections aren't cancelled by
	/// `dropped`.
	// Implementation note: because of concurrency issues, it is possible that we push a `Connect`
	// message to the output channel with a `PeerId`, and that `incoming` gets called with the same
	// `PeerId` before that message has been read by the user. In this situation we must not answer.
	fn on_incoming_connection(&mut self, peer_id: PeerId, incoming_index: IncomingIndex) {
		if self.reserved_only && !self.reserved_nodes.contains_key(&peer_id) {
			self.reject_connection(incoming_index);
			return
		}

		// Check if the node is reserved first.
		if let Some(state) = self.reserved_nodes.get_mut(&peer_id) {
			match state {
				// If we're already connected, don't answer, as the docs mention.
				PeerState::Connected(_) => {},
				PeerState::NotConnected => {
					// It's questionable whether we should check a reputation of reserved node.
					// FIXME: unable to call `self.is_banned()` because of borrowed `self`.
					if self.peerset_handle.is_banned(peer_id) {
						self.reject_connection(incoming_index);
					} else {
						*state = PeerState::Connected(Direction::Inbound);
						self.accept_connection(incoming_index);
					}
				},
			}
			return
		}

		// If we're already connected, don't answer, as the docs mention.
		if self.nodes.contains_key(&peer_id) {
			return
		}

		if self.is_banned(peer_id) {
			self.reject_connection(incoming_index);
			return
		}

		if self.num_in >= self.max_in {
			self.reject_connection(incoming_index);
			return
		}

		self.num_in += 1;
		self.nodes.insert(peer_id, Direction::Inbound);
		self.accept_connection(incoming_index);
	}

	/// Indicate that a connection with the peer was dropped.
	/// Returns `Err(PeerId)` if the peer wasn't connected or is not known to us.
	fn on_peer_dropped(&mut self, peer_id: PeerId, reason: DropReason) -> Result<(), PeerId> {
		if self.drop_reserved_peer(&peer_id)? || self.drop_regular_peer(&peer_id) {
			// The peer found and disconnected.
			self.report_disconnect(peer_id, reason);
			Ok(())
		} else {
			// The peer was not found in neither regular or reserved lists.
			Err(peer_id)
		}
	}

	/// Try dropping the peer as a reserved peer. Return `Ok(true)` if the peer was found and
	/// disconnected, `Ok(false)` if it wasn't found, `Err(PeerId)`, if the peer found, but not in
	/// connected state.
	fn drop_reserved_peer(&mut self, peer_id: &PeerId) -> Result<bool, PeerId> {
		let Some(state) = self.reserved_nodes.get_mut(peer_id) else {
			return Ok(false)
		};

		if let PeerState::Connected(_) = state {
			*state = PeerState::NotConnected;
			Ok(true)
		} else {
			Err(peer_id.clone())
		}
	}

	/// Try dropping the peer as a regular peer. Return `true` if the peer was found and
	/// disconnected, `false` if it wasn't found.
	fn drop_regular_peer(&mut self, peer_id: &PeerId) -> bool {
		let Some(direction) = self.nodes.remove(peer_id) else {
			return false
		};

		match direction {
			Direction::Inbound => self.num_in -= 1,
			Direction::Outbound => self.num_out -= 1,
		}

		true
	}

	/// Initiate outgoing connections trying to connect all reserved nodes and fill in all outgoing
	/// slots.
	fn alloc_slots(&mut self) {
		if self.num_out >= self.max_out {
			return
		}

		// Try connecting to reserved nodes first.
		self.reserved_nodes
			.iter_mut()
			.filter_map(|(peer_id, state)| {
				(matches!(state, PeerState::NotConnected) &&
					!self.peerset_handle.is_banned(*peer_id))
				.then_some({
					*state = PeerState::Connected(Direction::Outbound);
					peer_id
				})
			})
			.cloned()
			.collect::<Vec<_>>()
			.into_iter()
			.for_each(|peer_id| {
				self.start_connection(peer_id);
			});

		// Nothing more to do if we're in reserved-only mode.
		if self.reserved_only {
			return
		}

		// Fill available slots with non-reserved nodes
		let available_slots = (self.max_out - self.num_out).saturated_into();
		// Ignore reserved nodes (connected above) and already connected nodes.
		let ignored = self
			.reserved_nodes
			.keys()
			.cloned()
			.collect::<HashSet<PeerId>>()
			.union(&self.nodes.keys().cloned().collect::<HashSet<_>>())
			.cloned()
			.collect::<HashSet<PeerId>>();

		self.peerset_handle
			.outgoing_candidates(available_slots, ignored)
			.filter_map(|peer_id| match self.nodes.entry(*peer_id) {
				Entry::Occupied(_) => {
					debug_assert!(false, "`Peerset` returned a node we asked to ignore.");
					error!(
						target: "peerset",
						"`Peerset` returned a node we asked to ignore: {}.",
						peer_id
					);
					None
				},
				Entry::Vacant(entry) => {
					self.num_out += 1;
					entry.insert(Direction::Outbound);
					Some(peer_id)
				},
			})
			.cloned()
			.collect::<Vec<_>>()
			.iter()
			.for_each(|peer_id| self.start_connection(*peer_id));
	}
}
