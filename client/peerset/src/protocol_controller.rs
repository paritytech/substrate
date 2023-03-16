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
	borrow::Cow,
	collections::{hash_map::Entry, HashMap, HashSet},
	time::{Duration, Instant},
};
use wasm_timer::Delay;

use crate::{IncomingIndex, Message, SetConfig, SetId};

#[derive(Debug)]
enum Action {
	AddReservedPeer(PeerId),
	RemoveReservedPeer(PeerId),
	SetReservedPeers(HashSet<PeerId>),
	SetReservedOnly(bool),
	AddPeer(PeerId),
	RemovePeer(PeerId),
	IncomingConnection(PeerId, IncomingIndex),
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

	/// Remove a peer from a set of peers we try to connect to and disconnect a peer.
	pub fn remove_peer(&self, peer_id: PeerId) {
		let _ = self.to_controller.unbounded_send(Action::RemovePeer(peer_id));
	}

	/// Notify about incoming connection. [`ProtocolController`] will either accept or reject it.
	pub fn incoming_connection(&self, peer_id: PeerId, incoming_index: IncomingIndex) {
		let _ = self
			.to_controller
			.unbounded_send(Action::IncomingConnection(peer_id, incoming_index));
	}
}

/// Status of a connection with a peer.
#[derive(Debug)]
enum ConnectionState {
	/// We are connected through an ingoing connection.
	In,
	/// We are connected through an outgoing connection.
	Out,
	/// We are not connected.
	NotConnected,
}

impl ConnectionState {
	/// Returns true if we are connected with the node.
	fn is_connected(&self) -> bool {
		matches!(self, ConnectionState::In | ConnectionState::Out)
	}
}

impl Default for ConnectionState {
	fn default() -> ConnectionState {
		ConnectionState::NotConnected
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
	nodes: HashMap<PeerId, ConnectionState>,
	/// Next time to allocate slots. This is done once per second.
	next_periodic_alloc_slots: Instant,
	/// Outgoing channel for messages to `Notifications`.
	to_notifications: TracingUnboundedSender<Message>,
}

impl ProtocolController {
	/// Construct new [`ProtocolController`].
	pub fn new(
		set_id: SetId,
		config: SetConfig,
		to_notifications: TracingUnboundedSender<Message>,
	) -> (ProtocolHandle, ProtocolController) {
		let (to_controller, from_handle) = tracing_unbounded("mpsc_protocol_controller", 10_000);
		let handle = ProtocolHandle { to_controller };
		let nodes = config
			.reserved_nodes
			.union(&config.bootnodes.into_iter().collect())
			.map(|p| (*p, ConnectionState::NotConnected))
			.collect::<HashMap<PeerId, ConnectionState>>();
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
		}
		true
	}

	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		if !self.reserved_nodes.insert(peer_id) {
			return
		}
		// Discount occupied slots or connect to the node.
		match self.nodes.entry(peer_id).or_default() {
			ConnectionState::In => self.num_in -= 1,
			ConnectionState::Out => self.num_out -= 1,
			ConnectionState::NotConnected => self.alloc_slots(),
		}
	}

	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		if !self.reserved_nodes.remove(&peer_id) {
			return
		}
		if let Entry::Occupied(mut node) = self.nodes.entry(peer_id) {
			if self.reserved_only && node.get().is_connected() {
				// If we are in reserved-only mode, the removed reserved node
				// should be disconnected.
				// Note that we don't need to update slots, so we drop the node manually here
				// and not via [`Peer`] interface
				*node.get_mut() = ConnectionState::NotConnected;
				let _ = self
					.to_notifications
					.unbounded_send(Message::Drop { set_id: self.set_id, peer_id: *node.key() });
				info!(
					target: "peerset",
					"Disconnecting previously reserved node {} on {:?}.",
					node.key(), self.set_id
				);
			} else {
				// Otherwise, just count occupied slots for the node.
				match node.get() {
					ConnectionState::In => self.num_in += 1,
					ConnectionState::Out => self.num_out += 1,
					ConnectionState::NotConnected => {},
				}
			}
		} else {
			error!(
				target: "peerset",
				"Invalid state: reserved node {} not in the list of known nodes.",
				peer_id,
			);
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
			for peer_id in self.connected_peers().cloned().collect::<Vec<_>>().iter() {
				self.peer(&peer_id)
					.into_connected()
					.expect(
						"We are enumerating connected peers, therefore the peer is connected; qed",
					)
					.disconnect();
			}
		} else {
			// Try connecting to non-reserved peers.
			self.alloc_slots();
		}
	}

	fn on_add_peer(&mut self, peer_id: PeerId) {
		if self.nodes.insert(peer_id, ConnectionState::NotConnected).is_none() {
			self.alloc_slots();
		}
	}

	fn on_remove_peer(&mut self, peer_id: PeerId) {
		// Don't do anything if the node is reserved.
		if self.reserved_nodes.contains(&peer_id) {
			return
		}

		self.peer(&peer_id)
			.into_connected()
			.map(|connected_peer| connected_peer.disconnect());
		self.nodes.remove(&peer_id);
	}

	fn on_incoming_connection(&mut self, peer_id: PeerId, incoming_index: IncomingIndex) {
		if self.reserved_only && !self.reserved_nodes.contains(&peer_id) {
			let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
			return
		}

		let not_connected = match self.peer(&peer_id) {
			// If we're already connected, don't answer, as the docs mention.
			Peer::Connected(_) => return,
			Peer::NotConnected(peer) => peer,
			// Adding incoming peer to our set of peers even before we decide whether to accept
			// it is questionable, but this is how it was implemented in the original `Peerset`.
			Peer::Unknown(peer) => peer.discover(),
		};

		if not_connected.is_banned() {
			let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
			return
		}

		let _ = not_connected.try_accept_incoming(incoming_index);
	}

	fn peer<'a>(&'a mut self, peer_id: &'a PeerId) -> Peer<'a> {
		match self.nodes.get(peer_id) {
			None =>
				Peer::Unknown(UnknownPeer { controller: self, peer_id: Cow::Borrowed(peer_id) }),
			Some(ConnectionState::NotConnected) => Peer::NotConnected(NotConnectedPeer {
				controller: self,
				peer_id: Cow::Borrowed(peer_id),
			}),
			Some(ConnectionState::In) | Some(ConnectionState::Out) =>
				Peer::Connected(ConnectedPeer { controller: self, peer_id: Cow::Borrowed(peer_id) }),
		}
	}

	fn connected_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.nodes
			.iter()
			.filter(|(_, state)| state.is_connected())
			.map(|(peer_id, _)| peer_id)
	}

	fn alloc_slots(&mut self) {
		todo!(
			"Count the number of slots we need to fill and request that number of peers from `Peerset`,
		     also passing the list of already connected peers to eliminate them from the list."
		);
	}
}
/// Grants access to the state of a peer in the [`ProtocolController`].
pub enum Peer<'a> {
	/// We are connected to this node.
	Connected(ConnectedPeer<'a>),
	/// We are not connected to this node.
	NotConnected(NotConnectedPeer<'a>),
	/// We have never heard of this node, or it is not part of the set.
	Unknown(UnknownPeer<'a>),
}

impl<'a> Peer<'a> {
	/// If we are the `Connected` variant, returns the inner [`ConnectedPeer`]. Returns `None`
	/// otherwise.
	fn into_connected(self) -> Option<ConnectedPeer<'a>> {
		match self {
			Self::Connected(peer) => Some(peer),
			Self::NotConnected(..) | Self::Unknown(..) => None,
		}
	}

	/// If we are the `NotConnected` variant, returns the inner [`NotConnectedPeer`]. Returns `None`
	/// otherwise.
	#[cfg(test)] // Feel free to remove this if this function is needed outside of tests
	fn into_not_connected(self) -> Option<NotConnectedPeer<'a>> {
		match self {
			Self::NotConnected(peer) => Some(peer),
			Self::Connected(..) | Self::Unknown(..) => None,
		}
	}

	/// If we are the `Unknown` variant, returns the inner [`UnknownPeer`]. Returns `None`
	/// otherwise.
	#[cfg(test)] // Feel free to remove this if this function is needed outside of tests
	fn into_unknown(self) -> Option<UnknownPeer<'a>> {
		match self {
			Self::Unknown(peer) => Some(peer),
			Self::Connected(..) | Self::NotConnected(..) => None,
		}
	}
}

/// A peer that is connected to us.
pub struct ConnectedPeer<'a> {
	controller: &'a mut ProtocolController,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> ConnectedPeer<'a> {
	/// Get the `PeerId` associated to this `ConnectedPeer`.
	fn peer_id(&self) -> &PeerId {
		&self.peer_id
	}

	/// Destroys this `ConnectedPeer` and returns the `PeerId` inside of it.
	fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Switches the peer to "not connected".
	fn disconnect(self) -> NotConnectedPeer<'a> {
		let is_no_slot_occupy = self.controller.reserved_nodes.contains(&*self.peer_id);
		if let Some(state) = self.controller.nodes.get_mut(&*self.peer_id) {
			if !is_no_slot_occupy {
				match state {
					ConnectionState::In => self.controller.num_in -= 1,
					ConnectionState::Out => self.controller.num_out -= 1,
					ConnectionState::NotConnected => {
						debug_assert!(
							false,
							"State inconsistency: disconnecting a disconnected node"
						)
					},
				}
			}
			*state = ConnectionState::NotConnected;
			let _ = self.controller.to_notifications.unbounded_send(Message::Drop {
				set_id: self.controller.set_id,
				peer_id: *self.peer_id,
			});
		} else {
			debug_assert!(false, "State inconsistency: disconnecting a disconnected node");
		}

		NotConnectedPeer { controller: self.controller, peer_id: self.peer_id }
	}
}

// A peer that is not connected to us.
pub struct NotConnectedPeer<'a> {
	controller: &'a mut ProtocolController,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> NotConnectedPeer<'a> {
	/// Destroys this `NotConnectedPeer` and returns the `PeerId` inside of it.
	fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Tries to set the peer as connected as an outgoing connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Non-slot-occupying nodes don't count towards the number of slots.
	fn try_outgoing(self) -> Result<ConnectedPeer<'a>, Self> {
		let is_no_slot_occupy = self.controller.reserved_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_out to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.controller.num_out >= self.controller.max_out && !is_no_slot_occupy {
			return Err(self)
		}

		if let Some(state) = self.controller.nodes.get_mut(&*self.peer_id) {
			debug_assert!(
				matches!(state, ConnectionState::NotConnected),
				"State inconsistency: try_outgoing on a connected node"
			);
			if !is_no_slot_occupy {
				self.controller.num_out += 1;
			}
			*state = ConnectionState::Out;
			let _ = self.controller.to_notifications.unbounded_send(Message::Connect {
				set_id: self.controller.set_id,
				peer_id: *self.peer_id,
			});
		} else {
			debug_assert!(false, "State inconsistency: try_outgoing on an unknown node");
		}

		Ok(ConnectedPeer { controller: self.controller, peer_id: self.peer_id })
	}

	/// Tries to accept the peer as an incoming connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Non-slot-occupying nodes don't count towards the number of slots.
	fn try_accept_incoming(self, incoming_index: IncomingIndex) -> Result<ConnectedPeer<'a>, Self> {
		let is_no_slot_occupy = self.controller.reserved_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_in to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.controller.num_in >= self.controller.max_in && !is_no_slot_occupy {
			return Err(self)
		}

		if let Some(state) = self.controller.nodes.get_mut(&*self.peer_id) {
			debug_assert!(
				matches!(state, ConnectionState::NotConnected),
				"State inconsistency: try_accept_incoming on a connected node"
			);
			if !is_no_slot_occupy {
				self.controller.num_in += 1;
			}
			*state = ConnectionState::In;
			let _ =
				self.controller.to_notifications.unbounded_send(Message::Accept(incoming_index));
		} else {
			debug_assert!(false, "State inconsistency: try_accept_incoming on an unknown node");
		}

		Ok(ConnectedPeer { controller: self.controller, peer_id: self.peer_id })
	}

	/// Removes the peer from the list of members of the set.
	fn forget_peer(self) -> UnknownPeer<'a> {
		if self.controller.nodes.remove(&*self.peer_id).is_none() {
			debug_assert!(false, "State inconsistency: forget_peer on an unknown node");
			error!(
				target: "peerset",
				"State inconsistency with {} when forgetting peer",
				self.peer_id
			);
		};

		UnknownPeer { controller: self.controller, peer_id: self.peer_id }
	}

	fn is_banned(&self) -> bool {
		todo!("request this info from `PeerSet`");
	}
}

/// A peer that we have never heard of or that isn't part of the set.
pub struct UnknownPeer<'a> {
	controller: &'a mut ProtocolController,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> UnknownPeer<'a> {
	/// Inserts the peer identity in our list.
	///
	/// The node starts with a reputation of 0. You can adjust these default
	/// values using the `NotConnectedPeer` that this method returns.
	fn discover(self) -> NotConnectedPeer<'a> {
		if self
			.controller
			.nodes
			.insert(*self.peer_id, ConnectionState::NotConnected)
			.is_some()
		{
			debug_assert!(false, "State inconsistency: discovered already known peer");
		}
		NotConnectedPeer { controller: self.controller, peer_id: self.peer_id }
	}
}
