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
//! respecting the inbound and outbound peer slot counts. Communicates with `PeerStore` to get and
//! update peer reputation values and sends commands to `Notifications`.
//!
//! Due to asynchronous nature of communication between `ProtocolController` and `Notifications`,
//! `ProtocolController` has an imperfect view of the states of the peers. To reduce this
//! desynchronization, the following measures are taken:
//!
//! 1. Network peer events from `Notifications` are prioritized over actions from external API and
//!    internal actions by `ProtocolController` (like slot allocation).
//! 2. `Notifications` ignores all commands from `ProtocolController` after sending "incoming"
//!    request until receiving the answer to this "incoming" request.
//! 3. After sending a "connect" message, `ProtocolController` switches the state of the peer from
//!    `Outbound` to `Inbound` if it receives an "incoming" request from `Notifications` for this
//!    peer.
//!
//! These measures do not eliminate confusing commands from `ProtocolController` completely,
//! so `Notifications` must correctly handle seemingly inconsistent commands, like a "connect"
//! command for the peer it thinks is already connected, and a "drop" command for a peer that
//! was previously dropped.
//!
//! Even though this does not guarantee that `ProtocolController` and `Notifications` have the same
//! view of the peers' states at any given moment, the eventual consistency is maintained.

use futures::{channel::oneshot, future::Either, FutureExt, StreamExt};
use libp2p::PeerId;
use log::{debug, error, trace, warn};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_arithmetic::traits::SaturatedConversion;
use std::{
	collections::{HashMap, HashSet},
	time::{Duration, Instant},
};
use wasm_timer::Delay;

use crate::{
	peer_store::PeerStoreProvider,
	peerset::{IncomingIndex, Message, SetConfig, SetId},
};

/// Log target for this file.
pub const LOG_TARGET: &str = "peerset";

/// External API actions.
#[derive(Debug)]
enum Action {
	/// Add a reserved peer or mark already connected peer as reserved.
	AddReservedPeer(PeerId),
	/// Remove a reserved peer.
	RemoveReservedPeer(PeerId),
	/// Update reserved peers to match the provided set.
	SetReservedPeers(HashSet<PeerId>),
	/// Set/unset reserved-only mode.
	SetReservedOnly(bool),
	/// Disconnect a peer.
	DisconnectPeer(PeerId),
	/// Get the list of reserved peers.
	GetReservedPeers(oneshot::Sender<Vec<PeerId>>),
}

/// Network events from `Notifications`.
#[derive(Debug)]
enum Event {
	/// Incoming connection from the peer.
	IncomingConnection(PeerId, IncomingIndex),
	/// Connection with the peer dropped.
	Dropped(PeerId),
}

/// Shared handle to [`ProtocolController`]. Distributed around the code outside of the
/// protocol implementation.
#[derive(Debug, Clone)]
pub struct ProtocolHandle {
	/// Actions from outer API.
	actions_tx: TracingUnboundedSender<Action>,
	/// Connection events from `Notifications`. We prioritize them over actions.
	events_tx: TracingUnboundedSender<Event>,
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
		let _ = self.actions_tx.unbounded_send(Action::AddReservedPeer(peer_id));
	}

	/// Demotes reserved peer to non-reserved. Does not disconnect the peer.
	///
	/// Has no effect if the node was not a reserved peer.
	pub fn remove_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.actions_tx.unbounded_send(Action::RemoveReservedPeer(peer_id));
	}

	/// Set reserved peers to the new set.
	pub fn set_reserved_peers(&self, peer_ids: HashSet<PeerId>) {
		let _ = self.actions_tx.unbounded_send(Action::SetReservedPeers(peer_ids));
	}

	/// Sets whether or not [`ProtocolController`] only has connections with nodes marked
	/// as reserved for the given set.
	pub fn set_reserved_only(&self, reserved: bool) {
		let _ = self.actions_tx.unbounded_send(Action::SetReservedOnly(reserved));
	}

	/// Disconnect peer. You should remove the `PeerId` from the `PeerStore` first
	/// to not connect to the peer again during the next slot allocation.
	pub fn disconnect_peer(&self, peer_id: PeerId) {
		let _ = self.actions_tx.unbounded_send(Action::DisconnectPeer(peer_id));
	}

	/// Get the list of reserved peers.
	pub fn reserved_peers(&self, pending_response: oneshot::Sender<Vec<PeerId>>) {
		let _ = self.actions_tx.unbounded_send(Action::GetReservedPeers(pending_response));
	}

	/// Notify about incoming connection. [`ProtocolController`] will either accept or reject it.
	pub fn incoming_connection(&self, peer_id: PeerId, incoming_index: IncomingIndex) {
		let _ = self
			.events_tx
			.unbounded_send(Event::IncomingConnection(peer_id, incoming_index));
	}

	/// Notify that connection was dropped (either refused or disconnected).
	pub fn dropped(&self, peer_id: PeerId) {
		let _ = self.events_tx.unbounded_send(Event::Dropped(peer_id));
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
	/// Receiver for outer API messages from [`ProtocolHandle`].
	actions_rx: TracingUnboundedReceiver<Action>,
	/// Receiver for connection events from `Notifications` sent via [`ProtocolHandle`].
	events_rx: TracingUnboundedReceiver<Event>,
	/// Number of occupied slots for incoming connections (not counting reserved nodes).
	num_in: u32,
	/// Number of occupied slots for outgoing connections (not counting reserved nodes).
	num_out: u32,
	/// Maximum number of slots for incoming connections (not counting reserved nodes).
	max_in: u32,
	/// Maximum number of slots for outgoing connections (not counting reserved nodes).
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
	/// `PeerStore` handle for checking peer reputation values and getting connection candidates
	/// with highest reputation.
	peer_store: Box<dyn PeerStoreProvider>,
}

impl ProtocolController {
	/// Construct new [`ProtocolController`].
	pub fn new(
		set_id: SetId,
		config: SetConfig,
		to_notifications: TracingUnboundedSender<Message>,
		peer_store: Box<dyn PeerStoreProvider>,
	) -> (ProtocolHandle, ProtocolController) {
		let (actions_tx, actions_rx) = tracing_unbounded("mpsc_api_protocol", 10_000);
		let (events_tx, events_rx) = tracing_unbounded("mpsc_notifications_protocol", 10_000);
		let handle = ProtocolHandle { actions_tx, events_tx };
		peer_store.register_protocol(handle.clone());
		let reserved_nodes =
			config.reserved_nodes.iter().map(|p| (*p, PeerState::NotConnected)).collect();
		let controller = ProtocolController {
			set_id,
			actions_rx,
			events_rx,
			num_in: 0,
			num_out: 0,
			max_in: config.in_peers,
			max_out: config.out_peers,
			nodes: HashMap::new(),
			reserved_nodes,
			reserved_only: config.reserved_only,
			next_periodic_alloc_slots: Instant::now(),
			to_notifications,
			peer_store,
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
		let either = loop {
			let mut next_alloc_slots = Delay::new_at(self.next_periodic_alloc_slots).fuse();

			// See the module doc for why we use `select_biased!`.
			futures::select_biased! {
				event = self.events_rx.next() => match event {
					Some(event) => break Either::Left(event),
					None => return false,
				},
				action = self.actions_rx.next() => match action {
					Some(action) => break Either::Right(action),
					None => return false,
				},
				_ = next_alloc_slots => {
					self.alloc_slots();
					self.next_periodic_alloc_slots = Instant::now() + Duration::new(1, 0);
				},
			}
		};

		match either {
			Either::Left(event) => self.process_event(event),
			Either::Right(action) => self.process_action(action),
		}

		true
	}

	/// Process connection event.
	fn process_event(&mut self, event: Event) {
		match event {
			Event::IncomingConnection(peer_id, index) =>
				self.on_incoming_connection(peer_id, index),
			Event::Dropped(peer_id) => self.on_peer_dropped(peer_id),
		}
	}

	/// Process action command.
	fn process_action(&mut self, action: Action) {
		match action {
			Action::AddReservedPeer(peer_id) => self.on_add_reserved_peer(peer_id),
			Action::RemoveReservedPeer(peer_id) => self.on_remove_reserved_peer(peer_id),
			Action::SetReservedPeers(peer_ids) => self.on_set_reserved_peers(peer_ids),
			Action::SetReservedOnly(reserved_only) => self.on_set_reserved_only(reserved_only),
			Action::DisconnectPeer(peer_id) => self.on_disconnect_peer(peer_id),
			Action::GetReservedPeers(pending_response) =>
				self.on_get_reserved_peers(pending_response),
		}
	}

	/// Send "accept" message to `Notifications`.
	fn accept_connection(&mut self, incoming_index: IncomingIndex) {
		trace!(
			target: LOG_TARGET,
			"Accepting {:?} on {:?} ({}/{} num_in/max_in).",
			incoming_index,
			self.set_id,
			self.num_in,
			self.max_in,
		);

		let _ = self.to_notifications.unbounded_send(Message::Accept(incoming_index));
	}

	/// Send "reject" message to `Notifications`.
	fn reject_connection(&mut self, incoming_index: IncomingIndex) {
		trace!(
			target: LOG_TARGET,
			"Rejecting {:?} on {:?} ({}/{} num_in/max_in).",
			incoming_index,
			self.set_id,
			self.num_in,
			self.max_in,
		);

		let _ = self.to_notifications.unbounded_send(Message::Reject(incoming_index));
	}

	/// Send "connect" message to `Notifications`.
	fn start_connection(&mut self, peer_id: PeerId) {
		trace!(
			target: LOG_TARGET,
			"Connecting to {} on {:?} ({}/{} num_out/max_out).",
			peer_id,
			self.set_id,
			self.num_out,
			self.max_out,
		);

		let _ = self
			.to_notifications
			.unbounded_send(Message::Connect { set_id: self.set_id, peer_id });
	}

	/// Send "drop" message to `Notifications`.
	fn drop_connection(&mut self, peer_id: PeerId) {
		trace!(
			target: LOG_TARGET,
			"Dropping {} on {:?} ({}/{} num_in/max_in, {}/{} num_out/max_out).",
			peer_id,
			self.set_id,
			self.num_in,
			self.max_in,
			self.num_out,
			self.max_out,
		);

		let _ = self
			.to_notifications
			.unbounded_send(Message::Drop { set_id: self.set_id, peer_id });
	}

	/// Report peer disconnect event to `PeerStore` for it to update peer's reputation accordingly.
	/// Should only be called if the remote node disconnected us, not the other way around.
	fn report_disconnect(&mut self, peer_id: PeerId) {
		self.peer_store.report_disconnect(peer_id);
	}

	/// Ask `Peerset` if the peer has a reputation value not sufficent for connection with it.
	fn is_banned(&self, peer_id: &PeerId) -> bool {
		self.peer_store.is_banned(peer_id)
	}

	/// Add the peer to the set of reserved peers. [`ProtocolController`] will try to always
	/// maintain connections with such peers.
	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		if self.reserved_nodes.contains_key(&peer_id) {
			warn!(
				target: LOG_TARGET,
				"Trying to add an already reserved node as reserved: {peer_id}.",
			);
			return
		}

		// Get the peer out of non-reserved peers if it's there.
		let state = match self.nodes.remove(&peer_id) {
			Some(direction) => {
				trace!(
					target: LOG_TARGET,
					"Marking previously connected node {peer_id} ({direction:?}) as reserved.",
				);
				PeerState::Connected(direction)
			},
			None => {
				trace!(target: LOG_TARGET, "Adding reserved node {peer_id}.");
				PeerState::NotConnected
			},
		};

		self.reserved_nodes.insert(peer_id, state.clone());

		// Discount occupied slots or connect to the node.
		match state {
			PeerState::Connected(Direction::Inbound) => self.num_in -= 1,
			PeerState::Connected(Direction::Outbound) => self.num_out -= 1,
			PeerState::NotConnected => self.alloc_slots(),
		}
	}

	/// Remove the peer from the set of reserved peers. The peer is moved to the set of regular
	/// nodes.
	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		let state = match self.reserved_nodes.remove(&peer_id) {
			Some(state) => state,
			None => {
				warn!(target: LOG_TARGET, "Trying to remove unknown reserved node: {peer_id}.");
				return
			},
		};

		if let PeerState::Connected(direction) = state {
			if self.reserved_only {
				// Disconnect the node.
				trace!(
					target: LOG_TARGET,
					"Disconnecting previously reserved node {} ({:?}) on {:?}.",
					peer_id,
					direction,
					self.set_id,
				);
				self.drop_connection(peer_id);
			} else {
				// Count connections as of regular node.
				trace!(
					target: LOG_TARGET,
					"Making a connected reserved node {} ({:?}) on {:?} a regular one.",
					peer_id,
					direction,
					self.set_id,
				);

				match direction {
					Direction::Inbound => self.num_in += 1,
					Direction::Outbound => self.num_out += 1,
				}

				// Put the node into the list of regular nodes.
				let prev = self.nodes.insert(peer_id, direction);
				assert!(prev.is_none(), "Corrupted state: reserved node was also non-reserved.");
			}
		} else {
			trace!(target: LOG_TARGET, "Removed disconnected reserved node {peer_id}.");
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
		trace!(target: LOG_TARGET, "Set reserved only: {reserved_only}");

		self.reserved_only = reserved_only;

		if !reserved_only {
			return self.alloc_slots()
		}

		// Disconnect all non-reserved peers.
		self.nodes
			.iter()
			.map(|(k, v)| (*k, *v))
			.collect::<Vec<(_, _)>>()
			.iter()
			.for_each(|(peer_id, direction)| {
				// Update counters in the loop for `drop_connection` to report the correct number.
				match direction {
					Direction::Inbound => self.num_in -= 1,
					Direction::Outbound => self.num_out -= 1,
				}
				self.drop_connection(*peer_id)
			});
		self.nodes.clear();
	}

	/// Get the list of reserved peers.
	fn on_get_reserved_peers(&self, pending_response: oneshot::Sender<Vec<PeerId>>) {
		let _ = pending_response.send(self.reserved_nodes.keys().cloned().collect());
	}

	/// Disconnect the peer.
	fn on_disconnect_peer(&mut self, peer_id: PeerId) {
		// Don't do anything if the node is reserved.
		if self.reserved_nodes.contains_key(&peer_id) {
			warn!(
				target: LOG_TARGET,
				"Ignoring request to disconnect reserved peer {} from {:?}.", peer_id, self.set_id,
			);
			return
		}

		match self.nodes.remove(&peer_id) {
			Some(direction) => {
				trace!(target: LOG_TARGET, "Disconnecting peer {peer_id} ({direction:?}).");
				match direction {
					Direction::Inbound => self.num_in -= 1,
					Direction::Outbound => self.num_out -= 1,
				}
				self.drop_connection(peer_id);
			},
			None => {
				debug!(
					target: LOG_TARGET,
					"Trying to disconnect unknown peer {} from {:?}.", peer_id, self.set_id,
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
	// Implementation note: because of concurrency issues, `ProtocolController` has an imperfect
	// view of the peers' states, and may issue commands for a peer after `Notifications` received
	// an incoming request for that peer. In this case, `Notifications` ignores all the commands
	// until it receives a response for the incoming request to `ProtocolController`, so we must
	// ensure we handle this incoming request correctly.
	fn on_incoming_connection(&mut self, peer_id: PeerId, incoming_index: IncomingIndex) {
		trace!(target: LOG_TARGET, "Incoming connection from peer {peer_id} ({incoming_index:?}).",);

		if self.reserved_only && !self.reserved_nodes.contains_key(&peer_id) {
			self.reject_connection(incoming_index);
			return
		}

		// Check if the node is reserved first.
		if let Some(state) = self.reserved_nodes.get_mut(&peer_id) {
			match state {
				PeerState::Connected(ref mut direction) => {
					// We are accepting an incoming connection, so ensure the direction is inbound.
					// (See the implementation note above.)
					*direction = Direction::Inbound;
					self.accept_connection(incoming_index);
				},
				PeerState::NotConnected =>
					if self.peer_store.is_banned(&peer_id) {
						self.reject_connection(incoming_index);
					} else {
						*state = PeerState::Connected(Direction::Inbound);
						self.accept_connection(incoming_index);
					},
			}
			return
		}

		// If we're already connected, pretend we are not connected and decide on the node again.
		// (See the note above.)
		if let Some(direction) = self.nodes.remove(&peer_id) {
			trace!(
				target: LOG_TARGET,
				"Handling incoming connection from peer {} we think we already connected as {:?}.",
				peer_id,
				direction,
			);
			match direction {
				Direction::Inbound => self.num_in -= 1,
				Direction::Outbound => self.num_out -= 1,
			}
		}

		if self.num_in >= self.max_in {
			self.reject_connection(incoming_index);
			return
		}

		if self.is_banned(&peer_id) {
			self.reject_connection(incoming_index);
			return
		}

		self.num_in += 1;
		self.nodes.insert(peer_id, Direction::Inbound);
		self.accept_connection(incoming_index);
	}

	/// Indicate that a connection with the peer was dropped.
	fn on_peer_dropped(&mut self, peer_id: PeerId) {
		self.on_peer_dropped_inner(peer_id).unwrap_or_else(|peer_id| {
			// We do not assert here, because due to asynchronous nature of communication
			// between `ProtocolController` and `Notifications` we can receive `Action::Dropped`
			// for a peer we already disconnected ourself.
			trace!(
				target: LOG_TARGET,
				"Received `Action::Dropped` for not connected peer {} on {:?}.",
				peer_id,
				self.set_id,
			)
		});
	}

	/// Indicate that a connection with the peer was dropped.
	/// Returns `Err(PeerId)` if the peer wasn't connected or is not known to us.
	fn on_peer_dropped_inner(&mut self, peer_id: PeerId) -> Result<(), PeerId> {
		if self.drop_reserved_peer(&peer_id)? || self.drop_regular_peer(&peer_id) {
			// The peer found and disconnected.
			self.report_disconnect(peer_id);
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

		if let PeerState::Connected(direction) = state {
			trace!(target: LOG_TARGET, "Reserved peer {peer_id} ({direction:?}) dropped.");
			*state = PeerState::NotConnected;
			Ok(true)
		} else {
			Err(*peer_id)
		}
	}

	/// Try dropping the peer as a regular peer. Return `true` if the peer was found and
	/// disconnected, `false` if it wasn't found.
	fn drop_regular_peer(&mut self, peer_id: &PeerId) -> bool {
		let Some(direction) = self.nodes.remove(peer_id) else {
			return false
		};

		trace!(target: LOG_TARGET, "Peer {peer_id} ({direction:?}) dropped.");

		match direction {
			Direction::Inbound => self.num_in -= 1,
			Direction::Outbound => self.num_out -= 1,
		}

		true
	}

	/// Initiate outgoing connections trying to connect all reserved nodes and fill in all outgoing
	/// slots.
	fn alloc_slots(&mut self) {
		// Try connecting to reserved nodes first, ignoring nodes with outstanding events/actions.
		self.reserved_nodes
			.iter_mut()
			.filter_map(|(peer_id, state)| {
				(!state.is_connected() && !self.peer_store.is_banned(peer_id)).then(|| {
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

		// Nothing more to do if we're in reserved-only mode or don't have slots available.
		if self.reserved_only || self.num_out >= self.max_out {
			return
		}

		// Fill available slots.
		let available_slots = (self.max_out - self.num_out).saturated_into();

		// Ignore reserved nodes (connected above), already connected nodes, and nodes with
		// outstanding events/actions.
		let ignored = self
			.reserved_nodes
			.keys()
			.collect::<HashSet<&PeerId>>()
			.union(&self.nodes.keys().collect::<HashSet<&PeerId>>())
			.cloned()
			.collect();

		let candidates = self
			.peer_store
			.outgoing_candidates(available_slots, ignored)
			.into_iter()
			.filter_map(|peer_id| {
				(!self.reserved_nodes.contains_key(&peer_id) && !self.nodes.contains_key(&peer_id))
					.then_some(peer_id)
					.or_else(|| {
						error!(
							target: LOG_TARGET,
							"`PeerStore` returned a node we asked to ignore: {peer_id}.",
						);
						debug_assert!(false, "`PeerStore` returned a node we asked to ignore.");
						None
					})
			})
			.collect::<Vec<_>>();

		if candidates.len() > available_slots {
			error!(
				target: LOG_TARGET,
				"`PeerStore` returned more nodes than there are slots available.",
			);
			debug_assert!(false, "`PeerStore` returned more nodes than there are slots available.");
		}

		candidates.into_iter().take(available_slots).for_each(|peer_id| {
			self.num_out += 1;
			self.nodes.insert(peer_id, Direction::Outbound);
			self.start_connection(peer_id);
		})
	}
}

#[cfg(test)]
mod tests {
	use super::{Direction, PeerState, ProtocolController, ProtocolHandle};
	use crate::{
		peer_store::PeerStoreProvider,
		peerset::{IncomingIndex, Message, SetConfig, SetId},
		ReputationChange,
	};
	use libp2p::PeerId;
	use sc_utils::mpsc::{tracing_unbounded, TryRecvError};
	use std::collections::HashSet;

	mockall::mock! {
		#[derive(Debug)]
		pub PeerStoreHandle {}

		impl PeerStoreProvider for PeerStoreHandle {
			fn is_banned(&self, peer_id: &PeerId) -> bool;
			fn register_protocol(&self, protocol_handle: ProtocolHandle);
			fn report_disconnect(&mut self, peer_id: PeerId);
			fn report_peer(&mut self, peer_id: PeerId, change: ReputationChange);
			fn peer_reputation(&self, peer_id: &PeerId) -> i32;
			fn outgoing_candidates<'a>(&self, count: usize, ignored: HashSet<&'a PeerId>) -> Vec<PeerId>;
		}
	}

	#[test]
	fn reserved_nodes_are_connected_dropped_and_accepted() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		// Add first reserved node via config.
		let config = SetConfig {
			in_peers: 0,
			out_peers: 0,
			bootnodes: Vec::new(),
			reserved_nodes: std::iter::once(reserved1).collect(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(4).return_const(false);
		peer_store.expect_report_disconnect().times(2).return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Add second reserved node at runtime (this currently calls `alloc_slots` internally).
		controller.on_add_reserved_peer(reserved2);

		// Initiate connections (currently, `alloc_slots` is also called internally in
		// `on_add_reserved_peer` above).
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));

		// Reserved peers do not occupy slots.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Drop connections to be able to accept reserved nodes.
		controller.on_peer_dropped(reserved1);
		controller.on_peer_dropped(reserved2);

		// Incoming connection from `reserved1`.
		let incoming1 = IncomingIndex(1);
		controller.on_incoming_connection(reserved1, incoming1);
		assert_eq!(rx.try_recv().unwrap(), Message::Accept(incoming1));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Incoming connection from `reserved2`.
		let incoming2 = IncomingIndex(2);
		controller.on_incoming_connection(reserved2, incoming2);
		assert_eq!(rx.try_recv().unwrap(), Message::Accept(incoming2));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Reserved peers do not occupy slots.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn banned_reserved_nodes_are_not_connected_and_not_accepted() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		// Add first reserved node via config.
		let config = SetConfig {
			in_peers: 0,
			out_peers: 0,
			bootnodes: Vec::new(),
			reserved_nodes: std::iter::once(reserved1).collect(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(6).return_const(true);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Add second reserved node at runtime (this currently calls `alloc_slots` internally).
		controller.on_add_reserved_peer(reserved2);

		// Initiate connections.
		controller.alloc_slots();

		// No slots occupied.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// No commands are generated.
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Incoming connection from `reserved1`.
		let incoming1 = IncomingIndex(1);
		controller.on_incoming_connection(reserved1, incoming1);
		assert_eq!(rx.try_recv().unwrap(), Message::Reject(incoming1));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Incoming connection from `reserved2`.
		let incoming2 = IncomingIndex(2);
		controller.on_incoming_connection(reserved2, incoming2);
		assert_eq!(rx.try_recv().unwrap(), Message::Reject(incoming2));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// No slots occupied.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn we_try_to_reconnect_to_dropped_reserved_nodes() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		// Add first reserved node via config.
		let config = SetConfig {
			in_peers: 0,
			out_peers: 0,
			bootnodes: Vec::new(),
			reserved_nodes: std::iter::once(reserved1).collect(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(4).return_const(false);
		peer_store.expect_report_disconnect().times(2).return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Add second reserved node at runtime (this calls `alloc_slots` internally).
		controller.on_add_reserved_peer(reserved2);

		// Initiate connections (actually redundant, see previous comment).
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));

		// Drop both reserved nodes.
		controller.on_peer_dropped(reserved1);
		controller.on_peer_dropped(reserved2);

		// Initiate connections.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));

		// No slots occupied.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn nodes_supplied_by_peer_store_are_connected() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let candidates = vec![peer1, peer2];

		let config = SetConfig {
			in_peers: 0,
			// Less slots than candidates.
			out_peers: 2,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_outgoing_candidates().once().return_const(candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		// Only first two peers are connected (we only have 2 slots).
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer2 }));

		// Outgoing slots occupied.
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);

		// No more nodes are connected.
		controller.alloc_slots();
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// No more slots occupied.
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn both_reserved_nodes_and_nodes_supplied_by_peer_store_are_connected() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();
		let regular1 = PeerId::random();
		let regular2 = PeerId::random();
		let outgoing_candidates = vec![regular1, regular2];
		let reserved_nodes = [reserved1, reserved2].iter().cloned().collect();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes,
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(2).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 4);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: regular1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: regular2 }));
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn if_slots_are_freed_we_try_to_allocate_them_again() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let peer3 = PeerId::random();
		let candidates1 = vec![peer1, peer2];
		let candidates2 = vec![peer3];

		let config = SetConfig {
			in_peers: 0,
			// Less slots than candidates.
			out_peers: 2,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_outgoing_candidates().once().return_const(candidates1);
		peer_store.expect_outgoing_candidates().once().return_const(candidates2);
		peer_store.expect_report_disconnect().times(2).return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		// Only first two peers are connected (we only have 2 slots).
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer2 }));

		// Outgoing slots occupied.
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);

		// No more nodes are connected.
		controller.alloc_slots();
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// No more slots occupied.
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);

		// Drop peers.
		controller.on_peer_dropped(peer1);
		controller.on_peer_dropped(peer2);

		// Slots are freed.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Initiate connections.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		// Peers are connected.
		assert_eq!(messages.len(), 1);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer3 }));

		// Outgoing slots occupied.
		assert_eq!(controller.num_out, 1);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn in_reserved_only_mode_no_peers_are_requested_from_peer_store_and_connected() {
		let config = SetConfig {
			in_peers: 0,
			// Make sure we have slots available.
			out_peers: 2,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();

		// No nodes are connected.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
	}

	#[test]
	fn in_reserved_only_mode_no_regular_peers_are_accepted() {
		let config = SetConfig {
			// Make sure we have slots available.
			in_peers: 2,
			out_peers: 0,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		let peer = PeerId::random();
		let incoming_index = IncomingIndex(1);
		controller.on_incoming_connection(peer, incoming_index);

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		// Peer is rejected.
		assert_eq!(messages.len(), 1);
		assert!(messages.contains(&Message::Reject(incoming_index)));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn disabling_reserved_only_mode_allows_to_connect_to_peers() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let candidates = vec![peer1, peer2];

		let config = SetConfig {
			in_peers: 0,
			// Make sure we have slots available.
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_outgoing_candidates().once().return_const(candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();

		// No nodes are connected.
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Disable reserved-only mode (this also connects to peers).
		controller.on_set_reserved_only(false);

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}

		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer2 }));
		assert_eq!(controller.num_out, 2);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn enabling_reserved_only_mode_disconnects_regular_peers() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();
		let regular1 = PeerId::random();
		let regular2 = PeerId::random();
		let outgoing_candidates = vec![regular1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [reserved1, reserved2].iter().cloned().collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(3).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Connect `regular1` as outbound.
		controller.alloc_slots();

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 3);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: regular1 }));
		assert_eq!(controller.num_out, 1);
		assert_eq!(controller.num_in, 0);

		// Connect `regular2` as inbound.
		let incoming_index = IncomingIndex(1);
		controller.on_incoming_connection(regular2, incoming_index);
		assert_eq!(rx.try_recv().unwrap(), Message::Accept(incoming_index));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.num_out, 1);
		assert_eq!(controller.num_in, 1);

		// Switch to reserved-only mode.
		controller.on_set_reserved_only(true);

		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Drop { set_id: SetId::from(0), peer_id: regular1 }));
		assert!(messages.contains(&Message::Drop { set_id: SetId::from(0), peer_id: regular2 }));
		assert_eq!(controller.nodes.len(), 0);
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn removed_disconnected_reserved_node_is_forgotten() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [reserved1, reserved2].iter().cloned().collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert_eq!(controller.reserved_nodes.len(), 2);
		assert_eq!(controller.nodes.len(), 0);
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		controller.on_remove_reserved_peer(reserved1);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.reserved_nodes.len(), 1);
		assert!(!controller.reserved_nodes.contains_key(&reserved1));
		assert_eq!(controller.nodes.len(), 0);
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);
	}

	#[test]
	fn removed_connected_reserved_node_is_disconnected_in_reserved_only_mode() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [reserved1, reserved2].iter().cloned().collect(),
			reserved_only: true,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(2).return_const(false);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Initiate connections.
		controller.alloc_slots();
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved1 }));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));
		assert_eq!(controller.reserved_nodes.len(), 2);
		assert!(controller.reserved_nodes.contains_key(&reserved1));
		assert!(controller.reserved_nodes.contains_key(&reserved2));
		assert!(controller.nodes.is_empty());

		// Remove reserved node
		controller.on_remove_reserved_peer(reserved1);
		assert_eq!(
			rx.try_recv().unwrap(),
			Message::Drop { set_id: SetId::from(0), peer_id: reserved1 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.reserved_nodes.len(), 1);
		assert!(controller.reserved_nodes.contains_key(&reserved2));
		assert!(controller.nodes.is_empty());
	}

	#[test]
	fn removed_connected_reserved_nodes_become_regular_in_non_reserved_mode() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [peer1, peer2].iter().cloned().collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(2).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(Vec::new());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `peer1` as inbound, `peer2` as outbound.
		controller.on_incoming_connection(peer1, IncomingIndex(1));
		controller.alloc_slots();
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer2 }));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Remove reserved nodes (and make them regular)
		controller.on_remove_reserved_peer(peer1);
		controller.on_remove_reserved_peer(peer2);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.nodes.len(), 2);
		assert!(matches!(controller.nodes.get(&peer1), Some(Direction::Inbound)));
		assert!(matches!(controller.nodes.get(&peer2), Some(Direction::Outbound)));
		assert_eq!(controller.num_out, 1);
		assert_eq!(controller.num_in, 1);
	}

	#[test]
	fn regular_nodes_stop_occupying_slots_when_become_reserved() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let outgoing_candidates = vec![peer1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `peer1` as outbound & `peer2` as inbound.
		controller.alloc_slots();
		controller.on_incoming_connection(peer2, IncomingIndex(1));
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert_eq!(controller.num_in, 1);
		assert_eq!(controller.num_out, 1);

		controller.on_add_reserved_peer(peer1);
		controller.on_add_reserved_peer(peer2);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.num_in, 0);
		assert_eq!(controller.num_out, 0);
	}

	#[test]
	fn disconnecting_regular_peers_work() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let outgoing_candidates = vec![peer1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `peer1` as outbound & `peer2` as inbound.
		controller.alloc_slots();
		controller.on_incoming_connection(peer2, IncomingIndex(1));
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert_eq!(controller.nodes.len(), 2);
		assert!(matches!(controller.nodes.get(&peer1), Some(Direction::Outbound)));
		assert!(matches!(controller.nodes.get(&peer2), Some(Direction::Inbound)));
		assert_eq!(controller.num_in, 1);
		assert_eq!(controller.num_out, 1);

		controller.on_disconnect_peer(peer1);
		assert_eq!(
			rx.try_recv().unwrap(),
			Message::Drop { set_id: SetId::from(0), peer_id: peer1 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.nodes.len(), 1);
		assert!(!controller.nodes.contains_key(&peer1));
		assert_eq!(controller.num_in, 1);
		assert_eq!(controller.num_out, 0);

		controller.on_disconnect_peer(peer2);
		assert_eq!(
			rx.try_recv().unwrap(),
			Message::Drop { set_id: SetId::from(0), peer_id: peer2 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.nodes.len(), 0);
		assert_eq!(controller.num_in, 0);
		assert_eq!(controller.num_out, 0);
	}

	#[test]
	fn disconnecting_reserved_peers_is_a_noop() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [reserved1, reserved2].iter().cloned().collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(2).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(Vec::new());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `reserved1` as inbound & `reserved2` as outbound.
		controller.on_incoming_connection(reserved1, IncomingIndex(1));
		controller.alloc_slots();
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));
		assert!(matches!(
			controller.reserved_nodes.get(&reserved1),
			Some(PeerState::Connected(Direction::Inbound))
		));
		assert!(matches!(
			controller.reserved_nodes.get(&reserved2),
			Some(PeerState::Connected(Direction::Outbound))
		));

		controller.on_disconnect_peer(reserved1);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(
			controller.reserved_nodes.get(&reserved1),
			Some(PeerState::Connected(Direction::Inbound))
		));

		controller.on_disconnect_peer(reserved2);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(
			controller.reserved_nodes.get(&reserved2),
			Some(PeerState::Connected(Direction::Outbound))
		));
	}

	#[test]
	fn dropping_regular_peers_work() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let outgoing_candidates = vec![peer1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);
		peer_store.expect_report_disconnect().times(2).return_const(());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `peer1` as outbound & `peer2` as inbound.
		controller.alloc_slots();
		controller.on_incoming_connection(peer2, IncomingIndex(1));
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: peer1 }));
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert_eq!(controller.nodes.len(), 2);
		assert!(matches!(controller.nodes.get(&peer1), Some(Direction::Outbound)));
		assert!(matches!(controller.nodes.get(&peer2), Some(Direction::Inbound)));
		assert_eq!(controller.num_in, 1);
		assert_eq!(controller.num_out, 1);

		controller.on_peer_dropped(peer1);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.nodes.len(), 1);
		assert!(!controller.nodes.contains_key(&peer1));
		assert_eq!(controller.num_in, 1);
		assert_eq!(controller.num_out, 0);

		controller.on_peer_dropped(peer2);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert_eq!(controller.nodes.len(), 0);
		assert_eq!(controller.num_in, 0);
		assert_eq!(controller.num_out, 0);
	}

	#[test]
	fn incoming_request_for_connected_reserved_node_switches_it_to_inbound() {
		let reserved1 = PeerId::random();
		let reserved2 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: [reserved1, reserved2].iter().cloned().collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(2).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(Vec::new());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `reserved1` as inbound & `reserved2` as outbound.
		controller.on_incoming_connection(reserved1, IncomingIndex(1));
		controller.alloc_slots();
		let mut messages = Vec::new();
		while let Some(message) = rx.try_recv().ok() {
			messages.push(message);
		}
		assert_eq!(messages.len(), 2);
		assert!(messages.contains(&Message::Accept(IncomingIndex(1))));
		assert!(messages.contains(&Message::Connect { set_id: SetId::from(0), peer_id: reserved2 }));
		assert!(matches!(
			controller.reserved_nodes.get(&reserved1),
			Some(PeerState::Connected(Direction::Inbound))
		));
		assert!(matches!(
			controller.reserved_nodes.get(&reserved2),
			Some(PeerState::Connected(Direction::Outbound))
		));

		// Incoming request for `reserved1`.
		controller.on_incoming_connection(reserved1, IncomingIndex(2));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(2)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(
			controller.reserved_nodes.get(&reserved1),
			Some(PeerState::Connected(Direction::Inbound))
		));

		// Incoming request for `reserved2`.
		controller.on_incoming_connection(reserved2, IncomingIndex(3));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(3)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(
			controller.reserved_nodes.get(&reserved2),
			Some(PeerState::Connected(Direction::Inbound))
		));
	}

	#[test]
	fn incoming_request_for_connected_regular_node_switches_it_to_inbound() {
		let regular1 = PeerId::random();
		let regular2 = PeerId::random();
		let outgoing_candidates = vec![regular1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().times(3).return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Connect `regular1` as outbound.
		controller.alloc_slots();
		assert_eq!(
			rx.try_recv().ok().unwrap(),
			Message::Connect { set_id: SetId::from(0), peer_id: regular1 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular1).unwrap(), Direction::Outbound,));

		// Connect `regular2` as inbound.
		controller.on_incoming_connection(regular2, IncomingIndex(0));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(0)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular2).unwrap(), Direction::Inbound,));

		// Incoming request for `regular1`.
		controller.on_incoming_connection(regular1, IncomingIndex(1));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular1).unwrap(), Direction::Inbound,));

		// Incoming request for `regular2`.
		controller.on_incoming_connection(regular2, IncomingIndex(2));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(2)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular2).unwrap(), Direction::Inbound,));
	}

	#[test]
	fn incoming_request_for_connected_node_is_rejected_if_its_banned() {
		let regular1 = PeerId::random();
		let regular2 = PeerId::random();
		let outgoing_candidates = vec![regular1];

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);
		peer_store.expect_is_banned().times(2).return_const(true);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Connect `regular1` as outbound.
		controller.alloc_slots();
		assert_eq!(
			rx.try_recv().ok().unwrap(),
			Message::Connect { set_id: SetId::from(0), peer_id: regular1 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular1).unwrap(), Direction::Outbound,));

		// Connect `regular2` as inbound.
		controller.on_incoming_connection(regular2, IncomingIndex(0));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(0)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular2).unwrap(), Direction::Inbound,));

		// Incoming request for `regular1`.
		controller.on_incoming_connection(regular1, IncomingIndex(1));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Reject(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(!controller.nodes.contains_key(&regular1));

		// Incoming request for `regular2`.
		controller.on_incoming_connection(regular2, IncomingIndex(2));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Reject(IncomingIndex(2)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(!controller.nodes.contains_key(&regular2));
	}

	#[test]
	fn incoming_request_for_connected_node_is_rejected_if_no_slots_available() {
		let regular1 = PeerId::random();
		let regular2 = PeerId::random();
		let outgoing_candidates = vec![regular1];

		let config = SetConfig {
			in_peers: 1,
			out_peers: 1,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);
		peer_store.expect_outgoing_candidates().once().return_const(outgoing_candidates);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert_eq!(controller.num_out, 0);
		assert_eq!(controller.num_in, 0);

		// Connect `regular1` as outbound.
		controller.alloc_slots();
		assert_eq!(
			rx.try_recv().ok().unwrap(),
			Message::Connect { set_id: SetId::from(0), peer_id: regular1 }
		);
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular1).unwrap(), Direction::Outbound,));

		// Connect `regular2` as inbound.
		controller.on_incoming_connection(regular2, IncomingIndex(0));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Accept(IncomingIndex(0)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(matches!(controller.nodes.get(&regular2).unwrap(), Direction::Inbound,));

		controller.max_in = 0;

		// Incoming request for `regular1`.
		controller.on_incoming_connection(regular1, IncomingIndex(1));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Reject(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(!controller.nodes.contains_key(&regular1));

		// Incoming request for `regular2`.
		controller.on_incoming_connection(regular2, IncomingIndex(2));
		assert_eq!(rx.try_recv().ok().unwrap(), Message::Reject(IncomingIndex(2)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
		assert!(!controller.nodes.contains_key(&regular2));
	}

	#[test]
	fn incoming_peers_that_exceed_slots_are_rejected() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();

		let config = SetConfig {
			in_peers: 1,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(false);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Connect `peer1` as inbound.
		controller.on_incoming_connection(peer1, IncomingIndex(1));
		assert_eq!(rx.try_recv().unwrap(), Message::Accept(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);

		// Incoming requests for `peer2`.
		controller.on_incoming_connection(peer2, IncomingIndex(2));
		assert_eq!(rx.try_recv().unwrap(), Message::Reject(IncomingIndex(2)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
	}

	#[test]
	fn banned_regular_incoming_node_is_rejected() {
		let peer1 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(true);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));

		// Incoming request.
		controller.on_incoming_connection(peer1, IncomingIndex(1));
		assert_eq!(rx.try_recv().unwrap(), Message::Reject(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
	}

	#[test]
	fn banned_reserved_incoming_node_is_rejected() {
		let reserved1 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: std::iter::once(reserved1).collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(true);

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert!(controller.reserved_nodes.contains_key(&reserved1));

		// Incoming request.
		controller.on_incoming_connection(reserved1, IncomingIndex(1));
		assert_eq!(rx.try_recv().unwrap(), Message::Reject(IncomingIndex(1)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
	}

	#[test]
	fn we_dont_connect_to_banned_reserved_node() {
		let reserved1 = PeerId::random();

		let config = SetConfig {
			in_peers: 10,
			out_peers: 10,
			bootnodes: Vec::new(),
			reserved_nodes: std::iter::once(reserved1).collect(),
			reserved_only: false,
		};
		let (tx, mut rx) = tracing_unbounded("mpsc_test_to_notifications", 100);

		let mut peer_store = MockPeerStoreHandle::new();
		peer_store.expect_register_protocol().once().return_const(());
		peer_store.expect_is_banned().once().return_const(true);
		peer_store.expect_outgoing_candidates().once().return_const(Vec::new());

		let (_handle, mut controller) =
			ProtocolController::new(SetId::from(0), config, tx, Box::new(peer_store));
		assert!(matches!(controller.reserved_nodes.get(&reserved1), Some(PeerState::NotConnected)));

		// Initiate connectios
		controller.alloc_slots();
		assert!(matches!(controller.reserved_nodes.get(&reserved1), Some(PeerState::NotConnected)));
		assert_eq!(rx.try_recv().unwrap_err(), TryRecvError::Empty);
	}
}
