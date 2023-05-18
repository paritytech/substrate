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

//! Peer Set Manager (PSM). Contains the strategy for choosing which nodes the network should be
//! connected to.
//!
//! The PSM handles *sets* of nodes. A set of nodes is defined as the nodes that are believed to
//! support a certain capability, such as handling blocks and transactions of a specific chain,
//! or collating a certain parachain.
//!
//! For each node in each set, the peerset holds a flag specifying whether the node is
//! connected to us or not.
//!
//! This connected/disconnected status is specific to the node and set combination, and it is for
//! example possible for a node to be connected through a specific set but not another.
//!
//! In addition, for each, set, the peerset also holds a list of reserved nodes towards which it
//! will at all time try to maintain a connection with.

mod peer_store;
mod protocol_controller;

use peer_store::{PeerStore, PeerStoreHandle, PeerStoreProvider};
use protocol_controller::{ProtocolController, ProtocolHandle};

use futures::{
	channel::oneshot,
	future::{join_all, BoxFuture, JoinAll},
	prelude::*,
	stream::Stream,
};
use log::debug;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use serde_json::json;
use std::{
	collections::HashSet,
	pin::Pin,
	task::{Context, Poll},
};

pub use libp2p_identity::PeerId;

pub use peer_store::BANNED_THRESHOLD;

pub const LOG_TARGET: &str = "peerset";

#[derive(Debug)]
enum Action {
	AddReservedPeer(SetId, PeerId),
	RemoveReservedPeer(SetId, PeerId),
	SetReservedPeers(SetId, HashSet<PeerId>),
	SetReservedOnly(SetId, bool),
	ReportPeer(PeerId, ReputationChange),
	AddKnownPeer(PeerId),
	PeerReputation(PeerId, oneshot::Sender<i32>),
}

/// Identifier of a set in the peerset.
///
/// Can be constructed using the `From<usize>` trait implementation based on the index of the set
/// within [`PeersetConfig::sets`]. For example, the first element of [`PeersetConfig::sets`] is
/// later referred to with `SetId::from(0)`. It is intended that the code responsible for building
/// the [`PeersetConfig`] is also responsible for constructing the [`SetId`]s.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SetId(usize);

impl SetId {
	pub const fn from(id: usize) -> Self {
		Self(id)
	}
}

impl From<usize> for SetId {
	fn from(id: usize) -> Self {
		Self(id)
	}
}

impl From<SetId> for usize {
	fn from(id: SetId) -> Self {
		id.0
	}
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
		Self { value, reason }
	}

	/// New reputation change that forces minimum possible reputation.
	pub const fn new_fatal(reason: &'static str) -> ReputationChange {
		Self { value: i32::MIN, reason }
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
	/// > otherwise it will not be able to connect to it.
	pub fn add_reserved_peer(&self, set_id: SetId, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::AddReservedPeer(set_id, peer_id));
	}

	/// Remove a previously-added reserved peer.
	///
	/// Has no effect if the node was not a reserved peer.
	pub fn remove_reserved_peer(&self, set_id: SetId, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::RemoveReservedPeer(set_id, peer_id));
	}

	/// Sets whether or not the peerset only has connections with nodes marked as reserved for
	/// the given set.
	pub fn set_reserved_only(&self, set_id: SetId, reserved: bool) {
		let _ = self.tx.unbounded_send(Action::SetReservedOnly(set_id, reserved));
	}

	/// Set reserved peers to the new set.
	pub fn set_reserved_peers(&self, set_id: SetId, peer_ids: HashSet<PeerId>) {
		let _ = self.tx.unbounded_send(Action::SetReservedPeers(set_id, peer_ids));
	}

	/// Reports an adjustment to the reputation of the given peer.
	pub fn report_peer(&self, peer_id: PeerId, score_diff: ReputationChange) {
		let _ = self.tx.unbounded_send(Action::ReportPeer(peer_id, score_diff));
	}

	/// Add a peer to the list of known peers.
	pub fn add_known_peer(&self, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::AddKnownPeer(peer_id));
	}

	/// Returns the reputation value of the peer.
	pub async fn peer_reputation(self, peer_id: PeerId) -> Result<i32, ()> {
		let (tx, rx) = oneshot::channel();

		let _ = self.tx.unbounded_send(Action::PeerReputation(peer_id, tx));

		// The channel can only be closed if the peerset no longer exists.
		rx.await.map_err(|_| ())
	}
}

/// Message that can be sent by the peer set manager (PSM).
#[derive(Debug, PartialEq)]
pub enum Message {
	/// Request to open a connection to the given peer. From the point of view of the PSM, we are
	/// immediately connected.
	Connect {
		/// Set id to connect on.
		set_id: SetId,
		/// Peer to connect to.
		peer_id: PeerId,
	},

	/// Drop the connection to the given peer, or cancel the connection attempt after a `Connect`.
	Drop {
		/// Set id to disconnect on.
		set_id: SetId,
		/// Peer to disconnect from.
		peer_id: PeerId,
	},

	/// Equivalent to `Connect` for the peer corresponding to this incoming index.
	Accept(IncomingIndex),

	/// Equivalent to `Drop` for the peer corresponding to this incoming index.
	Reject(IncomingIndex),
}

/// Opaque identifier for an incoming connection. Allocated by the network.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncomingIndex(pub u64);

impl From<u64> for IncomingIndex {
	fn from(val: u64) -> Self {
		Self(val)
	}
}

/// Configuration to pass when creating the peer set manager.
#[derive(Debug)]
pub struct PeersetConfig {
	/// List of sets of nodes the peerset manages.
	pub sets: Vec<SetConfig>,
}

/// Configuration for a single set of nodes.
#[derive(Debug)]
pub struct SetConfig {
	/// Maximum number of ingoing links to peers.
	pub in_peers: u32,

	/// Maximum number of outgoing links to peers.
	pub out_peers: u32,

	/// List of bootstrap nodes to initialize the set with.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// > otherwise it will not be able to connect to them.
	pub bootnodes: Vec<PeerId>,

	/// Lists of nodes we should always be connected to.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// >			otherwise it will not be able to connect to them.
	pub reserved_nodes: HashSet<PeerId>,

	/// If true, we only accept nodes in [`SetConfig::reserved_nodes`].
	pub reserved_only: bool,
}

/// Side of the peer set manager owned by the network. In other words, the "receiving" side.
///
/// Implements the `Stream` trait and can be polled for messages. The `Stream` never ends and never
/// errors.
pub struct Peerset {
	/// Peer reputation store handle.
	peer_store_handle: PeerStoreHandle,
	/// Peer reputation store.
	peer_store_future: BoxFuture<'static, ()>,
	/// Protocol handles.
	protocol_handles: Vec<ProtocolHandle>,
	/// Protocol controllers responsible for connections, per `SetId`.
	protocol_controller_futures: JoinAll<BoxFuture<'static, ()>>,
	/// Commands sent from protocol controllers to `Notifications`. The size of this vector never
	/// changes.
	from_controllers: TracingUnboundedReceiver<Message>,
	/// Receiver for messages from the `PeersetHandle` and from `to_self`.
	from_handle: TracingUnboundedReceiver<Action>,
	/// Sending side of `from_handle`.
	to_self: TracingUnboundedSender<Action>,
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> (Peerset, PeersetHandle) {
		let default_set_config = &config.sets[0];
		let peer_store = PeerStore::new(default_set_config.bootnodes.clone());

		let (to_notifications, from_controllers) =
			tracing_unbounded("mpsc_protocol_controllers_to_notifications", 10_000);

		let controllers = config
			.sets
			.into_iter()
			.enumerate()
			.map(|(set, set_config)| {
				ProtocolController::new(
					SetId::from(set),
					set_config,
					to_notifications.clone(),
					Box::new(peer_store.handle()),
				)
			})
			.collect::<Vec<_>>();

		let (protocol_handles, protocol_controllers): (Vec<ProtocolHandle>, Vec<_>) =
			controllers.into_iter().unzip();

		let (to_self, from_handle) = tracing_unbounded("mpsc_peerset_messages", 10_000);

		let handle = PeersetHandle { tx: to_self.clone() };

		let protocol_controller_futures =
			join_all(protocol_controllers.into_iter().map(|c| c.run().boxed()));

		let peerset = Peerset {
			peer_store_handle: peer_store.handle(),
			peer_store_future: peer_store.run().boxed(),
			protocol_handles,
			protocol_controller_futures,
			from_controllers,
			from_handle,
			to_self,
		};

		(peerset, handle)
	}

	/// Returns the list of reserved peers.
	pub fn reserved_peers(&self, set_id: SetId, pending_response: oneshot::Sender<Vec<PeerId>>) {
		self.protocol_handles[set_id.0].reserved_peers(pending_response);
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
	pub fn incoming(&mut self, set_id: SetId, peer_id: PeerId, index: IncomingIndex) {
		self.protocol_handles[set_id.0].incoming_connection(peer_id, index);
	}

	/// Indicate that we dropped an active connection with a peer, or that we failed to connect.
	///
	/// Must only be called after the PSM has either generated a `Connect` message with this
	/// `PeerId`, or accepted an incoming connection with this `PeerId`.
	pub fn dropped(&mut self, set_id: SetId, peer_id: PeerId, _reason: DropReason) {
		self.protocol_handles[set_id.0].dropped(peer_id);
	}

	/// Reports an adjustment to the reputation of the given peer.
	pub fn report_peer(&mut self, peer_id: PeerId, score_diff: ReputationChange) {
		// We don't immediately perform the adjustments in order to have state consistency. We
		// don't want the reporting here to take priority over messages sent using the
		// `PeersetHandle`.
		let _ = self.to_self.unbounded_send(Action::ReportPeer(peer_id, score_diff));
	}

	/// Produces a JSON object containing the state of the peerset manager, for debugging purposes.
	pub fn debug_info(&mut self) -> serde_json::Value {
		// TODO: Check what info we can include here.
		//       Issue reference: https://github.com/paritytech/substrate/issues/14160.
		json!("unimplemented")
	}

	/// Returns the number of peers that we have discovered.
	pub fn num_discovered_peers(&self) -> usize {
		self.peer_store_handle.num_known_peers()
	}
}

impl Stream for Peerset {
	type Item = Message;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		if let Poll::Ready(msg) = self.from_controllers.poll_next_unpin(cx) {
			if let Some(msg) = msg {
				return Poll::Ready(Some(msg))
			} else {
				debug!(
					target: LOG_TARGET,
					"All `ProtocolController`s have terminated, terminating `Peerset`."
				);
				return Poll::Ready(None)
			}
		}

		while let Poll::Ready(action) = self.from_handle.poll_next_unpin(cx) {
			if let Some(action) = action {
				match action {
					Action::AddReservedPeer(set_id, peer_id) =>
						self.protocol_handles[set_id.0].add_reserved_peer(peer_id),
					Action::RemoveReservedPeer(set_id, peer_id) =>
						self.protocol_handles[set_id.0].remove_reserved_peer(peer_id),
					Action::SetReservedPeers(set_id, peer_ids) =>
						self.protocol_handles[set_id.0].set_reserved_peers(peer_ids),
					Action::SetReservedOnly(set_id, reserved_only) =>
						self.protocol_handles[set_id.0].set_reserved_only(reserved_only),
					Action::ReportPeer(peer_id, score_diff) =>
						self.peer_store_handle.report_peer(peer_id, score_diff),
					Action::AddKnownPeer(peer_id) => self.peer_store_handle.add_known_peer(peer_id),
					Action::PeerReputation(peer_id, pending_response) => {
						let _ =
							pending_response.send(self.peer_store_handle.peer_reputation(&peer_id));
					},
				}
			} else {
				debug!(target: LOG_TARGET, "`PeersetHandle` was dropped, terminating `Peerset`.");
				return Poll::Ready(None)
			}
		}

		if let Poll::Ready(()) = self.peer_store_future.poll_unpin(cx) {
			debug!(target: LOG_TARGET, "`PeerStore` has terminated, terminating `PeerSet`.");
			return Poll::Ready(None)
		}

		if let Poll::Ready(_) = self.protocol_controller_futures.poll_unpin(cx) {
			debug!(
				target: LOG_TARGET,
				"All `ProtocolHandle`s have terminated, terminating `PeerSet`."
			);
			return Poll::Ready(None)
		}

		Poll::Pending
	}
}

/// Reason for calling [`Peerset::dropped`].
#[derive(Debug)]
pub enum DropReason {
	/// Substream or connection has been closed for an unknown reason.
	Unknown,
	/// Substream or connection has been explicitly refused by the target. In other words, the
	/// peer doesn't actually belong to this set.
	Refused,
}
