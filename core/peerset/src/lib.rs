// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Peer Set Manager (PSM). Contains the strategy for choosing which nodes the network should be
//! connected to.

mod slots;

use std::collections::{HashMap, VecDeque};
use std::ops;
use futures::{prelude::*, sync::mpsc};
use libp2p::PeerId;
use slots::{SlotType, SlotError, Slots};
pub use serde_json::Value;

#[derive(Debug)]
struct PeersetData {
	/// List of nodes that we know exist but we are not connected to.
	/// Elements in this list must never be in `out_slots` or `in_slots`.
	discovered: VecDeque<(PeerId, SlotType)>,
	/// If true, we only accept reserved nodes.
	reserved_only: bool,
	/// Node slots for outgoing connections.
	out_slots: Slots,
	/// Node slots for incoming connections.
	in_slots: Slots,
	/// List of node scores.
	scores: HashMap<PeerId, i32>,
}

#[derive(Debug)]
enum Action {
	AddReservedPeer(PeerId),
	RemoveReservedPeer(PeerId),
	SetReservedOnly(bool),
	ReportPeer(PeerId, i32),
	Incoming(PeerId, IncomingIndex),
	Dropped(PeerId),
	Discovered(PeerId),
}

/// Shared handle to the peer set manager (PSM). Distributed around the code.
#[derive(Debug, Clone)]
pub struct PeersetHandle {
	tx: mpsc::UnboundedSender<Action>,
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

	/// Reports an adjustement to the reputation of the given peer.
	pub fn report_peer(&self, peer_id: PeerId, score_diff: i32) {
		let _ = self.tx.unbounded_send(Action::ReportPeer(peer_id, score_diff));
	}

	/// Indicate that we received an incoming connection. Must be answered either with
	/// a corresponding `Accept` or `Reject`, except if we were already connected to this peer.
	///
	/// Note that this mechanism is orthogonal to `Connect`/`Drop`. Accepting an incoming
	/// connection implicitely means `Accept`, but incoming connections aren't cancelled by
	/// `dropped`.
	///
	/// Because of concurrency issues, it is acceptable to call `incoming` with a `PeerId` the
	/// peerset is already connected to, in which case it must not answer.
	pub fn incoming(&self, peer_id: PeerId, index: IncomingIndex) {
		let _ = self.tx.unbounded_send(Action::Incoming(peer_id, index));
	}

	/// Indicate that we dropped an active connection with a peer, or that we failed to connect.
	///
	/// Must only be called after the PSM has either generated a `Connect` message with this
	/// `PeerId`, or accepted an incoming connection with this `PeerId`.
	pub fn dropped(&self, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::Dropped(peer_id));
	}

	/// Adds a discovered peer id to the PSM.
	///
	/// > **Note**: There is no equivalent "expired" message, meaning that it is the responsibility
	/// >			of the PSM to remove `PeerId`s that fail to dial too often.
	pub fn discovered(&self, peer_id: PeerId) {
		let _ = self.tx.unbounded_send(Action::Discovered(peer_id));
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
	pub in_peers: usize,

	/// Maximum number of outgoing links to peers.
	pub out_peers: usize,

	/// List of bootstrap nodes to initialize the peer with.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// >			otherwise it will not be able to connect to them.
	pub bootnodes: Vec<PeerId>,

	/// If true, we only accept reserved nodes.
	pub reserved_only: bool,

	/// List of nodes that we should always be connected to.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for these nodes,
	/// >			otherwise it will not be able to connect to them.
	pub reserved_nodes: Vec<PeerId>,
}

/// Side of the peer set manager owned by the network. In other words, the "receiving" side.
///
/// Implements the `Stream` trait and can be polled for messages. The `Stream` never ends and never
/// errors.
#[derive(Debug)]
pub struct Peerset {
	data: PeersetData,
	handle: PeersetHandle,
	rx: mpsc::UnboundedReceiver<Action>,
	message_queue: VecDeque<Message>,
}

impl ops::Deref for Peerset {
	type Target = PeersetHandle;

	fn deref(&self) -> &Self::Target {
		&self.handle
	}
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> Peerset {
		let (tx, rx) = mpsc::unbounded();

		let data = PeersetData {
			discovered: Default::default(),
			reserved_only: config.reserved_only,
			out_slots: Slots::new(config.out_peers),
			in_slots: Slots::new(config.in_peers),
			scores: Default::default(),
		};

		let mut peerset = Peerset {
			data,
			handle: PeersetHandle {
				tx,
			},
			rx,
			message_queue: VecDeque::new(),
		};

		for peer_id in config.reserved_nodes {
			peerset.data.discovered.push_back((peer_id, SlotType::Reserved));
		}

		for peer_id in config.bootnodes {
			peerset.data.discovered.push_back((peer_id, SlotType::Common));
		}

		peerset.alloc_slots();
		peerset
	}

	/// Creates shared handle to the peer set manager (PSM).
	pub fn handle(&self) -> PeersetHandle {
		self.handle.clone()
	}

	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		// Nothing more to do if we're already connected.
		if self.data.in_slots.contains(&peer_id) {
			self.data.in_slots.mark_reserved(&peer_id);
			return;
		}

		match self.data.out_slots.add_peer(peer_id.clone(), SlotType::Reserved) {
			Ok(_) => {
				self.message_queue.push_back(Message::Connect(peer_id));
			},
			Err(SlotError::AlreadyConnected(_)) => {
				return;
			}
			Err(SlotError::MaxConnections(_)) => {
				if self.data.discovered.iter().all(|(p, _)| *p != peer_id) {
					self.data.discovered.push_front((peer_id, SlotType::Reserved));
				}
			}
			Err(SlotError::DemandReroute { disconnect, ..}) => {
				self.message_queue.push_back(Message::Drop(disconnect));
				if self.data.discovered.iter().all(|(p, _)| *p != peer_id) {
					self.data.discovered.push_front((peer_id, SlotType::Reserved));
				}
			}
		}
	}

	fn on_remove_reserved_peer(&mut self, peer_id: &PeerId) {
		self.data.in_slots.mark_not_reserved(peer_id);
		self.data.out_slots.mark_not_reserved(peer_id);
		// TODO: should we disconnect from this peer?
		// a) always?
		// b) only if reserved_only is set
	}

	fn on_set_reserved_only(&mut self, reserved_only: bool) {
		// Disconnect non-reserved nodes.
		self.data.reserved_only = reserved_only;
		if self.data.reserved_only {
			for peer in self.data.in_slots.common_peers().chain(self.data.out_slots.common_peers()) {
				// peer will be removed from `in_slots` or `out_slots` in `on_dropped` method
				self.message_queue.push_back(Message::Drop(peer.clone()))
			}
		}
	}

	fn on_report_peer(&mut self, peer_id: PeerId, score_diff: i32) {
		let score = self.data.scores.entry(peer_id.clone()).or_default();
		*score = score.saturating_add(score_diff);

		if *score < 0 {
			// peer will be removed from `in_slots` or `out_slots` in `on_dropped` method
			self.message_queue.push_back(Message::Drop(peer_id));
		}
	}

	fn alloc_slots(&mut self) {
		while let Some((peer_id, slot_type)) = self.data.discovered.pop_front() {
			// reserved peers are always at the beginning of discovered vec
			// if we get a common peer, that means it's a goot time to stop
			if self.data.reserved_only && slot_type == SlotType::Common {
				self.data.discovered.push_front((peer_id, slot_type));
				break;
			}
			match self.data.out_slots.add_peer(peer_id.clone(), slot_type) {
				Ok(_) => {
					self.message_queue.push_back(Message::Connect(peer_id));
				},
				Err(SlotError::AlreadyConnected(_)) => (),
				Err(SlotError::MaxConnections(_)) => {
					self.data.discovered.push_front((peer_id, slot_type));
					break;
				},
				Err(SlotError::DemandReroute { disconnect, .. }) => {
					self.message_queue.push_back(Message::Drop(disconnect));
					self.data.discovered.push_front((peer_id, slot_type));
					break;
				}
			}
		}
	}

	fn on_incoming(&mut self, peer_id: PeerId, index: IncomingIndex) {
		// check if we are already connected to this peer
		if self.data.out_slots.contains(&peer_id) {
			self.message_queue.push_back(Message::Reject(index));
		}

		match self.data.in_slots.add_peer(peer_id, SlotType::Common) {
			Ok(_) => {
				self.message_queue.push_back(Message::Accept(index));
			},
			Err(SlotError::MaxConnections(peer_id)) => {
				if self.data.discovered.iter().all(|(p, _)| *p != peer_id) {
					self.data.discovered.push_back((peer_id, SlotType::Common));
				}
				self.message_queue.push_back(Message::Reject(index));
			},
			_ => {
				self.message_queue.push_back(Message::Reject(index));
			}
		}
	}

	fn on_dropped(&mut self, peer_id: PeerId) {
		// Automatically connect back if reserved.
		if self.data.in_slots.is_reserved(&peer_id) || self.data.out_slots.is_reserved(&peer_id) {
			self.message_queue.push_back(Message::Connect(peer_id));
			return;
		}

		// Otherwise, free the slot.
		self.data.in_slots.clear_slot(&peer_id);
		self.data.out_slots.clear_slot(&peer_id);

		// Note: in this dummy implementation we consider that peers never expire. As soon as we
		// are disconnected from a peer, we try again.
		if self.data.discovered.iter().all(|(p, _)| p != &peer_id) {
			self.data.discovered.push_back((peer_id, SlotType::Common));
		}

		self.alloc_slots();
	}

	fn on_discovered(&mut self, peer_id: PeerId) {
		if self.data.in_slots.contains(&peer_id) || self.data.out_slots.contains(&peer_id) {
			return;
		}

		if self.data.discovered.iter().all(|(p, _)| *p != peer_id) {
			self.data.discovered.push_back((peer_id, SlotType::Common));
		}
		self.alloc_slots();
	}

	/// Produces a JSON object containing the state of the peerset manager, for debugging purposes.
	pub fn debug_info(&self) -> serde_json::Value {
		serde_json::Value::Null
	}
}

impl Stream for Peerset {
	type Item = Message;
	type Error = ();

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		loop {
			if let Some(message) = self.message_queue.pop_front() {
				return Ok(Async::Ready(Some(message)));
			}
			match self.rx.poll()? {
				Async::NotReady => return Ok(Async::NotReady),
				Async::Ready(None) => return Ok(Async::Ready(None)),
				Async::Ready(Some(action)) => match action {
					Action::AddReservedPeer(peer_id) => self.on_add_reserved_peer(peer_id),
					Action::RemoveReservedPeer(peer_id) => self.on_remove_reserved_peer(&peer_id),
					Action::SetReservedOnly(reserved) => self.on_set_reserved_only(reserved),
					Action::ReportPeer(peer_id, score_diff) => self.on_report_peer(peer_id, score_diff),
					Action::Incoming(peer_id, index) => self.on_incoming(peer_id, index),
					Action::Dropped(peer_id) => self.on_dropped(peer_id),
					Action::Discovered(peer_id) => self.on_discovered(peer_id),
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use libp2p::PeerId;
	use futures::prelude::*;
	use super::{PeersetConfig, Peerset, Message};

	fn assert_messages(mut peerset: Peerset, messages: Vec<Message>) {
		for expected_message in messages {
			let (message, p) = next_message(peerset).expect("expected message");
			assert_eq!(message, expected_message);
			peerset = p;
		}
		assert!(peerset.message_queue.is_empty())
	}

	fn next_message(peerset: Peerset) -> Result<(Message, Peerset), ()> {
		let (next, peerset) = peerset.into_future()
			.wait()
			.map_err(|_| ())?;
		let message = next.ok_or_else(|| ())?;
		Ok((message, peerset))
	}

	#[test]
	fn test_peerset_from_config_with_bootnodes() {
		let bootnode = PeerId::random();
		let bootnode2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 2,
			bootnodes: vec![bootnode.clone(), bootnode2.clone()],
			reserved_only: false,
			reserved_nodes: Vec::new(),
		};

		let peerset = Peerset::from_config(config);

		assert_messages(peerset, vec![
			Message::Connect(bootnode),
			Message::Connect(bootnode2),
		]);
	}

	#[test]
	fn test_peerset_from_config_with_reserved_nodes() {
		let bootnode = PeerId::random();
		let bootnode2 = PeerId::random();
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 3,
			bootnodes: vec![bootnode.clone(), bootnode2.clone()],
			reserved_only: false,
			reserved_nodes: vec![reserved_peer.clone(), reserved_peer2.clone()],
		};

		let peerset = Peerset::from_config(config);

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(reserved_peer2),
			Message::Connect(bootnode)
		]);
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
			reserved_nodes: Vec::new(),
		};

		let peerset = Peerset::from_config(config);
		peerset.add_reserved_peer(reserved_peer.clone());
		peerset.add_reserved_peer(reserved_peer2.clone());

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(reserved_peer2)
		]);
	}

	#[test]
	fn test_peerset_remove_reserved_peer() {
		//unimplemented!();
	}

	#[test]
	fn test_peerset_set_reserved_only() {
		let bootnode = PeerId::random();
		let bootnode2 = PeerId::random();
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 4,
			bootnodes: vec![bootnode.clone(), bootnode2.clone()],
			reserved_only: false,
			reserved_nodes: vec![reserved_peer.clone(), reserved_peer2.clone()],
		};

		let peerset = Peerset::from_config(config);
		peerset.set_reserved_only(true);

		let (message, peerset) = next_message(peerset).expect("Message::Connect to reserved_peer");
		assert_eq!(message, Message::Connect(reserved_peer));
		let (message, peerset) = next_message(peerset).expect("Message::Connect to reserved_peer2");
		assert_eq!(message, Message::Connect(reserved_peer2));
		let (message, peerset) = next_message(peerset).expect("Message::Connect to bootnode");
		assert_eq!(message, Message::Connect(bootnode.clone()));
		let (message, peerset) = next_message(peerset).expect("Message::Connect to bootnode2");
		assert_eq!(message, Message::Connect(bootnode2.clone()));

		let (message, peerset) = next_message(peerset).expect("Message::Drop the bootnode");
		let (message2, _peerset) = next_message(peerset).expect("Message::Drop the bootnode2");
		assert!(
			(message == Message::Drop(bootnode.clone()) && message2 == Message::Drop(bootnode2.clone())) ||
			(message2 == Message::Drop(bootnode) && message == Message::Drop(bootnode2))
		);
	}

	#[test]
	fn test_peerset_report_peer() {
		//unimplemented!();
	}

	#[test]
	fn test_peerset_incoming() {
		//unimplemented!();
	}

	#[test]
	fn test_peerset_dropped() {
		let bootnode = PeerId::random();
		let bootnode2 = PeerId::random();
		let reserved_peer = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 2,
			bootnodes: vec![bootnode.clone(), bootnode2.clone()],
			reserved_only: false,
			reserved_nodes: vec![reserved_peer.clone()],
		};

		let peerset = Peerset::from_config(config);
		peerset.dropped(reserved_peer.clone());
		peerset.dropped(bootnode.clone());

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer.clone()),
			Message::Connect(bootnode),
			Message::Connect(reserved_peer),
			Message::Connect(bootnode2),
		]);
	}

	#[test]
	fn test_peerset_discovered() {
		//unimplemented!();
	}
}
