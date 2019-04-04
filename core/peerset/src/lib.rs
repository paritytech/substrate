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

use std::collections::VecDeque;
use futures::{prelude::*, sync::mpsc, try_ready};
use libp2p::PeerId;
use linked_hash_map::LinkedHashMap;
use log::trace;
use lru_cache::LruCache;
use slots::{SlotType, SlotState, Slots};
pub use serde_json::Value;

const PEERSET_SCORES_CACHE_SIZE: usize = 1000;

/// FIFO-ordered list of nodes that we know exist, but we are not connected to.
#[derive(Debug, Default)]
struct Discovered {
	/// Nodes we should connect to first.
	reserved: LinkedHashMap<PeerId, ()>,
	/// All remaining nodes.
	common: LinkedHashMap<PeerId, ()>,
}

impl Discovered {
	/// Returns true if we already know given node.
	fn contains(&self, peer_id: &PeerId) -> bool {
		self.reserved.contains_key(peer_id) || self.common.contains_key(peer_id)
	}

	/// Returns true if given node is reserved.
	fn is_reserved(&self, peer_id: &PeerId) -> bool {
		self.reserved.contains_key(peer_id)
	}

	/// Adds new peer of a given type.
	fn add_peer(&mut self, peer_id: PeerId, slot_type: SlotType) {
		if !self.contains(&peer_id) {
			match slot_type {
				SlotType::Common => self.common.insert(peer_id, ()),
				SlotType::Reserved => self.reserved.insert(peer_id, ()),
			};
		}
	}

	/// Pops the oldest peer from the list.
	fn pop_peer(&mut self, reserved_only: bool) -> Option<(PeerId, SlotType)> {
		if let Some((peer_id, _)) = self.reserved.pop_front() {
			return Some((peer_id, SlotType::Reserved));
		}

		if reserved_only {
			return None;
		}

		self.common.pop_front()
			.map(|(peer_id, _)| (peer_id, SlotType::Common))
	}

	/// Marks the node as not reserved.
	fn mark_not_reserved(&mut self, peer_id: &PeerId) {
		if let Some(_) = self.reserved.remove(peer_id) {
			self.common.insert(peer_id.clone(), ());
		}
	}

	/// Removes the node from the list.
	fn remove_peer(&mut self, peer_id: &PeerId) {
		self.reserved.remove(peer_id);
		self.common.remove(peer_id);
	}
}

#[derive(Debug)]
struct PeersetData {
	/// List of nodes that we know exist, but we are not connected to.
	/// Elements in this list must never be in `out_slots` or `in_slots`.
	discovered: Discovered,
	/// If true, we only accept reserved nodes.
	reserved_only: bool,
	/// Node slots for outgoing connections.
	out_slots: Slots,
	/// Node slots for incoming connections.
	in_slots: Slots,
	/// List of node scores.
	scores: LruCache<PeerId, i32>,
}

#[derive(Debug)]
enum Action {
	AddReservedPeer(PeerId),
	RemoveReservedPeer(PeerId),
	SetReservedOnly(bool),
	ReportPeer(PeerId, i32),
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

	/// Reports an adjustment to the reputation of the given peer.
	pub fn report_peer(&self, peer_id: PeerId, score_diff: i32) {
		let _ = self.tx.unbounded_send(Action::ReportPeer(peer_id, score_diff));
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
	pub in_peers: u32,

	/// Maximum number of outgoing links to peers.
	pub out_peers: u32,

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
	rx: mpsc::UnboundedReceiver<Action>,
	message_queue: VecDeque<Message>,
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> (Peerset, PeersetHandle) {
		let (tx, rx) = mpsc::unbounded();

		let data = PeersetData {
			discovered: Default::default(),
			reserved_only: config.reserved_only,
			out_slots: Slots::new(config.out_peers),
			in_slots: Slots::new(config.in_peers),
			scores: LruCache::new(PEERSET_SCORES_CACHE_SIZE),
		};

		let handle = PeersetHandle {
			tx,
		};

		let mut peerset = Peerset {
			data,
			rx,
			message_queue: VecDeque::new(),
		};

		for peer_id in config.reserved_nodes {
			peerset.data.discovered.add_peer(peer_id, SlotType::Reserved);
		}

		for peer_id in config.bootnodes {
			peerset.data.discovered.add_peer(peer_id, SlotType::Common);
		}

		peerset.alloc_slots();
		(peerset, handle)
	}

	fn on_add_reserved_peer(&mut self, peer_id: PeerId) {
		// Nothing more to do if we're already connected.
		if self.data.in_slots.contains(&peer_id) {
			self.data.in_slots.mark_reserved(&peer_id);
			return;
		}

		match self.data.out_slots.add_peer(peer_id, SlotType::Reserved) {
			SlotState::Added(peer_id) => {
				// reserved node may have been previously stored as normal node in discovered list
				self.data.discovered.remove_peer(&peer_id);

				// notify that connection has been made
				self.message_queue.push_back(Message::Connect(peer_id));
				return;
			},
			SlotState::Swaped { removed, added } => {
				// reserved node may have been previously stored as normal node in discovered list
				self.data.discovered.remove_peer(&added);
				// let's add the peer we disconnected from to the discovered list again
				self.data.discovered.add_peer(removed.clone(), SlotType::Common);
				// swap connections
				self.message_queue.push_back(Message::Drop(removed));
				self.message_queue.push_back(Message::Connect(added));
			}
			SlotState::AlreadyConnected(_) | SlotState::Upgraded(_) => {
				return;
			}
			SlotState::MaxConnections(peer_id) => {
				self.data.discovered.add_peer(peer_id, SlotType::Reserved);
				return;
			}
		}
	}

	fn on_remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.data.in_slots.mark_not_reserved(&peer_id);
		self.data.out_slots.mark_not_reserved(&peer_id);
		self.data.discovered.mark_not_reserved(&peer_id);
		if self.data.reserved_only {
			if self.data.in_slots.clear_slot(&peer_id) || self.data.out_slots.clear_slot(&peer_id) {
				// insert peer back into discovered list
				self.data.discovered.add_peer(peer_id.clone(), SlotType::Common);
				self.message_queue.push_back(Message::Drop(peer_id));
				// call alloc_slots again, cause we may have some reserved peers in discovered list
				// waiting for the slot that was just cleared
				self.alloc_slots();
			}
		}
	}

	fn on_set_reserved_only(&mut self, reserved_only: bool) {
		// Disconnect non-reserved nodes.
		self.data.reserved_only = reserved_only;
		if self.data.reserved_only {
			for peer_id in self.data.in_slots.clear_common_slots().into_iter().chain(self.data.out_slots.clear_common_slots().into_iter()) {
				// insert peer back into discovered list
				self.data.discovered.add_peer(peer_id.clone(), SlotType::Common);
				self.message_queue.push_back(Message::Drop(peer_id));
			}
		} else {
			self.alloc_slots();
		}
	}

	fn on_report_peer(&mut self, peer_id: PeerId, score_diff: i32) {
		let score = match self.data.scores.get_mut(&peer_id) {
			Some(score) => {
				*score = score.saturating_add(score_diff);
				*score
			},
			None => {
				self.data.scores.insert(peer_id.clone(), score_diff);
				score_diff
			}
		};

		if score < 0 {
			// peer will be removed from `in_slots` or `out_slots` in `on_dropped` method
			if self.data.in_slots.contains(&peer_id) || self.data.out_slots.contains(&peer_id) {
				self.data.in_slots.clear_slot(&peer_id);
				self.data.out_slots.clear_slot(&peer_id);
				self.message_queue.push_back(Message::Drop(peer_id));
			}
		}
	}

	fn alloc_slots(&mut self) {
		while let Some((peer_id, slot_type)) = self.data.discovered.pop_peer(self.data.reserved_only) {
			match self.data.out_slots.add_peer(peer_id, slot_type) {
				SlotState::Added(peer_id) => {
					self.message_queue.push_back(Message::Connect(peer_id));
				},
				SlotState::Swaped { removed, added } => {
					// insert peer back into discovered list
					self.data.discovered.add_peer(removed.clone(), SlotType::Common);
					self.message_queue.push_back(Message::Drop(removed));
					self.message_queue.push_back(Message::Connect(added));
				}
				SlotState::Upgraded(_) | SlotState::AlreadyConnected(_) => {
					// TODO: we should never reach this point
				},
				SlotState::MaxConnections(peer_id) => {
					self.data.discovered.add_peer(peer_id, slot_type);
					break;
				},
			}
		}
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
	pub fn incoming(&mut self, peer_id: PeerId, index: IncomingIndex) {
		trace!(
			target: "peerset",
			"Incoming {:?}\nin_slots={:?}\nout_slots={:?}",
			peer_id, self.data.in_slots, self.data.out_slots
		);
		// if `reserved_only` is set, but this peer is not a part of our discovered list,
		// a) it is not reserved, so we reject the connection
		// b) we are already connected to it, so we reject the connection
		if self.data.reserved_only && !self.data.discovered.is_reserved(&peer_id) {
			self.message_queue.push_back(Message::Reject(index));
			return;
		}

		// check if we are already connected to this peer
		if self.data.out_slots.contains(&peer_id) {
			// we are already connected. in this case we do not answer
			return;
		}

		let slot_type = if self.data.reserved_only {
			SlotType::Reserved
		} else {
			SlotType::Common
		};

		match self.data.in_slots.add_peer(peer_id, slot_type) {
			SlotState::Added(peer_id) => {
				// reserved node may have been previously stored as normal node in discovered list
				self.data.discovered.remove_peer(&peer_id);
				self.message_queue.push_back(Message::Accept(index));
				return;
			},
			SlotState::Swaped { removed, added } => {
				// reserved node may have been previously stored as normal node in discovered list
				self.data.discovered.remove_peer(&added);
				// swap connections.
				self.message_queue.push_back(Message::Drop(removed));
				self.message_queue.push_back(Message::Accept(index));
			},
			SlotState::AlreadyConnected(_) | SlotState::Upgraded(_) => {
				// we are already connected. in this case we do not answer
				return;
			},
			SlotState::MaxConnections(peer_id) => {
				self.data.discovered.add_peer(peer_id, slot_type);
				self.message_queue.push_back(Message::Reject(index));
				return;
			},
		}
	}

	/// Indicate that we dropped an active connection with a peer, or that we failed to connect.
	///
	/// Must only be called after the PSM has either generated a `Connect` message with this
	/// `PeerId`, or accepted an incoming connection with this `PeerId`.
	pub fn dropped(&mut self, peer_id: PeerId) {
		trace!(
			target: "peerset",
			"Dropping {:?}\nin_slots={:?}\nout_slots={:?}",
			peer_id, self.data.in_slots, self.data.out_slots
		);
		// Automatically connect back if reserved.
		if self.data.in_slots.is_connected_and_reserved(&peer_id) || self.data.out_slots.is_connected_and_reserved(&peer_id) {
			self.message_queue.push_back(Message::Connect(peer_id));
			return;
		}

		// Otherwise, free the slot.
		self.data.in_slots.clear_slot(&peer_id);
		self.data.out_slots.clear_slot(&peer_id);

		// Note: in this dummy implementation we consider that peers never expire. As soon as we
		// are disconnected from a peer, we try again.
		self.data.discovered.add_peer(peer_id, SlotType::Common);
		self.alloc_slots();
	}

	/// Adds discovered peer ids to the PSM.
	///
	/// > **Note**: There is no equivalent "expired" message, meaning that it is the responsibility
	/// >			of the PSM to remove `PeerId`s that fail to dial too often.
	pub fn discovered<I: IntoIterator<Item = PeerId>>(&mut self, peer_ids: I) {
		for peer_id in peer_ids {
			if !self.data.in_slots.contains(&peer_id) && !self.data.out_slots.contains(&peer_id) && !self.data.discovered.contains(&peer_id) {
				trace!(target: "peerset", "Discovered new peer: {:?}", peer_id);
				self.data.discovered.add_peer(peer_id, SlotType::Common);
			} else {
				trace!(target: "peerset", "Discovered known peer: {:?}", peer_id);
			}
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
			match try_ready!(self.rx.poll()) {
				None => return Ok(Async::Ready(None)),
				Some(action) => match action {
					Action::AddReservedPeer(peer_id) => self.on_add_reserved_peer(peer_id),
					Action::RemoveReservedPeer(peer_id) => self.on_remove_reserved_peer(peer_id),
					Action::SetReservedOnly(reserved) => self.on_set_reserved_only(reserved),
					Action::ReportPeer(peer_id, score_diff) => self.on_report_peer(peer_id, score_diff),
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use libp2p::PeerId;
	use futures::prelude::*;
	use super::{PeersetConfig, Peerset, Message, IncomingIndex};

	fn assert_messages(mut peerset: Peerset, messages: Vec<Message>) -> Peerset {
		for expected_message in messages {
			let (message, p) = next_message(peerset).expect("expected message");
			assert_eq!(message, expected_message);
			peerset = p;
		}
		assert!(peerset.message_queue.is_empty());
		peerset
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

		let (peerset, _handle) = Peerset::from_config(config);

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

		let (peerset, _handle) = Peerset::from_config(config);

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

		let (peerset, handle) = Peerset::from_config(config);
		handle.add_reserved_peer(reserved_peer.clone());
		handle.add_reserved_peer(reserved_peer2.clone());

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(reserved_peer2)
		]);
	}

	#[test]
	fn test_peerset_remove_reserved_peer() {
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 2,
			bootnodes: vec![],
			reserved_only: false,
			reserved_nodes: vec![reserved_peer.clone(), reserved_peer2.clone()],
		};

		let (peerset, handle) = Peerset::from_config(config);
		handle.remove_reserved_peer(reserved_peer.clone());

		let peerset = assert_messages(peerset, vec![
			Message::Connect(reserved_peer.clone()),
			Message::Connect(reserved_peer2.clone()),
		]);

		handle.set_reserved_only(true);
		handle.remove_reserved_peer(reserved_peer2.clone());

		assert_messages(peerset, vec![
			Message::Drop(reserved_peer),
			Message::Drop(reserved_peer2),
		]);
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

		let (peerset, handle) = Peerset::from_config(config);
		handle.set_reserved_only(true);
		handle.set_reserved_only(false);

		assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(reserved_peer2),
			Message::Connect(bootnode.clone()),
			Message::Connect(bootnode2.clone()),
			Message::Drop(bootnode.clone()),
			Message::Drop(bootnode2.clone()),
			Message::Connect(bootnode),
			Message::Connect(bootnode2),
		]);
	}

	#[test]
	fn test_peerset_report_peer() {
		let bootnode = PeerId::random();
		let bootnode2 = PeerId::random();
		let config = PeersetConfig {
			in_peers: 0,
			out_peers: 1,
			bootnodes: vec![bootnode.clone(), bootnode2.clone()],
			reserved_only: false,
			reserved_nodes: Vec::new(),
		};

		let (peerset, handle) = Peerset::from_config(config);
		handle.report_peer(bootnode2, -1);
		handle.report_peer(bootnode.clone(), -1);

		assert_messages(peerset, vec![
			Message::Connect(bootnode.clone()),
			Message::Drop(bootnode)
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
			reserved_nodes: Vec::new(),
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

		let (peerset, _handle) = Peerset::from_config(config);

		let mut peerset = assert_messages(peerset, vec![
			Message::Connect(reserved_peer.clone()),
			Message::Connect(bootnode.clone()),
		]);

		peerset.dropped(reserved_peer.clone());
		peerset.dropped(bootnode);

		let _peerset = assert_messages(peerset, vec![
			Message::Connect(reserved_peer),
			Message::Connect(bootnode2),
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
			reserved_nodes: vec![],
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
}
