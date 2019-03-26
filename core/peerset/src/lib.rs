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

use std::collections::{HashSet, VecDeque};
use futures::{prelude::*, sync::mpsc};
use libp2p::PeerId;

struct PeersetData {
	/// List of nodes that we know exist but we are not connected to.
	/// Elements in this list must never be in `out_slots` or `in_slots`.
	discovered: Vec<PeerId>,
	/// List of reserved nodes.
	reserved: HashSet<PeerId>,
	/// If true, we only accept reserved nodes.
	reserved_only: bool,
	/// Node slots for outgoing connections. Each slot contains either `None` if the node is free,
	/// or `Some` if it is assigned to a peer.
	out_slots: Vec<Option<PeerId>>,
	/// Node slots for incoming connections. Each slot contains either `None` if the node is free,
	/// or `Some` if it is assigned to a peer.
	in_slots: Vec<Option<PeerId>>,
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
#[derive(Clone)]
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
#[derive(Debug)]
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
pub struct Peerset {
	data: PeersetData,
	tx: mpsc::UnboundedSender<Action>,
	rx: mpsc::UnboundedReceiver<Action>,
	message_queue: VecDeque<Message>,
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> Peerset {
		let (tx, rx) = mpsc::unbounded();

		let data = PeersetData {
			discovered: config.bootnodes.into_iter().collect(),
			reserved: Default::default(),
			reserved_only: config.reserved_only,
			out_slots: (0 .. config.out_peers).map(|_| None).collect(),
			in_slots: (0 .. config.in_peers).map(|_| None).collect(),
		};

		let mut peerset = Peerset {
			data,
			tx,
			rx,
			message_queue: VecDeque::new(),
		};

		peerset.alloc_slots();

		let handle = peerset.handle();

		for reserved in config.reserved_nodes {
			handle.add_reserved_peer(reserved);
		}

		peerset
	}

	fn handle(&self) -> PeersetHandle {
		PeersetHandle {
			tx: self.tx.clone(),
		}
	}

	fn add_reserved_peer(&mut self, peer_id: PeerId) {
		if !self.data.reserved.insert(peer_id.clone()) {
			// Immediately return if this peer was already in the list.
			return;
		}

		// Nothing more to do if we're already connected.
		if self.data.out_slots.iter().chain(self.data.in_slots.iter()).any(|s| s.as_ref() == Some(&peer_id)) {
			return;
		}

		// Assign a slot for this reserved peer.
		if let Some(pos) = self.data.out_slots.iter().position(|s| s.as_ref().map(|n| !self.data.reserved.contains(n)).unwrap_or(true)) {
			self.message_queue.push_back(Message::Connect(peer_id.clone()));
			self.data.out_slots[pos] = Some(peer_id);
		} else {
			// All slots are filled with reserved peers.
			if self.data.discovered.iter().all(|p| *p != peer_id) {
				self.data.discovered.push(peer_id);
			}
		}
	}

	fn remove_reserved_peer(&mut self, peer_id: &PeerId) {
		self.data.reserved.remove(peer_id);
	}

	fn set_reserved_only(&mut self, reserved_only: bool) {
		// Disconnect non-reserved nodes.
		if self.data.reserved_only {
			for slot in self.data.out_slots.iter_mut().chain(self.data.in_slots.iter_mut()) {
				if let Some(peer) = slot.as_ref() {
					if self.data.reserved.contains(peer) {
						continue;
					}

					self.message_queue.push_back(Message::Drop(peer.clone()));
				}

				*slot = None;
			}
		}
	}

	pub fn report_peer(&self, _peer_id: PeerId, _score_diff: i32) {
		//unimplemented!();
		// This is not implemented in this dummy implementation.
	}

	fn alloc_slots(&mut self) {
		if self.data.reserved_only {
			return;
		}

		for slot in self.data.out_slots.iter_mut() {
			if slot.is_some() {
				continue;
			}

			if !self.data.discovered.is_empty() {
				let elem = self.data.discovered.remove(0);
				*slot = Some(elem.clone());
				self.message_queue.push_back(Message::Connect(elem));
			}
		}
	}

	fn incoming(&mut self, peer_id: PeerId, index: IncomingIndex) {
		if self.data.out_slots.iter().chain(self.data.in_slots.iter()).any(|s| s.as_ref() == Some(&peer_id)) {
			return
		}

		if let Some(pos) = self.data.in_slots.iter().position(|s| s.is_none()) {
			self.data.in_slots[pos] = Some(peer_id);
			self.message_queue.push_back(Message::Accept(index));
		} else {
			if self.data.discovered.iter().all(|p| *p != peer_id) {
				self.data.discovered.push(peer_id);
			}
			self.message_queue.push_back(Message::Reject(index));
		}
	}

	fn dropped(&mut self, peer_id: PeerId) {
		// Automatically connect back if reserved.
		if self.data.reserved.contains(&peer_id) {
			self.message_queue.push_back(Message::Connect(peer_id.clone()));
			return
		}

		// Otherwise, free the slot.
		for slot in self.data.out_slots.iter_mut().chain(self.data.in_slots.iter_mut()) {
			if slot.as_ref() == Some(&peer_id) {
				*slot = None;
				break;
			}
		}

		// Note: in this dummy implementation we consider that peers never expire. As soon as we
		// are disconnected from a peer, we try again.
		if self.data.discovered.iter().all(|p| p != &peer_id) {
			self.data.discovered.push(peer_id.clone());
		}
		self.alloc_slots();
	}

	fn discovered(&mut self, peer_id: PeerId) {
		if self.data.out_slots.iter().chain(self.data.in_slots.iter()).any(|p| p.as_ref() == Some(&peer_id)) {
			return;
		}

		if self.data.discovered.iter().all(|p| *p != peer_id) {
			self.data.discovered.push(peer_id);
		}
		self.alloc_slots();
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
					Action::AddReservedPeer(peer_id) => self.add_reserved_peer(peer_id),
					Action::RemoveReservedPeer(peer_id) => self.remove_reserved_peer(&peer_id),
					Action::SetReservedOnly(reserved) => self.set_reserved_only(reserved),
					Action::ReportPeer(peer_id, score_diff) => self.report_peer(peer_id, score_diff),
					Action::Incoming(peer_id, index) => self.incoming(peer_id, index),
					Action::Dropped(peer_id) => self.dropped(peer_id),
					Action::Discovered(peer_id) => self.discovered(peer_id),
				}
			}
		}
	}
}
