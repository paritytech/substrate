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

use std::collections::HashSet;
use futures::{prelude::*, sync::mpsc};
use libp2p::PeerId;
use parking_lot::Mutex;
use std::sync::Arc;

pub use serde_json::Value;

/// Shared part of the peer set manager (PSM). Distributed around the code.
pub struct Peerset {
	tx: mpsc::UnboundedSender<Message>,
	inner: Mutex<Inner>,
}

struct Inner {
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
pub struct PeersetMut {
	parent: Arc<Peerset>,
	rx: mpsc::UnboundedReceiver<Message>,
}

impl Peerset {
	/// Builds a new peerset from the given configuration.
	pub fn from_config(config: PeersetConfig) -> (Arc<Peerset>, PeersetMut) {
		let (tx, rx) = mpsc::unbounded();

		let mut inner = Inner {
			discovered: config.bootnodes.into_iter().collect(),
			reserved: Default::default(),
			reserved_only: config.reserved_only,
			out_slots: (0 .. config.out_peers).map(|_| None).collect(),
			in_slots: (0 .. config.in_peers).map(|_| None).collect(),
		};

		alloc_slots(&mut inner, &tx);

		let peerset = Arc::new(Peerset {
			tx,
			inner: Mutex::new(inner),
		});

		let rx = PeersetMut {
			parent: peerset.clone(),
			rx,
		};

		for reserved in config.reserved_nodes {
			peerset.add_reserved_peer(reserved);
		}

		(peerset, rx)
	}

	/// Adds a new reserved peer. The peerset will make an effort to always remain connected to
	/// this peer.
	///
	/// Has no effect if the node was already a reserved peer.
	///
	/// > **Note**: Keep in mind that the networking has to know an address for this node,
	/// >			otherwise it will not be able to connect to it.
	pub fn add_reserved_peer(&self, peer_id: PeerId) {
		let mut inner = self.inner.lock();
		if !inner.reserved.insert(peer_id.clone()) {
			// Immediately return if this peer was already in the list.
			return;
		}

		// Nothing more to do if we're already connected.
		if inner.out_slots.iter().chain(inner.in_slots.iter()).any(|s| s.as_ref() == Some(&peer_id)) {
			return;
		}

		// Assign a slot for this reserved peer.
		if let Some(pos) = inner.out_slots.iter().position(|s| s.as_ref().map(|n| !inner.reserved.contains(n)).unwrap_or(true)) {
			let _ = self.tx.unbounded_send(Message::Connect(peer_id.clone()));
			inner.out_slots[pos] = Some(peer_id);

		} else {
			// All slots are filled with reserved peers.
			if inner.discovered.iter().all(|p| *p != peer_id) {
				inner.discovered.push(peer_id);
			}
		}
	}

	/// Remove a previously-added reserved peer.
	///
	/// Has no effect if the node was not a reserved peer.
	pub fn remove_reserved_peer(&self, peer_id: &PeerId) {
		let mut inner = self.inner.lock();
		inner.reserved.remove(peer_id);
	}

	/// Sets whether or not the peerset only has connections .
	pub fn set_reserved_only(&self, reserved_only: bool) {
		let mut inner = self.inner.lock();
		let inner = &mut *inner;	// Fixes a borrowing issue.
		inner.reserved_only = reserved_only;

		// Disconnect non-reserved nodes.
		if reserved_only {
			for slot in inner.out_slots.iter_mut().chain(inner.in_slots.iter_mut()) {
				if let Some(peer) = slot.as_ref() {
					if inner.reserved.contains(peer) {
						continue;
					}

					let _ = self.tx.unbounded_send(Message::Drop(peer.clone()));
				}

				*slot = None;
			}
		}
	}

	/// Reports an adjustement to the reputation of the given peer.
	pub fn report_peer(&self, _peer_id: &PeerId, _score_diff: i32) {
		// This is not implemented in this dummy implementation.
	}
}

fn alloc_slots(inner: &mut Inner, tx: &mpsc::UnboundedSender<Message>) {
	if inner.reserved_only {
		return;
	}

	for slot in inner.out_slots.iter_mut() {
		if slot.is_some() {
			continue;
		}

		if !inner.discovered.is_empty() {
			let elem = inner.discovered.remove(0);
			*slot = Some(elem.clone());
			let _ = tx.unbounded_send(Message::Connect(elem));
		}
	}
}

impl PeersetMut {
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
		let mut inner = self.parent.inner.lock();
		if inner.out_slots.iter().chain(inner.in_slots.iter()).any(|s| s.as_ref() == Some(&peer_id)) {
			return
		}

		if let Some(pos) = inner.in_slots.iter().position(|s| s.is_none()) {
			inner.in_slots[pos] = Some(peer_id);
			let _ = self.parent.tx.unbounded_send(Message::Accept(index));
		} else {
			if inner.discovered.iter().all(|p| *p != peer_id) {
				inner.discovered.push(peer_id);
			}
			let _ = self.parent.tx.unbounded_send(Message::Reject(index));
		}
	}

	/// Indicate that we dropped an active connection with a peer, or that we failed to connect.
	///
	/// Must only be called after the PSM has either generated a `Connect` message with this
	/// `PeerId`, or accepted an incoming connection with this `PeerId`.
	pub fn dropped(&self, peer_id: &PeerId) {
		let mut inner = self.parent.inner.lock();
		let inner = &mut *inner;	// Fixes a borrowing issue.

		// Automatically connect back if reserved.
		if inner.reserved.contains(peer_id) {
			let _ = self.parent.tx.unbounded_send(Message::Connect(peer_id.clone()));
			return
		}

		// Otherwise, free the slot.
		for slot in inner.out_slots.iter_mut().chain(inner.in_slots.iter_mut()) {
			if slot.as_ref() == Some(peer_id) {
				*slot = None;
				break;
			}
		}

		// Note: in this dummy implementation we consider that peers never expire. As soon as we
		// are disconnected from a peer, we try again.
		if inner.discovered.iter().all(|p| p != peer_id) {
			inner.discovered.push(peer_id.clone());
		}
		alloc_slots(inner, &self.parent.tx);
	}

	/// Adds a discovered peer id to the PSM.
	///
	/// > **Note**: There is no equivalent "expired" message, meaning that it is the responsibility
	/// >			of the PSM to remove `PeerId`s that fail to dial too often.
	pub fn discovered(&self, peer_id: PeerId) {
		let mut inner = self.parent.inner.lock();

		if inner.out_slots.iter().chain(inner.in_slots.iter()).any(|p| p.as_ref() == Some(&peer_id)) {
			return;
		}

		if inner.discovered.iter().all(|p| *p != peer_id) {
			inner.discovered.push(peer_id);
		}
		alloc_slots(&mut inner, &self.parent.tx);
	}

	/// Produces a JSON object containing the state of the peerset manager, for debugging purposes.
	pub fn debug_info(&self) -> serde_json::Value {
		serde_json::Value::Null
	}
}

impl Stream for PeersetMut {
	type Item = Message;
	type Error = ();

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		self.rx.poll()
	}
}
