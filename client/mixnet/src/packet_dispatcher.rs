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

//! [`AddressedPacket`] dispatching.

use super::peer_id::{from_core_peer_id, to_core_peer_id};
use arrayvec::ArrayVec;
use libp2p_identity::PeerId;
use log::{debug, error, warn};
use mixnet::core::{AddressedPacket, NetworkStatus, Packet, PeerId as CorePeerId};
use parking_lot::Mutex;
use sc_network::{NetworkNotification, ProtocolName};
use std::{collections::HashMap, future::Future, sync::Arc};

const LOG_TARGET: &str = "mixnet";

/// Packet queue for a peer.
///
/// Ideally we would use `Rc<RefCell<_>>`, but that would prevent the top-level future from being
/// automatically marked `Send`. I believe it would be safe to manually mark it `Send`, but using
/// `Arc<Mutex<_>>` here is not really a big deal.
struct PeerQueue(Mutex<ArrayVec<Box<Packet>, 2>>);

impl PeerQueue {
	fn new() -> Self {
		Self(Mutex::new(ArrayVec::new()))
	}

	/// Push `packet` onto the queue. Returns `true` if the queue was previously empty. Fails if
	/// the queue is full.
	fn push(&self, packet: Box<Packet>) -> Result<bool, ()> {
		let mut queue = self.0.lock();
		if queue.is_full() {
			Err(())
		} else {
			let was_empty = queue.is_empty();
			queue.push(packet);
			Ok(was_empty)
		}
	}

	/// Drop all packets from the queue.
	fn clear(&self) {
		let mut queue = self.0.lock();
		queue.clear();
	}

	/// Pop the packet at the head of the queue and return it, or, if the queue is empty, return
	/// `None`. Also returns `true` if there are more packets in the queue.
	fn pop(&self) -> (Option<Box<Packet>>, bool) {
		let mut queue = self.0.lock();
		let packet = queue.pop();
		(packet, !queue.is_empty())
	}
}

/// A peer which has packets ready to send but is not currently being serviced.
pub struct ReadyPeer {
	id: PeerId,
	/// The peer's packet queue. Not empty.
	queue: Arc<PeerQueue>,
}

impl ReadyPeer {
	/// If a future is returned, and if that future returns `Some`, this function should be called
	/// again to send the next packet queued for the peer; `self` is placed in the `Some` to make
	/// this straightforward. Otherwise, we have either sent or dropped all packets queued for the
	/// peer, and it can be forgotten about for the time being.
	pub fn send_packet(
		self,
		network: &impl NetworkNotification,
		protocol_name: ProtocolName,
	) -> Option<impl Future<Output = Option<Self>>> {
		match network.notification_sender(self.id, protocol_name) {
			Err(err) => {
				warn!(
					target: LOG_TARGET,
					"Failed to get notification sender for peer ID {}: {err}", self.id
				);
				self.queue.clear();
				None
			},
			Ok(sender) => Some(async move {
				match sender.ready().await.and_then(|mut ready| {
					let (packet, more_packets) = self.queue.pop();
					let packet =
						packet.expect("Should only be called if there is a packet to send");
					ready.send((packet as Box<[_]>).into())?;
					Ok(more_packets)
				}) {
					Err(err) => {
						warn!(
							target: LOG_TARGET,
							"Notification sender for peer ID {} failed: {err}", self.id
						);
						self.queue.clear();
						None
					},
					Ok(more_packets) => more_packets.then(|| self),
				}
			}),
		}
	}
}

pub struct PacketDispatcher {
	/// Peer ID of the local node. Only used to implement [`NetworkStatus`].
	local_peer_id: CorePeerId,
	/// Packet queue for each connected peer. These queues are very short and only exist to give
	/// packets somewhere to sit while waiting for notification senders to be ready.
	peer_queues: HashMap<CorePeerId, Arc<PeerQueue>>,
}

impl PacketDispatcher {
	pub fn new(local_peer_id: &CorePeerId) -> Self {
		Self { local_peer_id: *local_peer_id, peer_queues: HashMap::new() }
	}

	pub fn add_peer(&mut self, id: &PeerId) {
		let Some(core_id) = to_core_peer_id(id) else {
			error!(target: LOG_TARGET,
				"Cannot add peer; failed to convert libp2p peer ID {id} to mixnet peer ID");
			return
		};
		if self.peer_queues.insert(core_id, Arc::new(PeerQueue::new())).is_some() {
			error!(target: LOG_TARGET, "Two stream opened notifications for peer ID {id}");
		}
	}

	pub fn remove_peer(&mut self, id: &PeerId) {
		let Some(core_id) = to_core_peer_id(id) else {
			error!(target: LOG_TARGET,
				"Cannot remove peer; failed to convert libp2p peer ID {id} to mixnet peer ID");
			return
		};
		if self.peer_queues.remove(&core_id).is_none() {
			error!(target: LOG_TARGET, "Stream closed notification for unknown peer ID {id}");
		}
	}

	/// If the peer is not connected or the peer's packet queue is full, the packet is dropped.
	/// Otherwise the packet is pushed onto the peer's queue, and if the queue was previously empty
	/// a [`ReadyPeer`] is returned.
	pub fn dispatch(&mut self, packet: AddressedPacket) -> Option<ReadyPeer> {
		let Some(queue) = self.peer_queues.get_mut(&packet.peer_id) else {
			debug!(target: LOG_TARGET, "Dropped packet to mixnet peer ID {:x?}; not connected",
				packet.peer_id);
			return None
		};

		match queue.push(packet.packet) {
			Err(_) => {
				warn!(
					target: LOG_TARGET,
					"Dropped packet to mixnet peer ID {:x?}; peer queue full", packet.peer_id
				);
				None
			},
			Ok(true) => {
				// Queue was empty. Construct and return a ReadyPeer.
				let Some(id) = from_core_peer_id(&packet.peer_id) else {
					error!(target: LOG_TARGET, "Cannot send packet; \
						failed to convert mixnet peer ID {:x?} to libp2p peer ID",
						packet.peer_id);
					queue.clear();
					return None
				};
				Some(ReadyPeer { id, queue: queue.clone() })
			},
			Ok(false) => None, // Queue was not empty
		}
	}
}

impl NetworkStatus for PacketDispatcher {
	fn local_peer_id(&self) -> CorePeerId {
		self.local_peer_id
	}

	fn is_connected(&self, peer_id: &CorePeerId) -> bool {
		self.peer_queues.contains_key(peer_id)
	}
}
