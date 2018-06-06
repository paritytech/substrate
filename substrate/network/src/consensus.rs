// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Consensus related bits of the network service.

use std::collections::{HashMap, HashSet};
use futures::sync::mpsc;
use std::time::{Instant, Duration};
use io::SyncIo;
use protocol::Protocol;
use network::PeerId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use message::{self, generic::Message as GenericMessage};

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct Consensus<B: BlockT> {
	peers: HashMap<PeerId, PeerConsensus<B::Hash>>,
	bft_message_sink: Option<(mpsc::UnboundedSender<message::LocalizedBftMessage<B>>, B::Hash)>,
	messages: Vec<(B::Hash, Instant, message::Message<B>)>,
	message_hashes: HashSet<B::Hash>,
}

impl<B: BlockT> Consensus<B> where B::Header: HeaderT<Number=u64> {
	/// Create a new instance.
	pub fn new() -> Self {
		Consensus {
			peers: HashMap::new(),
			bft_message_sink: None,
			messages: Default::default(),
			message_hashes: Default::default(),
		}
	}

	/// Closes all notification streams.
	pub fn restart(&mut self) {
		self.bft_message_sink = None;
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, io: &mut SyncIo, protocol: &Protocol<B>, peer_id: PeerId, roles: &[message::Role]) {
		if roles.iter().any(|r| *r == message::Role::Validator) {
			trace!(target:"sync", "Registering validator {}", peer_id);
			// Send out all known messages.
			// TODO: limit by size
			let mut known_messages = HashSet::new();
			for &(ref hash, _, ref message) in self.messages.iter() {
				known_messages.insert(hash.clone());
				protocol.send_message(io, peer_id, message.clone());
			}
			self.peers.insert(peer_id, PeerConsensus {
				known_messages,
			});
		}
	}

	fn propagate(&mut self, io: &mut SyncIo, protocol: &Protocol<B>, message: message::Message<B>, hash: B::Hash) {
		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.known_messages.insert(hash.clone()) {
				protocol.send_message(io, *id, message.clone());
			}
		}
	}

	fn register_message(&mut self, hash: B::Hash, message: message::Message<B>) {
		if self.message_hashes.insert(hash) {
			self.messages.push((hash, Instant::now(), message));
		}
	}

	pub fn on_bft_message(&mut self, io: &mut SyncIo, protocol: &Protocol<B>, peer_id: PeerId, message: message::LocalizedBftMessage<B>, hash: B::Hash) {
		if self.message_hashes.contains(&hash) {
			trace!(target:"sync", "Ignored already known BFT message from {}", peer_id);
			return;
		}

		match (protocol.chain().info(), protocol.chain().header(&BlockId::Hash(message.parent_hash))) {
			(_, Err(e)) | (Err(e), _) => {
				debug!(target:"sync", "Error reading blockchain: {:?}", e);
				return;
			},
			(Ok(info), Ok(Some(header))) => {
				if header.number() < &info.chain.best_number {
					trace!(target:"sync", "Ignored ancient BFT message from {}, hash={}", peer_id, message.parent_hash);
					return;
				}
			},
			(Ok(_), Ok(None)) => {},
		}

		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			peer.known_messages.insert(hash);
			// TODO: validate signature?
			if let Some((sink, parent_hash)) = self.bft_message_sink.take() {
				if message.parent_hash == parent_hash {
					if let Err(e) = sink.unbounded_send(message.clone()) {
						trace!(target:"sync", "Error broadcasting BFT message notification: {:?}", e);
					} else {
						self.bft_message_sink = Some((sink, parent_hash));
					}
				}
			}
		} else {
			trace!(target:"sync", "Ignored BFT statement from unregistered peer {}", peer_id);
			return;
		}

		let message = GenericMessage::BftMessage(message);
		self.register_message(hash.clone(), message.clone());
		// Propagate to other peers.
		self.propagate(io, protocol, message, hash);
	}

	pub fn bft_messages(&mut self, parent_hash: B::Hash) -> mpsc::UnboundedReceiver<message::LocalizedBftMessage<B>> {
		let (sink, stream) = mpsc::unbounded();

		for &(_, _, ref message) in self.messages.iter() {
			let bft_message = match *message {
				GenericMessage::BftMessage(ref msg) => msg,
				_ => continue,
			};

			if bft_message.parent_hash == parent_hash {
				sink.unbounded_send(bft_message.clone()).expect("receiving end known to be open; qed");
			}
		}

		self.bft_message_sink = Some((sink, parent_hash));
		stream
	}

	pub fn send_bft_message(&mut self, io: &mut SyncIo, protocol: &Protocol<B>, message: message::LocalizedBftMessage<B>) {
		// Broadcast message to all validators.
		trace!(target:"sync", "Broadcasting BFT message {:?}", message);
		let message = GenericMessage::BftMessage(message);
		let hash = Protocol::hash_message(&message);
		self.register_message(hash.clone(), message.clone());
		self.propagate(io, protocol, message, hash);
	}

	pub fn peer_disconnected(&mut self, _io: &mut SyncIo, _protocol: &Protocol<B>, peer_id: PeerId) {
		self.peers.remove(&peer_id);
	}

	pub fn collect_garbage(&mut self, best_header: Option<&B::Header>) {
		let hashes = &mut self.message_hashes;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|&(ref hash, timestamp, ref message)| {
			if timestamp >= now - MESSAGE_LIFETIME &&
				best_header.map_or(true, |header|
					match *message {
						GenericMessage::BftMessage(ref msg) => &msg.parent_hash != header.parent_hash(),
						_ => true,
					})
			{
				true
			} else {
				hashes.remove(hash);
				false
			}
		});
		if self.messages.len() != before {
			trace!(target:"sync", "Cleaned up {} stale messages", before - self.messages.len());
		}
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::bft::Justification;
	use runtime_primitives::testing::{H256, Header, Block as RawBlock};
	use std::time::Instant;
	use message::{self, generic::Message as GenericMessage};
	use super::{Consensus, MESSAGE_LIFETIME};

	type Block = RawBlock<u64>;

	#[test]
	fn collects_garbage() {
		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = Consensus::<Block>::new();
		let now = Instant::now();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = GenericMessage::BftMessage(message::LocalizedBftMessage {
			parent_hash: prev_hash,
			message: message::generic::BftMessage::Auxiliary(Justification {
				round_number: 0,
				hash: Default::default(),
				signatures: Default::default(),
			}),
		});
		let m2 = GenericMessage::BftMessage(message::LocalizedBftMessage {
			parent_hash: best_hash,
			message: message::generic::BftMessage::Auxiliary(Justification {
				round_number: 0,
				hash: Default::default(),
				signatures: Default::default(),
			}),
		});
		consensus.messages.push((m1_hash, now, m1));
		consensus.messages.push((m2_hash, now, m2.clone()));
		consensus.message_hashes.insert(m1_hash);
		consensus.message_hashes.insert(m2_hash);

		// nothing to collect
		consensus.collect_garbage(None);
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// random header, nothing should be cleared
		let mut header = Header {
			parent_hash: H256::default(),
			number: 0,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Default::default(),
		};

		consensus.collect_garbage(Some(&header));
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// header that matches one of the messages
		header.parent_hash = prev_hash;
		consensus.collect_garbage(Some(&header));
		assert_eq!(consensus.messages.len(), 1);
		assert_eq!(consensus.message_hashes.len(), 1);
		assert!(consensus.message_hashes.contains(&m2_hash));

		// make timestamp expired
		consensus.messages.clear();
		consensus.messages.push((m2_hash, now - MESSAGE_LIFETIME, m2));
		consensus.collect_garbage(None);
		assert!(consensus.messages.is_empty());
		assert!(consensus.message_hashes.is_empty());
	}
}
