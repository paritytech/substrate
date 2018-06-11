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

//! Utility for gossip of network messages between authorities.
//! Handles chain-specific and standard BFT messages.

use std::collections::{HashMap, HashSet};
use futures::sync::mpsc;
use std::time::{Instant, Duration};
use network::PeerId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use message::{self, generic::Message as GenericMessage};
use protocol::Context;

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
}

#[derive(Clone)]
enum ConsensusMessage<B: BlockT> {
	Bft(message::LocalizedBftMessage<B>),
	ChainSpecific(Vec<u8>, B::Hash),
}

struct MessageEntry<B: BlockT> {
	hash: B::Hash,
	message: ConsensusMessage<B>,
	instant: Instant,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<PeerId, PeerConsensus<B::Hash>>,
	bft_message_sink: Option<(mpsc::UnboundedSender<message::LocalizedBftMessage<B>>, B::Hash)>,
	messages: Vec<MessageEntry<B>>,
	message_hashes: HashSet<B::Hash>,
}

impl<B: BlockT> ConsensusGossip<B> where B::Header: HeaderT<Number=u64> {
	/// Create a new instance.
	pub fn new() -> Self {
		ConsensusGossip {
			peers: HashMap::new(),
			bft_message_sink: None,
			messages: Default::default(),
			message_hashes: Default::default(),
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.bft_message_sink = None;
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, peer_id: PeerId, roles: &[message::Role]) {
		if roles.iter().any(|r| *r == message::Role::Authority) {
			trace!(target:"sync", "Registering authority {}", peer_id);
			// Send out all known messages.
			// TODO: limit by size
			let mut known_messages = HashSet::new();
			for entry in self.messages.iter() {
				known_messages.insert(entry.hash);
				let message = match entry.message {
					ConsensusMessage::Bft(ref bft) => GenericMessage::BftMessage(bft.clone()),
					ConsensusMessage::ChainSpecific(ref msg, _) => GenericMessage::ChainSpecific(msg.clone()),
				};

				protocol.send_message(peer_id, message);
			}
			self.peers.insert(peer_id, PeerConsensus {
				known_messages,
			});
		}
	}

	fn propagate(&mut self, protocol: &mut Context<B>, message: message::Message<B>, hash: B::Hash) {
		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.known_messages.insert(hash.clone()) {
				protocol.send_message(*id, message.clone());
			}
		}
	}

	fn register_message(&mut self, hash: B::Hash, message: ConsensusMessage<B>) {
		if self.message_hashes.insert(hash) {
			self.messages.push(MessageEntry {
				hash,
				instant: Instant::now(),
				message,
			});
		}
	}

	/// Handles incoming BFT message, passing to stream and repropagating.
	pub fn on_bft_message(&mut self, protocol: &mut Context<B>, peer_id: PeerId, message: message::LocalizedBftMessage<B>) {
		let generic = GenericMessage::BftMessage(message);
		let hash = ::protocol::hash_message(&generic);

		let message = match generic {
			GenericMessage::BftMessage(msg) => msg,
			_ => panic!("`generic` is known to be the `BftMessage` variant; qed"),
		};

		if self.message_hashes.contains(&hash) {
			trace!(target:"sync", "Ignored already known BFT message from {}", peer_id);
			return;
		}

		match (protocol.client().info(), protocol.client().header(&BlockId::Hash(message.parent_hash))) {
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

		// propagate to other peers.
		self.multicast(protocol, ConsensusMessage::Bft(message), Some(hash));
	}

	/// Get a stream of BFT messages relevant to consensus on top of a given parent hash.
	pub fn bft_messages(&mut self, parent_hash: B::Hash) -> mpsc::UnboundedReceiver<message::LocalizedBftMessage<B>> {
		let (sink, stream) = mpsc::unbounded();

		for entry in self.messages.iter() {
			let bft_message = match entry.message {
				ConsensusMessage::Bft(ref msg) => msg,
				_ => continue,
			};

			if bft_message.parent_hash == parent_hash {
				sink.unbounded_send(bft_message.clone()).expect("receiving end known to be open; qed");
			}
		}

		self.bft_message_sink = Some((sink, parent_hash));
		stream
	}

	/// Multicast a chain-specific message to other authorities.
	pub fn multicast_chain_specific(&mut self, protocol: &mut Context<B>, parent_hash: B::Hash, message: Vec<u8>) {
		trace!(target: "bft", "sending chain-specific message");
		self.multicast(protocol, ConsensusMessage::ChainSpecific(message, parent_hash), None);
	}

	/// Multicast a BFT message to other authorities
	pub fn multicast_bft_message(&mut self, protocol: &mut Context<B>, message: message::LocalizedBftMessage<B>) {
		// Broadcast message to all authorities.
		trace!(target:"bft", "Broadcasting BFT message {:?}", message);
		self.multicast(protocol, ConsensusMessage::Bft(message), None);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, _protocol: &mut Context<B>, peer_id: PeerId) {
		self.peers.remove(&peer_id);
	}

	/// Prune old or no longer relevant consensus messages.
	pub fn collect_garbage(&mut self, best_header: Option<&B::Header>) {
		let hashes = &mut self.message_hashes;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|entry| {
			if entry.instant + MESSAGE_LIFETIME >= now &&
				best_header.map_or(true, |header|
					match entry.message {
						ConsensusMessage::Bft(ref msg) => &msg.parent_hash != header.parent_hash(),
						ConsensusMessage::ChainSpecific(_, ref h) => h != header.parent_hash(),
					})
			{
				true
			} else {
				hashes.remove(&entry.hash);
				false
			}
		});
		if self.messages.len() != before {
			trace!(target:"bft", "Cleaned up {} stale messages", before - self.messages.len());
		}
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}

	fn multicast(&mut self, protocol: &mut Context<B>, message: ConsensusMessage<B>, hash: Option<B::Hash>) {
		let generic = match message {
			ConsensusMessage::Bft(ref message) => GenericMessage::BftMessage(message.clone()),
			ConsensusMessage::ChainSpecific(ref message, _) => GenericMessage::ChainSpecific(message.clone()),
		};

		let hash = hash.unwrap_or_else(|| ::protocol::hash_message(&generic));
		self.register_message(hash, message);
		self.propagate(protocol, generic, hash);
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::bft::Justification;
	use runtime_primitives::testing::{H256, Header, Block as RawBlock};
	use std::time::Instant;
	use message::{self, generic};
	use super::*;

	type Block = RawBlock<u64>;

	#[test]
	fn collects_garbage() {
		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = ConsensusGossip::<Block>::new();
		let now = Instant::now();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = ConsensusMessage::Bft(message::LocalizedBftMessage {
			parent_hash: prev_hash,
			message: message::generic::BftMessage::Auxiliary(Justification {
				round_number: 0,
				hash: Default::default(),
				signatures: Default::default(),
			}),
		});
		let m2 = ConsensusMessage::ChainSpecific(vec![1, 2, 3], best_hash);

		macro_rules! push_msg {
			($hash:expr, $now: expr, $m:expr) => {
				consensus.messages.push(MessageEntry {
					hash: $hash,
					instant: $now,
					message: $m,
				})
			}
		}

		push_msg!(m1_hash, now, m1);
		push_msg!(m2_hash, now, m2.clone());
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
		push_msg!(m2_hash, now - MESSAGE_LIFETIME, m2);
		consensus.collect_garbage(None);
		assert!(consensus.messages.is_empty());
		assert!(consensus.message_hashes.is_empty());
	}

	#[test]
	fn bft_messages_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::new();

		let bft_message = generic::BftMessage::Consensus(generic::SignedConsensusMessage::Vote(generic::SignedConsensusVote {
			vote: generic::ConsensusVote::AdvanceRound(0),
			sender: [0; 32],
			signature: Default::default(),
		}));

		let parent_hash = [1; 32].into();

		let localized = ::message::LocalizedBftMessage::<Block> {
			message: bft_message,
			parent_hash: parent_hash,
		};

		let message = generic::Message::BftMessage(localized.clone());
		let message_hash = ::protocol::hash_message::<Block>(&message);

		consensus.register_message(message_hash, ConsensusMessage::Bft(localized.clone()));
		let stream = consensus.bft_messages(parent_hash);

		assert_eq!(stream.wait().next(), Some(Ok(localized)));
	}
}
