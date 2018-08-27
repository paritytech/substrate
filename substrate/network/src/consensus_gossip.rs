// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Utility for gossip of network messages between authorities.
//! Handles chain-specific and standard BFT messages.

use std::collections::{HashMap, HashSet};
use futures::sync::mpsc;
use std::time::{Instant, Duration};
use network_libp2p::NodeIndex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use message::{self, generic::Message as GenericMessage};
use protocol::Context;
use service::Roles;

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
}

/// Consensus messages.
#[derive(Debug, Clone, PartialEq)]
pub enum ConsensusMessage<B: BlockT> {
	/// A message concerning BFT agreement
	Bft(message::LocalizedBftMessage<B>),
	/// A message concerning some chain-specific aspect of consensus
	ChainSpecific(Vec<u8>, B::Hash),
}

struct MessageEntry<B: BlockT> {
	hash: B::Hash,
	message: ConsensusMessage<B>,
	instant: Instant,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<B::Hash>>,
	message_sink: Option<(mpsc::UnboundedSender<ConsensusMessage<B>>, B::Hash)>,
	messages: Vec<MessageEntry<B>>,
	message_hashes: HashSet<B::Hash>,
}

impl<B: BlockT> ConsensusGossip<B> where B::Header: HeaderT<Number=u64> {
	/// Create a new instance.
	pub fn new() -> Self {
		ConsensusGossip {
			peers: HashMap::new(),
			message_sink: None,
			messages: Default::default(),
			message_hashes: Default::default(),
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.message_sink = None;
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, who: NodeIndex, roles: Roles) {
		if roles.intersects(Roles::AUTHORITY | Roles::FULL) {
			trace!(target:"gossip", "Registering {:?} {}", roles, who);
			// Send out all known messages.
			// TODO: limit by size
			let mut known_messages = HashSet::new();
			for entry in self.messages.iter() {
				known_messages.insert(entry.hash);
				let message = match entry.message {
					ConsensusMessage::Bft(ref bft) => GenericMessage::BftMessage(bft.clone()),
					ConsensusMessage::ChainSpecific(ref msg, _) => GenericMessage::ChainSpecific(msg.clone()),
				};

				protocol.send_message(who, message);
			}
			self.peers.insert(who, PeerConsensus {
				known_messages,
			});
		}
	}

	fn propagate(&mut self, protocol: &mut Context<B>, message: message::Message<B>, hash: B::Hash) {
		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.known_messages.insert(hash.clone()) {
				trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
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
	pub fn on_bft_message(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: message::LocalizedBftMessage<B>) {
		if let Some((hash, message)) = self.handle_incoming(protocol, who, ConsensusMessage::Bft(message)) {
			// propagate to other peers.
			self.multicast(protocol, message, Some(hash));
		}
	}

	/// Handles incoming chain-specific message and repropagates
	pub fn on_chain_specific(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: Vec<u8>, parent_hash: B::Hash) {
		debug!(target: "gossip", "received chain-specific gossip message");
		if let Some((hash, message)) = self.handle_incoming(protocol, who, ConsensusMessage::ChainSpecific(message, parent_hash)) {
			debug!(target: "gossip", "handled incoming chain-specific message");
			// propagate to other peers.
			self.multicast(protocol, message, Some(hash));
		}
	}

	/// Get a stream of messages relevant to consensus on top of a given parent hash.
	pub fn messages_for(&mut self, parent_hash: B::Hash) -> mpsc::UnboundedReceiver<ConsensusMessage<B>> {
		let (sink, stream) = mpsc::unbounded();

		for entry in self.messages.iter() {
			let message_matches = match entry.message {
				ConsensusMessage::Bft(ref msg) => msg.parent_hash == parent_hash,
				ConsensusMessage::ChainSpecific(_, ref h) => h == &parent_hash,
			};

			if message_matches {
				sink.unbounded_send(entry.message.clone()).expect("receiving end known to be open; qed");
			}
		}

		self.message_sink = Some((sink, parent_hash));
		stream
	}

	/// Multicast a chain-specific message to other authorities.
	pub fn multicast_chain_specific(&mut self, protocol: &mut Context<B>, message: Vec<u8>, parent_hash: B::Hash) {
		trace!(target:"gossip", "sending chain-specific message");
		self.multicast(protocol, ConsensusMessage::ChainSpecific(message, parent_hash), None);
	}

	/// Multicast a BFT message to other authorities
	pub fn multicast_bft_message(&mut self, protocol: &mut Context<B>, message: message::LocalizedBftMessage<B>) {
		// Broadcast message to all authorities.
		trace!(target:"gossip", "Broadcasting BFT message {:?}", message);
		self.multicast(protocol, ConsensusMessage::Bft(message), None);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, _protocol: &mut Context<B>, who: NodeIndex) {
		self.peers.remove(&who);
	}

	/// Prune old or no longer relevant consensus messages.
	/// Supply an optional block hash where consensus is known to have concluded.
	pub fn collect_garbage(&mut self, best_hash: Option<&B::Hash>) {
		let hashes = &mut self.message_hashes;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|entry| {
			if entry.instant + MESSAGE_LIFETIME >= now &&
				best_hash.map_or(true, |parent_hash|
					match entry.message {
						ConsensusMessage::Bft(ref msg) => &msg.parent_hash != parent_hash,
						ConsensusMessage::ChainSpecific(_, ref h) => h != parent_hash,
					})
			{
				true
			} else {
				hashes.remove(&entry.hash);
				false
			}
		});
		if self.messages.len() != before {
			trace!(target:"gossip", "Cleaned up {} stale messages", before - self.messages.len());
		}
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}

	fn handle_incoming(&mut self, protocol: &mut Context<B>, who: NodeIndex, message: ConsensusMessage<B>) -> Option<(B::Hash, ConsensusMessage<B>)> {
		let (hash, parent, message) = match message {
			ConsensusMessage::Bft(msg) => {
				let parent = msg.parent_hash;
				let generic = GenericMessage::BftMessage(msg);
				(
					::protocol::hash_message(&generic),
					parent,
					match generic {
						GenericMessage::BftMessage(msg) => ConsensusMessage::Bft(msg),
						_ => panic!("`generic` is known to be the `BftMessage` variant; qed"),
					}
				)
			}
			ConsensusMessage::ChainSpecific(msg, parent) => {
				let generic = GenericMessage::ChainSpecific(msg);
				(
					::protocol::hash_message::<B>(&generic),
					parent,
					match generic {
						GenericMessage::ChainSpecific(msg) => ConsensusMessage::ChainSpecific(msg, parent),
						_ => panic!("`generic` is known to be the `ChainSpecific` variant; qed"),
					}
				)
			}
		};

		if self.message_hashes.contains(&hash) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			return None;
		}

		match (protocol.client().info(), protocol.client().header(&BlockId::Hash(parent))) {
			(_, Err(e)) | (Err(e), _) => {
				debug!(target:"gossip", "Error reading blockchain: {:?}", e);
				return None;
			},
			(Ok(info), Ok(Some(header))) => {
				if header.number() < &info.chain.best_number {
					trace!(target:"gossip", "Ignored ancient message from {}, hash={}", who, parent);
					return None;
				}
			},
			(Ok(_), Ok(None)) => {},
		}

		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			peer.known_messages.insert(hash);
			if let Some((sink, parent_hash)) = self.message_sink.take() {
				if parent == parent_hash {
					debug!(target: "gossip", "Pushing relevant consensus message to sink.");
					if let Err(e) = sink.unbounded_send(message.clone()) {
						trace!(target:"gossip", "Error broadcasting message notification: {:?}", e);
					}
				}

				self.message_sink = Some((sink, parent_hash));
			}
		} else {
			trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
			return None;
		}

		Some((hash, message))
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

		consensus.collect_garbage(Some(&H256::default()));
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// header that matches one of the messages
		header.parent_hash = prev_hash;
		consensus.collect_garbage(Some(&prev_hash));
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
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::new();

		let bft_message = generic::BftMessage::Consensus(generic::SignedConsensusMessage::Vote(generic::SignedConsensusVote {
			vote: generic::ConsensusVote::AdvanceRound(0),
			sender: [0; 32].into(),
			signature: Default::default(),
		}));

		let parent_hash = [1; 32].into();

		let localized = ::message::LocalizedBftMessage::<Block> {
			message: bft_message,
			parent_hash: parent_hash,
		};

		let message = generic::Message::BftMessage(localized.clone());
		let message_hash = ::protocol::hash_message::<Block>(&message);

		let message = ConsensusMessage::Bft(localized);
		consensus.register_message(message_hash, message.clone());
		let stream = consensus.messages_for(parent_hash);

		assert_eq!(stream.wait().next(), Some(Ok(message)));
	}
}
