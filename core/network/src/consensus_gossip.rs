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
use rand::{self, Rng};
use network_libp2p::NodeIndex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use message::generic::{Message, ConsensusMessage};
use protocol::Context;
use service::Roles;

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
	is_authority: bool,
}

struct MessageEntry<B: BlockT> {
	topic: B::Hash,
	message: ConsensusMessage,
	instant: Instant,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<B::Hash, mpsc::UnboundedSender<ConsensusMessage>>,
	messages: Vec<MessageEntry<B>>,
	message_hashes: HashSet<B::Hash>,
}

impl<B: BlockT> ConsensusGossip<B>
where
	B::Header: HeaderT<Number=u64>
{
	/// Create a new instance.
	pub fn new() -> Self {
		ConsensusGossip {
			peers: HashMap::new(),
			live_message_sinks: HashMap::new(),
			messages: Default::default(),
			message_hashes: Default::default(),
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.live_message_sinks.clear();
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, who: NodeIndex, roles: Roles) {
		if roles.intersects(Roles::AUTHORITY) {
			trace!(target:"gossip", "Registering {:?} {}", roles, who);
			// Send out all known messages to authorities.
			// TODO: limit by size
			let mut known_messages = HashSet::new();
			for entry in self.messages.iter() {
				known_messages.insert(entry.topic);
				protocol.send_message(who, Message::Consensus(entry.topic.clone(), entry.message.clone()));
			}
			self.peers.insert(who, PeerConsensus {
				known_messages,
				is_authority: true,
			});
		}
		else if roles.intersects(Roles::FULL) {
			self.peers.insert(who, PeerConsensus {
				known_messages: HashSet::new(),
				is_authority: false,
			});
		}
	}

	fn propagate(&mut self, protocol: &mut Context<B>, topic: B::Hash, message: ConsensusMessage) {
		let mut non_authorities: Vec<_> = self.peers.iter()
			.filter_map(|(id, ref peer)| if !peer.is_authority && !peer.known_messages.contains(&topic) { Some(*id) } else { None })
			.collect();

		rand::thread_rng().shuffle(&mut non_authorities);
		let non_authorities: HashSet<_> = if non_authorities.is_empty() {
			HashSet::new()
		} else {
			non_authorities[0..non_authorities.len().min(((non_authorities.len() as f64).sqrt() as usize).max(3))].iter().collect()
		};

		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.is_authority {
				if peer.known_messages.insert(topic.clone()) {
					trace!(target:"gossip", "Propagating to authority {}: {:?}", id, message);
					protocol.send_message(*id, Message::Consensus(topic, message.clone()));
				}
			}
			else if non_authorities.contains(&id) {
				trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
				peer.known_messages.insert(topic.clone());
				protocol.send_message(*id, Message::Consensus(topic, message.clone()));
			}
		}
	}

	fn register_message(&mut self, topic: B::Hash, message: ConsensusMessage) {
		if self.message_hashes.insert(topic) {
			self.messages.push(MessageEntry {
				topic,
				instant: Instant::now(),
				message,
			});
		}
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, _protocol: &mut Context<B>, who: NodeIndex) {
		self.peers.remove(&who);
	}

	/// Prune old or no longer relevant consensus messages. Provide a predicate
	/// for pruning, which returns `false` when the items with a given topic should be pruned.
	pub fn collect_garbage<P: Fn(&B::Hash) -> bool>(&mut self, predicate: P) {
		self.live_message_sinks.retain(|_, sink| !sink.is_closed());

		let hashes = &mut self.message_hashes;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|entry| {
			if entry.instant + MESSAGE_LIFETIME >= now && predicate(&entry.topic) {
				true
			} else {
				hashes.remove(&entry.topic);
				false
			}
		});
		trace!(target:"gossip", "Cleaned up {} stale messages, {} left", before - self.messages.len(), self.messages.len());
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}

	/// Handle an incoming ConsensusMessage for topic by who via protocol. Discard message if topic
	/// already known, the message is old, its source peers isn't a registered peer or the connection
	/// to them is broken. Return `Some(topic, message)` if it was added to the internal queue, `None`
	/// in all other cases.
	pub fn on_incoming(
		&mut self,
		protocol: &mut Context<B>,
		who: NodeIndex,
		topic: B::Hash,
		message: ConsensusMessage,
	) -> Option<(B::Hash, ConsensusMessage)> {

		if self.message_hashes.contains(&topic) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			return None;
		}

		match (protocol.client().info(), protocol.client().header(&BlockId::Hash(topic))) {
			(_, Err(e)) | (Err(e), _) => {
				debug!(target:"gossip", "Error reading blockchain: {:?}", e);
				return None;
			},
			(Ok(info), Ok(Some(header))) => {
				if header.number() < &info.chain.best_number {
					trace!(target:"gossip", "Ignored ancient message from {}, hash={}", who, topic);
					return None;
				}
			},
			(Ok(_), Ok(None)) => {},
		}


		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			use std::collections::hash_map::Entry;
			peer.known_messages.insert(hash);
			if let Entry::Occupied(mut entry) = self.live_message_sinks.entry(topic) {
				debug!(target: "gossip", "Pushing relevant consensus message to sink.");
				if let Err(e) = entry.get().unbounded_send(message.clone()) {
					trace!(target:"gossip", "Error broadcasting message notification: {:?}", e);
				}

				if entry.get().is_closed() {
					entry.remove_entry();
				}
			}
		} else {
			trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
			return None;
		}

		Some((topic, message))
	}

	fn multicast(&mut self, protocol: &mut Context<B>, topic: B::Hash, message: ConsensusMessage) {
		self.register_message(topic, message.clone());
		self.propagate(protocol, topic, message);
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
		let m1 = Message::Bft(message::LocalizedBftMessage {
			parent_topic: prev_hash,
			message: message::generic::BftMessage::Auxiliary(Justification {
				round_number: 0,
				topic: Default::default(),
				signatures: Default::default(),
			}),
		});
		let m2 = Message::ChainSpecific(vec![1, 2, 3], best_hash);

		macro_rules! push_msg {
			($topic:expr, $now: expr, $m:expr) => {
				consensus.messages.push(MessageEntry {
					topic: $hash,
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
		consensus.collect_garbage(|_topic| true);
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

		consensus.collect_garbage(|&topic| topic != Default::default());
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.message_hashes.len(), 2);

		// header that matches one of the messages
		header.parent_hash = prev_hash;
		consensus.collect_garbage(|topic| topic != &prev_hash);
		assert_eq!(consensus.messages.len(), 1);
		assert_eq!(consensus.message_hashes.len(), 1);
		assert!(consensus.message_hashes.contains(&m2_hash));

		// make timestamp expired
		consensus.messages.clear();
		push_msg!(m2_hash, now - MESSAGE_LIFETIME, m2);
		consensus.collect_garbage(|_topic| true);
		assert!(consensus.messages.is_empty());
		assert!(consensus.message_hashes.is_empty());
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::new();

		let bft_message = generic::BftMessage::Consensus(generic::SignedMessage::Vote(generic::SignedConsensusVote {
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

		let message = Message::Bft(localized);
		consensus.register_message(message_hash, message.clone());
		let stream = consensus.messages_for(parent_hash);

		assert_eq!(stream.wait().next(), Some(Ok(message)));
	}
}
