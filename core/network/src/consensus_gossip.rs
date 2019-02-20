// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
use std::sync::Arc;
use std::time::{Instant, Duration};
use log::{trace, debug};
use futures::sync::mpsc;
use rand::{self, seq::SliceRandom};
use lru_cache::LruCache;
use network_libp2p::{Severity, NodeIndex};
use runtime_primitives::traits::{Block as BlockT, Hash, HashFor};
pub use crate::message::generic::{Message, ConsensusMessage};
use crate::protocol::Context;
use crate::config::Roles;
use crate::ConsensusEngineId;

// FIXME: Add additional spam/DoS attack protection: https://github.com/paritytech/substrate/issues/1115
const MESSAGE_LIFETIME: Duration = Duration::from_secs(120);
const KNOWN_MESSAGES_CACHE_SIZE: usize = 4096;

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
	is_authority: bool,
}

struct MessageEntry<B: BlockT> {
	message_hash: B::Hash,
	topic: B::Hash,
	message: ConsensusMessage,
	timestamp: Instant,
}

/// Message validation result.
pub enum ValidationResult<H> {
	/// Message is valid with this topic.
	Valid(H),
	/// Invalid message.
	Invalid,
	/// Obsolete message.
	Expired,
}

/// Validates consensus messages.
pub trait Validator<H> {
	/// Validate consensus message.
	fn validate(&self, data: &[u8]) -> ValidationResult<H>;
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<B::Hash, Vec<mpsc::UnboundedSender<Vec<u8>>>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: LruCache<B::Hash, ()>,
	validators: HashMap<ConsensusEngineId, Arc<Validator<B::Hash>>>,
}

impl<B: BlockT> ConsensusGossip<B> {
	/// Create a new instance.
	pub fn new() -> Self {
		ConsensusGossip {
			peers: HashMap::new(),
			live_message_sinks: HashMap::new(),
			messages: Default::default(),
			known_messages: LruCache::new(KNOWN_MESSAGES_CACHE_SIZE),
			validators: Default::default(),
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.live_message_sinks.clear();
	}

	/// Register message validator for a message type.
	pub fn register_validator(&mut self, engine_id: ConsensusEngineId, validator: Arc<Validator<B::Hash>>) {
		self.validators.insert(engine_id, validator);
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, who: NodeIndex, roles: Roles) {
		if roles.intersects(Roles::AUTHORITY) {
			trace!(target:"gossip", "Registering {:?} {}", roles, who);
			let now = Instant::now();
			// Send out all known messages to authorities.
			let mut known_messages = HashSet::new();
			for entry in self.messages.iter() {
				if entry.timestamp + MESSAGE_LIFETIME < now { continue };
				known_messages.insert(entry.message_hash);
				protocol.send_message(who, Message::Consensus(entry.message.clone()));
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

	fn propagate<F>(
		&mut self,
		protocol: &mut Context<B>,
		message_hash: B::Hash,
		get_message: F,
	)
		where F: Fn() -> ConsensusMessage,
	{
		let mut non_authorities: Vec<_> = self.peers.iter()
			.filter_map(|(id, ref peer)|
				if !peer.is_authority && !peer.known_messages.contains(&message_hash) {
					Some(*id)
				} else {
					None
				}
			)
			.collect();

		non_authorities.shuffle(&mut rand::thread_rng());
		let non_authorities: HashSet<_> = if non_authorities.is_empty() {
			HashSet::new()
		} else {
			non_authorities[0..non_authorities.len().min(((non_authorities.len() as f64).sqrt() as usize).max(3))].iter().collect()
		};

		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.is_authority {
				if peer.known_messages.insert(message_hash.clone()) {
					let message = get_message();
					trace!(target:"gossip", "Propagating to authority {}: {:?}", id, message);
					protocol.send_message(*id, Message::Consensus(message));
				}
			} else if non_authorities.contains(&id) {
				if peer.known_messages.insert(message_hash.clone()) {
					let message = get_message();
					trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
					protocol.send_message(*id, Message::Consensus(message));
				}
			}
		}
	}

	fn register_message<F>(&mut self, message_hash: B::Hash, topic: B::Hash, get_message: F)
		where F: Fn() -> ConsensusMessage
	{
		if self.known_messages.insert(message_hash, ()).is_none()
		{
			self.messages.push(MessageEntry {
				topic,
				message_hash,
				message: get_message(),
				timestamp: Instant::now(),
			});

		}
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, _protocol: &mut Context<B>, who: NodeIndex) {
		self.peers.remove(&who);
	}

	/// Prune old or no longer relevant consensus messages. Provide a predicate
	/// for pruning, which returns `false` when the items with a given topic should be pruned.
	pub fn collect_garbage(&mut self) {
		self.live_message_sinks.retain(|_, sinks| {
			sinks.retain(|sink| !sink.is_closed());
			!sinks.is_empty()
		});

		let known_messages = &mut self.known_messages;
		let before = self.messages.len();
		let validators = &self.validators;
		let now = Instant::now();

		self.messages.retain(|entry| {
			entry.timestamp + MESSAGE_LIFETIME >= now
			&& match validators.get(&entry.message.engine_id)
				.map(|v| v.validate(&entry.message.data))
			{
				Some(ValidationResult::Valid(_)) => true,
				_ => false,
			}
		});

		trace!(target: "gossip", "Cleaned up {} stale messages, {} left ({} known)",
			before - self.messages.len(),
			self.messages.len(),
			known_messages.len(),
		);

		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| known_messages.contains_key(h));
		}
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile)
	pub fn messages_for(&mut self, topic: B::Hash) -> mpsc::UnboundedReceiver<Vec<u8>> {
		let (tx, rx) = mpsc::unbounded();
		for entry in self.messages.iter().filter(|e| e.topic == topic) {
			tx.unbounded_send(entry.message.data.clone()).expect("receiver known to be live; qed");
		}
		self.live_message_sinks.entry(topic).or_default().push(tx);

		rx
	}

	/// Handle an incoming ConsensusMessage for topic by who via protocol. Discard message if topic
	/// already known, the message is old, its source peers isn't a registered peer or the connection
	/// to them is broken. Return `Some(topic, message)` if it was added to the internal queue, `None`
	/// in all other cases.
	pub fn on_incoming(
		&mut self,
		protocol: &mut Context<B>,
		who: NodeIndex,
		message: ConsensusMessage,
		is_syncing: bool,
	) -> Option<(B::Hash, ConsensusMessage)> {
		let message_hash = HashFor::<B>::hash(&message.data[..]);

		if self.known_messages.contains_key(&message_hash) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			return None;
		}

		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			use std::collections::hash_map::Entry;

			//validate the message
			let topic = match self.validators.get(&message.engine_id)
				.map(|v| v.validate(&message.data))
			{
				Some(ValidationResult::Valid(topic)) => topic,
				Some(ValidationResult::Invalid) => {
					trace!(target:"gossip", "Invalid message from {}", who);
					protocol.report_peer(
						who,
						Severity::Bad(format!("Sent invalid consensus message")),
					);
					return None;
				},
				Some(ValidationResult::Expired) => {
					trace!(target:"gossip", "Ignored expired message from {}", who);
					if !is_syncing {
						protocol.report_peer(
							who,
							Severity::Useless(format!("Sent expired consensus message")),
						);
					}
					return None;
				}
				None => {
					protocol.report_peer(
						who,
						Severity::Useless(format!("Sent unknown consensus engine id")),
					);
					trace!(target:"gossip", "Unknown message engine id {:?} from {}", message.engine_id, who);
					return None;
				}
			};

			peer.known_messages.insert(message_hash);
			if let Entry::Occupied(mut entry) = self.live_message_sinks.entry(topic) {
				debug!(target: "gossip", "Pushing consensus message to sinks for {}.", topic);
				entry.get_mut().retain(|sink| {
					if let Err(e) = sink.unbounded_send(message.data.clone()) {
						trace!(target:"gossip", "Error broadcasting message notification: {:?}", e);
					}
					!sink.is_closed()
				});
				if entry.get().is_empty() {
					entry.remove_entry();
				}
			}
			self.multicast_inner(protocol, message_hash, topic, || message.clone());
			Some((topic, message))
		} else {
			trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
			None
		}
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		protocol: &mut Context<B>,
		topic: B::Hash,
		message: ConsensusMessage,
	) {
		let message_hash = HashFor::<B>::hash(&message.data);
		self.multicast_inner(protocol, message_hash, topic, || message.clone());
	}

	fn multicast_inner<F>(
		&mut self,
		protocol: &mut Context<B>,
		message_hash: B::Hash,
		topic: B::Hash,
		get_message: F,
	)
		where F: Fn() -> ConsensusMessage
	{
		self.register_message(message_hash, topic, &get_message);
		self.propagate(protocol, message_hash, get_message);
	}

	/// Note new consensus session.
	pub fn new_session(&mut self, _parent_hash: B::Hash) {
		self.collect_garbage();
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use std::time::Instant;
	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	macro_rules! push_msg {
		($consensus:expr, $topic:expr, $hash: expr, $now: expr, $m:expr) => {
			if $consensus.known_messages.insert($hash, ()).is_none() {
				$consensus.messages.push(MessageEntry {
					topic: $topic,
					message_hash: $hash,
					message: ConsensusMessage { data: $m, engine_id: [0, 0, 0, 0]},
					timestamp: $now,
				});
			}
		}
	}

	#[test]
	fn collects_garbage() {

		struct AllowAll;
		impl Validator<H256> for AllowAll {
			fn validate(&self, _data: &[u8]) -> ValidationResult<H256> {
				ValidationResult::Valid(H256::default())
			}
		}

		struct AllowOne;
		impl Validator<H256> for AllowOne {
			fn validate(&self, data: &[u8]) -> ValidationResult<H256> {
				if data[0] == 1 {
					ValidationResult::Valid(H256::default())
				} else {
					ValidationResult::Expired
				}
			}
		}

		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = ConsensusGossip::<Block>::new();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = vec![1, 2, 3];
		let m2 = vec![4, 5, 6];

		let now = Instant::now();
		push_msg!(consensus, prev_hash, m1_hash, now, m1);
		push_msg!(consensus, best_hash, m2_hash, now, m2.clone());
		consensus.known_messages.insert(m1_hash, ());
		consensus.known_messages.insert(m2_hash, ());

		let test_engine_id = Default::default();
		consensus.register_validator(test_engine_id, Arc::new(AllowAll));
		consensus.collect_garbage();
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.known_messages.len(), 2);

		consensus.register_validator(test_engine_id, Arc::new(AllowOne));

		// m2 is expired
		consensus.collect_garbage();
		assert_eq!(consensus.messages.len(), 1);
		// known messages are only pruned based on size.
		assert_eq!(consensus.known_messages.len(), 2);
		assert!(consensus.known_messages.contains_key(&m2_hash));

		// make timestamp expired, but the message is still kept as known
		consensus.messages.clear();
		consensus.known_messages.clear();
		consensus.register_validator(test_engine_id, Arc::new(AllowAll));
		push_msg!(consensus, best_hash, m2_hash, now - MESSAGE_LIFETIME, m2.clone());
		consensus.collect_garbage();
		assert!(consensus.messages.is_empty());
		assert_eq!(consensus.known_messages.len(), 1);
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::<Block>::new();

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		let message_hash = HashFor::<Block>::hash(&message.data);
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(message_hash, topic, || message.clone());
		let stream = consensus.messages_for(topic);

		assert_eq!(stream.wait().next(), Some(Ok(message.data)));
	}

	#[test]
	fn can_keep_multiple_messages_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();

		let topic = [1; 32].into();
		let msg_a = ConsensusMessage { data: vec![1, 2, 3], engine_id: [0, 0, 0, 0] };
		let msg_b = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		consensus.register_message(HashFor::<Block>::hash(&msg_a.data), topic, || msg_a.clone());
		consensus.register_message(HashFor::<Block>::hash(&msg_b.data), topic, || msg_b.clone());

		assert_eq!(consensus.messages.len(), 2);
	}

	#[test]
	fn can_keep_multiple_subscribers_per_topic() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::<Block>::new();

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		let message_hash = HashFor::<Block>::hash(&message.data);
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(message_hash, topic, || message.clone());

		let stream1 = consensus.messages_for(topic);
		let stream2 = consensus.messages_for(topic);

		assert_eq!(stream1.wait().next(), Some(Ok(message.data.clone())));
		assert_eq!(stream2.wait().next(), Some(Ok(message.data)));
	}
}
