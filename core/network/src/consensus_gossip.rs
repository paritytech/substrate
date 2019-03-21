// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use log::{trace, debug};
use futures::sync::mpsc;
use lru_cache::LruCache;
use network_libp2p::{Severity, NodeIndex};
use runtime_primitives::traits::{Block as BlockT, Hash, HashFor};
pub use crate::message::generic::{Message, ConsensusMessage};
use crate::protocol::Context;
use crate::config::Roles;
use crate::ConsensusEngineId;

// FIXME: Add additional spam/DoS attack protection: https://github.com/paritytech/substrate/issues/1115
const KNOWN_MESSAGES_CACHE_SIZE: usize = 4096;

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
}

struct MessageEntry<B: BlockT> {
	topic: B::Hash,
	message: ConsensusMessage,
}

/// Consensus message destination.
pub enum MessageRecipient {
	/// Send to all peers.
	BroadcastToAll,
	/// Send to peers that don't have that message already.
	BroadcastNew,
	/// Send to specific peer.
	Peer(NodeIndex),
}

/// Message validation result.
pub enum ValidationResult<H> {
	/// Message is valid with this topic and should be stored for repropagation.
	ValidStored(H),
	/// Message is valid and should not be tracked.
	ValidOneHop,
	/// Invalid message.
	Invalid,
	/// Obsolete message.
	Expired,
}

/// Validation context. Allows reacting to incoming messages by sending out furter messages.
pub struct ValidatorContext<'g, 'p, B: BlockT> {
	gossip: &'g mut ConsensusGossip<B>,
	protocol: &'p mut Context<B>,
	engine_id: ConsensusEngineId,
}

impl<'g, 'p, B: BlockT> ValidatorContext<'g, 'p, B> {
	/// Broadcast all messages with given topic to peers that do not have it yet.
	pub fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
	   let messages: Vec<_> = self.gossip.messages.iter()
		   .filter_map(|entry| if entry.topic == topic { Some(entry.message.clone()) } else { None })
		   .collect();
		for m in messages {
		   self.gossip.multicast(self.protocol, topic, m, force);
		}
	}

	/// Broadcast a message to all peers that have not received it previously.
	pub fn broadcast_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool) {
		self.gossip.multicast(
			self.protocol,
			topic,
			ConsensusMessage{ data: message, engine_id: self.engine_id.clone() },
			force,
		);
	}

	/// Send addressed message to a peer.
	pub fn send_message(&mut self, who: NodeIndex, message: Vec<u8>) {
		self.protocol.send_message(who, Message::Consensus(ConsensusMessage {
			engine_id: self.engine_id,
			data: message,
		}));
	}
}

/// Validates consensus messages.
pub trait Validator<B: BlockT> {
	/// New peer is connected.
	fn new_peer(&self, _context: &mut ValidatorContext<B>, _who: NodeIndex, _roles: Roles) {
	}

	/// New connection is dropped.
	fn peer_disconnected(&self, _context: &mut ValidatorContext<B>, _who: NodeIndex) {
	}

	/// Validate consensus message.
	fn validate(&self, context: &mut ValidatorContext<B>, who: NodeIndex, data: &[u8]) -> ValidationResult<B::Hash>;

	/// Filter out departing messages.
	fn should_send_to(&self, _who: NodeIndex, _topic: &B::Hash, _data: &[u8]) -> bool {
		true
	}

	/// Produce a closure for validating messages on a given topic.
	fn message_expired<'a>(&'a self) -> Box<FnMut(B::Hash, &[u8]) -> bool + 'a> {
		Box::new(move |_topic, _data| false )
	}
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<(ConsensusEngineId, B::Hash), Vec<mpsc::UnboundedSender<Vec<u8>>>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: LruCache<B::Hash, ()>,
	validators: HashMap<ConsensusEngineId, Arc<Validator<B>>>,
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
	pub fn register_validator(&mut self, engine_id: ConsensusEngineId, validator: Arc<Validator<B>>) {
		self.validators.insert(engine_id, validator);
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut Context<B>, who: NodeIndex, roles: Roles) {
		trace!(target:"gossip", "Registering {:?} {}", roles, who);
		self.peers.insert(who, PeerConsensus {
			known_messages: HashSet::new(),
		});
		for (engine_id, v) in self.validators.clone() {
			let mut context = ValidatorContext { gossip: self, protocol, engine_id: engine_id.clone() };
			v.new_peer(&mut context, who, roles);
		}
	}

	fn propagate<F>(
		&mut self,
		protocol: &mut Context<B>,
		message_hash: B::Hash,
		topic: B::Hash,
		get_message: F,
		force: bool,
	)
		where F: Fn() -> ConsensusMessage,
	{
		for (id, ref mut peer) in self.peers.iter_mut() {
			if !force && peer.known_messages.contains(&message_hash) {
				continue
			}
			let message = get_message();
			if let Some(validator) = self.validators.get(&message.engine_id) {
				if !validator.should_send_to(*id, &topic, &message.data) {
					continue
				}
			}
			peer.known_messages.insert(message_hash.clone());
			trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
			protocol.send_message(*id, Message::Consensus(message));
		}
	}

	fn register_message<F>(
		&mut self,
		message_hash: B::Hash,
		topic: B::Hash,
		get_message: F,
	)
		where F: Fn() -> ConsensusMessage
	{
		if self.known_messages.insert(message_hash, ()).is_none() {
			self.messages.push(MessageEntry {
				topic,
				message: get_message(),
			});
		}
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, protocol: &mut Context<B>, who: NodeIndex) {
		for (engine_id, v) in self.validators.clone() {
			let mut context = ValidatorContext { gossip: self, protocol, engine_id: engine_id.clone() };
			v.peer_disconnected(&mut context, who);
		}
		self.peers.remove(&who);
	}

	/// Prune old or no longer relevant consensus messages. Provide a predicate
	/// for pruning, which returns `false` when the items with a given topic should be pruned.
	pub fn collect_garbage(&mut self) {
		use std::collections::hash_map::Entry;

		self.live_message_sinks.retain(|_, sinks| {
			sinks.retain(|sink| !sink.is_closed());
			!sinks.is_empty()
		});

		let known_messages = &mut self.known_messages;
		let before = self.messages.len();
		let validators = &self.validators;

		let mut check_fns = HashMap::new();
		let mut message_expired = move |entry: &MessageEntry<B>| {
			let engine_id = entry.message.engine_id;
			let check_fn = match check_fns.entry(engine_id) {
				Entry::Occupied(entry) => entry.into_mut(),
				Entry::Vacant(vacant) => match validators.get(&engine_id) {
					None => return true, // treat all messages with no validator as expired
					Some(validator) => vacant.insert(validator.message_expired()),
				}
			};

			(check_fn)(entry.topic, &entry.message.data)
		};

		self.messages.retain(|entry| !message_expired(entry));

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
	pub fn messages_for(&mut self, engine_id: ConsensusEngineId, topic: B::Hash)
		-> mpsc::UnboundedReceiver<Vec<u8>>
	{
		let (tx, rx) = mpsc::unbounded();
		for entry in self.messages.iter_mut()
			.filter(|e| e.topic == topic && e.message.engine_id == engine_id)
		{
			tx.unbounded_send(entry.message.data.clone())
				.expect("receiver known to be live; qed");
		}

		self.live_message_sinks.entry((engine_id, topic)).or_default().push(tx);

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
	) -> Option<(B::Hash, ConsensusMessage)> {
		let message_hash = HashFor::<B>::hash(&message.data[..]);

		if self.known_messages.contains_key(&message_hash) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			return None;
		}

		let engine_id = message.engine_id;
		//validate the message
		let validation = self.validators.get(&engine_id)
			.cloned()
			.map(|v| {
				let mut context = ValidatorContext { gossip: self, protocol, engine_id };
				v.validate(&mut context, who, &message.data)
			});
		let topic = match validation {
			Some(ValidationResult::ValidStored(topic)) => Some(topic),
			Some(ValidationResult::ValidOneHop) => None,
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
				return None;
			}
			None => {
				protocol.report_peer(
					who,
					Severity::Useless(format!("Sent unknown consensus engine id")),
				);
				trace!(target:"gossip", "Unknown message engine id {:?} from {}",
					engine_id, who);
				return None;
			}
		};

		if let Some(topic) = topic {
			if let Some(ref mut peer) = self.peers.get_mut(&who) {
				use std::collections::hash_map::Entry;
				peer.known_messages.insert(message_hash);
				if let Entry::Occupied(mut entry) = self.live_message_sinks.entry((engine_id, topic)) {
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
				Some((topic, message))
			} else {
				trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
				None
			}
		} else {
			trace!(target:"gossip", "Handled valid one hop message from peer {}", who);
			None
		}
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		protocol: &mut Context<B>,
		topic: B::Hash,
		message: ConsensusMessage,
		force: bool,
	) {
		let message_hash = HashFor::<B>::hash(&message.data);
		self.multicast_inner(protocol, message_hash, topic, || message.clone(), force);
	}

	fn multicast_inner<F>(
		&mut self,
		protocol: &mut Context<B>,
		message_hash: B::Hash,
		topic: B::Hash,
		get_message: F,
		force: bool,
	)
		where F: Fn() -> ConsensusMessage
	{
		self.register_message(message_hash, topic, &get_message);
		self.propagate(protocol, message_hash, topic, get_message, force);
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use futures::Stream;

	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	macro_rules! push_msg {
		($consensus:expr, $topic:expr, $hash: expr, $m:expr) => {
			if $consensus.known_messages.insert($hash, ()).is_none() {
				$consensus.messages.push(MessageEntry {
					topic: $topic,
					message: ConsensusMessage { data: $m, engine_id: [0, 0, 0, 0]},
				});
			}
		}
	}

	struct AllowAll;
	impl Validator<Block> for AllowAll {
		fn validate(&self, _context: &mut ValidatorContext<Block>, _data: &[u8]) -> ValidationResult<H256> {
			ValidationResult::ValidStored(H256::default())
		}
	}

	#[test]
	fn collects_garbage() {
		struct AllowOne;
		impl Validator<Block> for AllowOne {
			fn validate(&self, _context: &mut ValidatorContext<Block>, data: &[u8]) -> ValidationResult<H256> {
				if data[0] == 1 {
					ValidationResult::ValidStored(H256::default())
				} else {
					ValidationResult::Expired
				}
			}

			fn message_expired<'a>(&'a self) -> Box<FnMut(H256, &[u8]) -> bool + 'a> {
				Box::new(move |_topic, data| data[0] != 1 )
			}
		}

		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = ConsensusGossip::<Block>::new();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = vec![1, 2, 3];
		let m2 = vec![4, 5, 6];

		push_msg!(consensus, prev_hash, m1_hash, m1);
		push_msg!(consensus, best_hash, m2_hash, m2.clone());
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
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator([0, 0, 0, 0], Arc::new(AllowAll));

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		let message_hash = HashFor::<Block>::hash(&message.data);
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(message_hash, topic, || message.clone());
		let stream = consensus.messages_for([0, 0, 0, 0], topic);

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
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator([0, 0, 0, 0], Arc::new(AllowAll));

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		let message_hash = HashFor::<Block>::hash(&message.data);
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(message_hash, topic, || message.clone());

		let stream1 = consensus.messages_for([0, 0, 0, 0], topic);
		let stream2 = consensus.messages_for([0, 0, 0, 0], topic);

		assert_eq!(stream1.wait().next(), Some(Ok(message.data.clone())));
		assert_eq!(stream2.wait().next(), Some(Ok(message.data)));
	}

	#[test]
	fn topics_are_localized_to_engine_id() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator([0, 0, 0, 0], Arc::new(AllowAll));

		let topic = [1; 32].into();
		let msg_a = ConsensusMessage { data: vec![1, 2, 3], engine_id: [0, 0, 0, 0] };
		let msg_b = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 1] };

		consensus.register_message(HashFor::<Block>::hash(&msg_a.data), topic, || msg_a.clone());
		consensus.register_message(HashFor::<Block>::hash(&msg_b.data), topic, || msg_b.clone());

		let mut stream = consensus.messages_for([0, 0, 0, 0], topic).wait();

		assert_eq!(stream.next(), Some(Ok(vec![1, 2, 3])));
		let _ = consensus.live_message_sinks.remove(&([0, 0, 0, 0], topic));
		assert_eq!(stream.next(), None);
	}
}
