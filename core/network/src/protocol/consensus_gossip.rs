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

use std::collections::{HashMap, HashSet, hash_map::Entry};
use std::sync::Arc;
use std::iter;
use std::time;
use log::{trace, debug};
use futures::sync::mpsc;
use lru_cache::LruCache;
use network_libp2p::PeerId;
use runtime_primitives::traits::{Block as BlockT, Hash, HashFor};
use runtime_primitives::ConsensusEngineId;
pub use crate::message::generic::{Message, ConsensusMessage};
use crate::protocol::Context;
use crate::config::Roles;

// FIXME: Add additional spam/DoS attack protection: https://github.com/paritytech/substrate/issues/1115
const KNOWN_MESSAGES_CACHE_SIZE: usize = 4096;

const REBROADCAST_INTERVAL: time::Duration = time::Duration::from_secs(30);
/// Reputation change when a peer sends us a gossip message that we didn't know about.
const GOSSIP_SUCCESS_REPUTATION_CHANGE: i32 = 1 << 4;
/// Reputation change when a peer sends us a gossip message that we already knew about.
const DUPLICATE_GOSSIP_REPUTATION_CHANGE: i32 = -(1 << 2);
/// Reputation change when a peer sends us a gossip message for an unknown engine, whatever that
/// means.
const UNKNOWN_GOSSIP_REPUTATION_CHANGE: i32 = -(1 << 6);
/// Reputation change when a peer sends a message from a topic it isn't registered on.
const UNREGISTERED_TOPIC_REPUTATION_CHANGE: i32 = -(1 << 10);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
	roles: Roles,
}

/// Topic stream message with sender.
#[derive(Debug, Eq, PartialEq)]
pub struct TopicNotification {
	/// Message data.
	pub message: Vec<u8>,
	/// Sender if available.
	pub sender: Option<PeerId>,
}

struct MessageEntry<B: BlockT> {
	message_hash: B::Hash,
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
	Peer(PeerId),
}

/// The reason for sending out the message.
#[derive(Eq, PartialEq, Copy, Clone)]
pub enum MessageIntent {
	/// Requested broadcast
	Broadcast,
	/// Requested broadcast to all peers.
	ForcedBroadcast,
	/// Periodic rebroadcast of all messages to all peers.
	PeriodicRebroadcast,
}

/// Message validation result.
pub enum ValidationResult<H> {
	/// Message should be stored and propagated under given topic.
	ProcessAndKeep(H),
	/// Message should be processed, but not propagated.
	ProcessAndDiscard(H),
	/// Message should be ignored.
	Discard,
}

/// Validation context. Allows reacting to incoming messages by sending out further messages.
pub trait ValidatorContext<B: BlockT> {
	/// Broadcast all messages with given topic to peers that do not have it yet.
	fn broadcast_topic(&mut self, topic: B::Hash, force: bool);
	/// Broadcast a message to all peers that have not received it previously.
	fn broadcast_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool);
	/// Send addressed message to a peer.
	fn send_message(&mut self, who: &PeerId, message: Vec<u8>);
	/// Send all messages with given topic to a peer.
	fn send_topic(&mut self, who: &PeerId, topic: B::Hash, force: bool);
}

struct NetworkContext<'g, 'p, B: BlockT> {
	gossip: &'g mut ConsensusGossip<B>,
	protocol: &'p mut dyn Context<B>,
	engine_id: ConsensusEngineId,
}

impl<'g, 'p, B: BlockT> ValidatorContext<B> for NetworkContext<'g, 'p, B> {
	/// Broadcast all messages with given topic to peers that do not have it yet.
	fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.gossip.broadcast_topic(self.protocol, topic, force);
	}

	/// Broadcast a message to all peers that have not received it previously.
	fn broadcast_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool) {
		self.gossip.multicast(
			self.protocol,
			topic,
			ConsensusMessage{ data: message, engine_id: self.engine_id.clone() },
			force,
		);
	}

	/// Send addressed message to a peer.
	fn send_message(&mut self, who: &PeerId, message: Vec<u8>) {
		self.protocol.send_consensus(who.clone(), ConsensusMessage {
			engine_id: self.engine_id,
			data: message,
		});
	}

	/// Send all messages with given topic to a peer.
	fn send_topic(&mut self, who: &PeerId, topic: B::Hash, force: bool) {
		self.gossip.send_topic(self.protocol, who, topic, self.engine_id, force);
	}
}

fn propagate<'a, B: BlockT, I>(
	protocol: &mut dyn Context<B>,
	messages: I,
	intent: MessageIntent,
	peers: &mut HashMap<PeerId, PeerConsensus<B::Hash>>,
	validators: &HashMap<ConsensusEngineId, Arc<dyn Validator<B>>>,
)
	where I: IntoIterator<Item=(&'a B::Hash, &'a B::Hash, &'a ConsensusMessage)>,  // (msg_hash, topic, message)
{
	let mut check_fns = HashMap::new();
	let mut message_allowed = move |who: &PeerId, intent: MessageIntent, topic: &B::Hash, message: &ConsensusMessage| {
		let engine_id = message.engine_id;
		let check_fn = match check_fns.entry(engine_id) {
			Entry::Occupied(entry) => entry.into_mut(),
			Entry::Vacant(vacant) => match validators.get(&engine_id) {
				None => return false, // treat all messages with no validator as not allowed
				Some(validator) => vacant.insert(validator.message_allowed()),
			}
		};

		(check_fn)(who, intent, topic, &message.data)
	};

	for (message_hash, topic, message) in messages {
		for (id, ref mut peer) in peers.iter_mut() {
			let intent = match intent {
				MessageIntent::Broadcast =>
					if peer.known_messages.contains(&message_hash) {
						continue
					} else {
						MessageIntent::Broadcast
					},
				MessageIntent::PeriodicRebroadcast =>
					if peer.known_messages.contains(&message_hash) {
						MessageIntent::PeriodicRebroadcast
					} else {
						// peer doesn't know message, so the logic should treat it as an
						// initial broadcast.
						MessageIntent::Broadcast
					},
				other => other,
			};

			if !message_allowed(id, intent, &topic, &message) {
				continue
			}
			peer.known_messages.insert(message_hash.clone());
			trace!(target: "gossip", "Propagating to {}: {:?}", id, message);
			protocol.send_consensus(id.clone(), message.clone());
		}
	}
}

/// Validates consensus messages.
pub trait Validator<B: BlockT>: Send + Sync {
	/// New peer is connected.
	fn new_peer(&self, _context: &mut dyn ValidatorContext<B>, _who: &PeerId, _roles: Roles) {
	}

	/// New connection is dropped.
	fn peer_disconnected(&self, _context: &mut dyn ValidatorContext<B>, _who: &PeerId) {
	}

	/// Validate consensus message.
	fn validate(
		&self,
		context: &mut dyn ValidatorContext<B>,
		sender: &PeerId,
		data: &[u8]
	) -> ValidationResult<B::Hash>;

	/// Produce a closure for validating messages on a given topic.
	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		Box::new(move |_topic, _data| false)
	}

	/// Produce a closure for filtering egress messages.
	fn message_allowed<'a>(&'a self) -> Box<dyn FnMut(&PeerId, MessageIntent, &B::Hash, &[u8]) -> bool + 'a> {
		Box::new(move |_who, _intent, _topic, _data| true)
	}
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<PeerId, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<(ConsensusEngineId, B::Hash), Vec<mpsc::UnboundedSender<TopicNotification>>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: LruCache<B::Hash, ()>,
	validators: HashMap<ConsensusEngineId, Arc<dyn Validator<B>>>,
	next_broadcast: time::Instant,
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
			next_broadcast: time::Instant::now() + REBROADCAST_INTERVAL,
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.live_message_sinks.clear();
	}

	/// Register message validator for a message type.
	pub fn register_validator(
		&mut self,
		protocol: &mut dyn Context<B>,
		engine_id: ConsensusEngineId,
		validator: Arc<dyn Validator<B>>
	) {
		self.register_validator_internal(engine_id, validator.clone());
		let peers: Vec<_> = self.peers.iter().map(|(id, peer)| (id.clone(), peer.roles)).collect();
		for (id, roles) in peers {
			let mut context = NetworkContext { gossip: self, protocol, engine_id: engine_id.clone() };
			validator.new_peer(&mut context, &id, roles);
		}
	}

	fn register_validator_internal(&mut self, engine_id: ConsensusEngineId, validator: Arc<dyn Validator<B>>) {
		self.validators.insert(engine_id, validator.clone());
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, protocol: &mut dyn Context<B>, who: PeerId, roles: Roles) {
		// light nodes are not valid targets for consensus gossip messages
		if !roles.is_full() {
			return;
		}

		trace!(target:"gossip", "Registering {:?} {}", roles, who);
		self.peers.insert(who.clone(), PeerConsensus {
			known_messages: HashSet::new(),
			roles,
		});
		for (engine_id, v) in self.validators.clone() {
			let mut context = NetworkContext { gossip: self, protocol, engine_id: engine_id.clone() };
			v.new_peer(&mut context, &who, roles);
		}
	}

	fn register_message_hashed(
		&mut self,
		message_hash: B::Hash,
		topic: B::Hash,
		message: ConsensusMessage,
	) {
		if self.known_messages.insert(message_hash.clone(), ()).is_none() {
			self.messages.push(MessageEntry {
				message_hash,
				topic,
				message,
			});
		}
	}

	/// Registers a message without propagating it to any peers. The message
	/// becomes available to new peers or when the service is asked to gossip
	/// the message's topic. No validation is performed on the message, if the
	/// message is already expired it should be dropped on the next garbage
	/// collection.
	pub fn register_message(
		&mut self,
		topic: B::Hash,
		message: ConsensusMessage,
	) {
		let message_hash = HashFor::<B>::hash(&message.data[..]);
		self.register_message_hashed(message_hash, topic, message);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, protocol: &mut dyn Context<B>, who: PeerId) {
		for (engine_id, v) in self.validators.clone() {
			let mut context = NetworkContext { gossip: self, protocol, engine_id: engine_id.clone() };
			v.peer_disconnected(&mut context, &who);
		}
	}

	/// Perform periodic maintenance
	pub fn tick(&mut self, protocol: &mut dyn Context<B>) {
		self.collect_garbage();
		if time::Instant::now() >= self.next_broadcast {
			self.rebroadcast(protocol);
			self.next_broadcast = time::Instant::now() + REBROADCAST_INTERVAL;
		}
	}

	/// Rebroadcast all messages to all peers.
	fn rebroadcast(&mut self, protocol: &mut dyn Context<B>) {
		let messages = self.messages.iter()
			.map(|entry| (&entry.message_hash, &entry.topic, &entry.message));
		propagate(protocol, messages, MessageIntent::PeriodicRebroadcast, &mut self.peers, &self.validators);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, protocol: &mut dyn Context<B>, topic: B::Hash, force: bool) {
		let messages = self.messages.iter()
			.filter_map(|entry|
				if entry.topic == topic { Some((&entry.message_hash, &entry.topic, &entry.message)) } else { None }
			);
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(protocol, messages, intent, &mut self.peers, &self.validators);
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
		-> mpsc::UnboundedReceiver<TopicNotification>
	{
		let (tx, rx) = mpsc::unbounded();
		for entry in self.messages.iter_mut()
			.filter(|e| e.topic == topic && e.message.engine_id == engine_id)
		{
			tx.unbounded_send(TopicNotification {
					message: entry.message.data.clone(),
					sender: None,
				})
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
		protocol: &mut dyn Context<B>,
		who: PeerId,
		message: ConsensusMessage,
	) {
		let message_hash = HashFor::<B>::hash(&message.data[..]);

		if self.known_messages.contains_key(&message_hash) {
			trace!(target:"gossip", "Ignored already known message from {}", who);
			protocol.report_peer(who.clone(), DUPLICATE_GOSSIP_REPUTATION_CHANGE);
			return;
		}

		let engine_id = message.engine_id;
		//validate the message
		let validation = self.validators.get(&engine_id)
			.cloned()
			.map(|v| {
				let mut context = NetworkContext { gossip: self, protocol, engine_id };
				v.validate(&mut context, &who, &message.data)
			});
		let validation_result = match validation {
			Some(ValidationResult::ProcessAndKeep(topic)) => Some((topic, true)),
			Some(ValidationResult::ProcessAndDiscard(topic)) => Some((topic, false)),
			Some(ValidationResult::Discard) => None,
			None => {
				trace!(target:"gossip", "Unknown message engine id {:?} from {}", engine_id, who);
				protocol.report_peer(who.clone(), UNKNOWN_GOSSIP_REPUTATION_CHANGE);
				protocol.disconnect_peer(who);
				return;
			}
		};

		if let Some((topic, keep)) = validation_result {
			protocol.report_peer(who.clone(), GOSSIP_SUCCESS_REPUTATION_CHANGE);
			if let Some(ref mut peer) = self.peers.get_mut(&who) {
				peer.known_messages.insert(message_hash);
				if let Entry::Occupied(mut entry) = self.live_message_sinks.entry((engine_id, topic)) {
					debug!(target: "gossip", "Pushing consensus message to sinks for {}.", topic);
					entry.get_mut().retain(|sink| {
						if let Err(e) = sink.unbounded_send(TopicNotification {
							message: message.data.clone(),
							sender: Some(who.clone())
						}) {
							trace!(target: "gossip", "Error broadcasting message notification: {:?}", e);
						}
						!sink.is_closed()
					});
					if entry.get().is_empty() {
						entry.remove_entry();
					}
				}
				if keep {
					self.register_message_hashed(message_hash, topic, message);
				}
			} else {
				trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
				protocol.report_peer(who.clone(), UNREGISTERED_TOPIC_REPUTATION_CHANGE);
			}
		} else {
			trace!(target:"gossip", "Handled valid one hop message from peer {}", who);
		}
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&mut self,
		protocol: &mut dyn Context<B>,
		who: &PeerId,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		force: bool
	) {
		let validator = self.validators.get(&engine_id);
		let mut message_allowed = match validator {
			None => return, // treat all messages with no validator as not allowed
			Some(validator) => validator.message_allowed(),
		};

		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };

		if let Some(ref mut peer) = self.peers.get_mut(who) {
			for entry in self.messages.iter().filter(|m| m.topic == topic && m.message.engine_id == engine_id) {
				if !force && peer.known_messages.contains(&entry.message_hash) {
					continue
				}
				if !message_allowed(who, intent, &entry.topic, &entry.message.data) {
					continue
				}
				peer.known_messages.insert(entry.message_hash.clone());
				trace!(target: "gossip", "Sending topic message to {}: {:?}", who, entry.message);
				protocol.send_consensus(who.clone(), ConsensusMessage {
					engine_id: engine_id.clone(),
					data: entry.message.data.clone(),
				});
			}
		}
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		protocol: &mut dyn Context<B>,
		topic: B::Hash,
		message: ConsensusMessage,
		force: bool,
	) {
		let message_hash = HashFor::<B>::hash(&message.data);
		self.register_message_hashed(message_hash, topic, message.clone());
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(protocol, iter::once((&message_hash, &topic, &message)), intent, &mut self.peers, &self.validators);
	}

	/// Send addressed message to a peer. The message is not kept or multicast
	/// later on.
	pub fn send_message(
		&mut self,
		protocol: &mut dyn Context<B>,
		who: &PeerId,
		message: ConsensusMessage,
	) {
		let peer = match self.peers.get_mut(who) {
			None => return,
			Some(peer) => peer,
		};

		let message_hash = HashFor::<B>::hash(&message.data);

		trace!(target: "gossip", "Sending direct to {}: {:?}", who, message);

		peer.known_messages.insert(message_hash);
		protocol.send_consensus(who.clone(), message.clone());
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
					message_hash: $hash,
					topic: $topic,
					message: ConsensusMessage { data: $m, engine_id: [0, 0, 0, 0]},
				});
			}
		}
	}

	struct AllowAll;
	impl Validator<Block> for AllowAll {
		fn validate(
			&self,
			_context: &mut dyn ValidatorContext<Block>,
			_sender: &PeerId,
			_data: &[u8],
		) -> ValidationResult<H256> {
			ValidationResult::ProcessAndKeep(H256::default())
		}
	}

	#[test]
	fn collects_garbage() {
		struct AllowOne;
		impl Validator<Block> for AllowOne {
			fn validate(
				&self,
				_context: &mut dyn ValidatorContext<Block>,
				_sender: &PeerId,
				data: &[u8],
			) -> ValidationResult<H256> {
				if data[0] == 1 {
					ValidationResult::ProcessAndKeep(H256::default())
				} else {
					ValidationResult::Discard
				}
			}

			fn message_expired<'a>(&'a self) -> Box<dyn FnMut(H256, &[u8]) -> bool + 'a> {
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
		consensus.register_validator_internal(test_engine_id, Arc::new(AllowAll));
		consensus.collect_garbage();
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.known_messages.len(), 2);

		consensus.register_validator_internal(test_engine_id, Arc::new(AllowOne));

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
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(topic, message.clone());
		let stream = consensus.messages_for([0, 0, 0, 0], topic);

		assert_eq!(stream.wait().next(), Some(Ok(TopicNotification { message: message.data, sender: None })));
	}

	#[test]
	fn can_keep_multiple_messages_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();

		let topic = [1; 32].into();
		let msg_a = ConsensusMessage { data: vec![1, 2, 3], engine_id: [0, 0, 0, 0] };
		let msg_b = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };

		consensus.register_message(topic, msg_a);
		consensus.register_message(topic, msg_b);

		assert_eq!(consensus.messages.len(), 2);
	}

	#[test]
	fn can_keep_multiple_subscribers_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let message = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 0] };
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(topic, message.clone());

		let stream1 = consensus.messages_for([0, 0, 0, 0], topic);
		let stream2 = consensus.messages_for([0, 0, 0, 0], topic);

		assert_eq!(stream1.wait().next(), Some(Ok(TopicNotification { message: message.data.clone(), sender: None })));
		assert_eq!(stream2.wait().next(), Some(Ok(TopicNotification { message: message.data, sender: None })));
	}

	#[test]
	fn topics_are_localized_to_engine_id() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let topic = [1; 32].into();
		let msg_a = ConsensusMessage { data: vec![1, 2, 3], engine_id: [0, 0, 0, 0] };
		let msg_b = ConsensusMessage { data: vec![4, 5, 6], engine_id: [0, 0, 0, 1] };

		consensus.register_message(topic, msg_a);
		consensus.register_message(topic, msg_b);

		let mut stream = consensus.messages_for([0, 0, 0, 0], topic).wait();

		assert_eq!(stream.next(), Some(Ok(TopicNotification { message: vec![1, 2, 3], sender: None })));
		let _ = consensus.live_message_sinks.remove(&([0, 0, 0, 0], topic));
		assert_eq!(stream.next(), None);
	}
}
