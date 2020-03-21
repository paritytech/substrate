// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::{Network, MessageIntent, Validator, ValidatorContext, ValidationResult};

use std::collections::{HashMap, HashSet, hash_map::Entry};
use std::sync::Arc;
use std::iter;
use std::time;
use log::{trace, debug};
use futures::channel::mpsc;
use lru::LruCache;
use libp2p::PeerId;
use sp_runtime::traits::{Block as BlockT, Hash, HashFor};
use sp_runtime::ConsensusEngineId;
use sc_network::config::Roles;
use wasm_timer::Instant;

// FIXME: Add additional spam/DoS attack protection: https://github.com/paritytech/substrate/issues/1115
const KNOWN_MESSAGES_CACHE_SIZE: usize = 4096;

const REBROADCAST_INTERVAL: time::Duration = time::Duration::from_secs(30);

pub(crate) const PERIODIC_MAINTENANCE_INTERVAL: time::Duration = time::Duration::from_millis(1100);

mod rep {
	use sc_network::ReputationChange as Rep;
	/// Reputation change when a peer sends us a gossip message that we didn't know about.
	pub const GOSSIP_SUCCESS: Rep = Rep::new(1 << 4, "Successfull gossip");
	/// Reputation change when a peer sends us a gossip message that we already knew about.
	pub const DUPLICATE_GOSSIP: Rep = Rep::new(-(1 << 2), "Duplicate gossip");
	/// Reputation change when a peer sends us a gossip message for an unknown engine, whatever that
	/// means.
	pub const UNKNOWN_GOSSIP: Rep = Rep::new(-(1 << 6), "Unknown gossip message engine id");
	/// Reputation change when a peer sends a message from a topic it isn't registered on.
	pub const UNREGISTERED_TOPIC: Rep = Rep::new(-(1 << 10), "Unregistered gossip message topic");
}

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
	engine_id: ConsensusEngineId,
	message: Vec<u8>,
	sender: Option<PeerId>,
}

/// Local implementation of `ValidatorContext`.
struct NetworkContext<'g, 'p, B: BlockT> {
	gossip: &'g mut ConsensusGossip<B>,
	network: &'p mut dyn Network<B>,
	engine_id: ConsensusEngineId,
}

impl<'g, 'p, B: BlockT> ValidatorContext<B> for NetworkContext<'g, 'p, B> {
	/// Broadcast all messages with given topic to peers that do not have it yet.
	fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.gossip.broadcast_topic(self.network, topic, force);
	}

	/// Broadcast a message to all peers that have not received it previously.
	fn broadcast_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool) {
		self.gossip.multicast(
			self.network,
			topic,
			self.engine_id.clone(),
			message,
			force,
		);
	}

	/// Send addressed message to a peer.
	fn send_message(&mut self, who: &PeerId, message: Vec<u8>) {
		self.network.write_notification(who.clone(), self.engine_id, message);
	}

	/// Send all messages with given topic to a peer.
	fn send_topic(&mut self, who: &PeerId, topic: B::Hash, force: bool) {
		self.gossip.send_topic(self.network, who, topic, self.engine_id, force);
	}
}

fn propagate<'a, B: BlockT, I>(
	network: &mut dyn Network<B>,
	messages: I,
	intent: MessageIntent,
	peers: &mut HashMap<PeerId, PeerConsensus<B::Hash>>,
	validators: &HashMap<ConsensusEngineId, Arc<dyn Validator<B>>>,
)
	// (msg_hash, topic, message)
	where I: Clone + IntoIterator<Item=(&'a B::Hash, &'a B::Hash, ConsensusEngineId, &'a Vec<u8>)>,
{
	let mut check_fns = HashMap::new();
	let mut message_allowed = move |who: &PeerId, intent: MessageIntent, topic: &B::Hash, engine_id: ConsensusEngineId, message: &Vec<u8>| {
		let check_fn = match check_fns.entry(engine_id) {
			Entry::Occupied(entry) => entry.into_mut(),
			Entry::Vacant(vacant) => match validators.get(&engine_id) {
				None => return false, // treat all messages with no validator as not allowed
				Some(validator) => vacant.insert(validator.message_allowed()),
			}
		};

		(check_fn)(who, intent, topic, &message)
	};

	for (id, ref mut peer) in peers.iter_mut() {
		for (message_hash, topic, engine_id, message) in messages.clone() {
			let intent = match intent {
				MessageIntent::Broadcast { .. } =>
					if peer.known_messages.contains(&message_hash) {
						continue;
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

			if !message_allowed(id, intent, &topic, engine_id, &message) {
				continue;
			}

			peer.known_messages.insert(message_hash.clone());

			trace!(target: "gossip", "Propagating to {}: {:?}", id, message);
			network.write_notification(id.clone(), engine_id, message.clone());
		}
	}
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<PeerId, PeerConsensus<B::Hash>>,
	live_message_sinks: HashMap<(ConsensusEngineId, B::Hash), Vec<mpsc::UnboundedSender<TopicNotification>>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: LruCache<B::Hash, ()>,
	validators: HashMap<ConsensusEngineId, Arc<dyn Validator<B>>>,
	next_broadcast: Instant,
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
			next_broadcast: Instant::now() + REBROADCAST_INTERVAL,
		}
	}

	/// Register message validator for a message type.
	pub fn register_validator(
		&mut self,
		network: &mut dyn Network<B>,
		engine_id: ConsensusEngineId,
		validator: Arc<dyn Validator<B>>
	) {
		self.register_validator_internal(engine_id, validator.clone());
		let peers: Vec<_> = self.peers.iter().map(|(id, peer)| (id.clone(), peer.roles)).collect();
		for (id, roles) in peers {
			let mut context = NetworkContext { gossip: self, network, engine_id: engine_id.clone() };
			validator.new_peer(&mut context, &id, roles);
		}
	}

	fn register_validator_internal(&mut self, engine_id: ConsensusEngineId, validator: Arc<dyn Validator<B>>) {
		self.validators.insert(engine_id, validator.clone());
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, network: &mut dyn Network<B>, who: PeerId, roles: Roles) {
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
			let mut context = NetworkContext { gossip: self, network, engine_id: engine_id.clone() };
			v.new_peer(&mut context, &who, roles);
		}
	}

	fn register_message_hashed(
		&mut self,
		message_hash: B::Hash,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
		sender: Option<PeerId>,
	) {
		if self.known_messages.put(message_hash.clone(), ()).is_none() {
			self.messages.push(MessageEntry {
				message_hash,
				topic,
				engine_id,
				message,
				sender,
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
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
	) {
		let message_hash = HashFor::<B>::hash(&message[..]);
		self.register_message_hashed(message_hash, topic, engine_id, message, None);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, network: &mut dyn Network<B>, who: PeerId) {
		for (engine_id, v) in self.validators.clone() {
			let mut context = NetworkContext { gossip: self, network, engine_id: engine_id.clone() };
			v.peer_disconnected(&mut context, &who);
		}
		self.peers.remove(&who);
	}

	/// Perform periodic maintenance
	pub fn tick(&mut self, network: &mut dyn Network<B>) {
		self.collect_garbage();
		if Instant::now() >= self.next_broadcast {
			self.rebroadcast(network);
			self.next_broadcast = Instant::now() + REBROADCAST_INTERVAL;
		}
	}

	/// Rebroadcast all messages to all peers.
	fn rebroadcast(&mut self, network: &mut dyn Network<B>) {
		let messages = self.messages.iter()
			.map(|entry| (&entry.message_hash, &entry.topic, entry.engine_id, &entry.message));
		propagate(network, messages, MessageIntent::PeriodicRebroadcast, &mut self.peers, &self.validators);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, network: &mut dyn Network<B>, topic: B::Hash, force: bool) {
		let messages = self.messages.iter()
			.filter_map(|entry|
				if entry.topic == topic {
					Some((&entry.message_hash, &entry.topic, entry.engine_id, &entry.message))
				} else { None }
			);
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(network, messages, intent, &mut self.peers, &self.validators);
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
			let engine_id = entry.engine_id;
			let check_fn = match check_fns.entry(engine_id) {
				Entry::Occupied(entry) => entry.into_mut(),
				Entry::Vacant(vacant) => match validators.get(&engine_id) {
					None => return true, // treat all messages with no validator as expired
					Some(validator) => vacant.insert(validator.message_expired()),
				}
			};

			(check_fn)(entry.topic, &entry.message)
		};

		self.messages.retain(|entry| !message_expired(entry));

		trace!(target: "gossip", "Cleaned up {} stale messages, {} left ({} known)",
			before - self.messages.len(),
			self.messages.len(),
			known_messages.len(),
		);

		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| known_messages.contains(h));
		}
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile)
	pub fn messages_for(&mut self, engine_id: ConsensusEngineId, topic: B::Hash)
		-> mpsc::UnboundedReceiver<TopicNotification>
	{
		let (tx, rx) = mpsc::unbounded();
		for entry in self.messages.iter_mut()
			.filter(|e| e.topic == topic && e.engine_id == engine_id)
		{
			tx.unbounded_send(TopicNotification {
					message: entry.message.clone(),
					sender: entry.sender.clone(),
				})
				.expect("receiver known to be live; qed");
		}

		self.live_message_sinks.entry((engine_id, topic)).or_default().push(tx);

		rx
	}

	/// Handle an incoming message for topic by who via protocol. Discard message if topic already
	/// known, the message is old, its source peers isn't a registered peer or the connection to
	/// them is broken. Return `Some(topic, message)` if it was added to the internal queue, `None`
	/// in all other cases.
	pub fn on_incoming(
		&mut self,
		network: &mut dyn Network<B>,
		who: PeerId,
		messages: Vec<(ConsensusEngineId, Vec<u8>)>,
	) {
		if !messages.is_empty() {
			trace!(target: "gossip", "Received {} messages from peer {}", messages.len(), who);
		}

		for (engine_id, message) in messages {
			let message_hash = HashFor::<B>::hash(&message[..]);

			if self.known_messages.contains(&message_hash) {
				trace!(target:"gossip", "Ignored already known message from {}", who);
				network.report_peer(who.clone(), rep::DUPLICATE_GOSSIP);
				continue;
			}

			// validate the message
			let validation = self.validators.get(&engine_id)
				.cloned()
				.map(|v| {
					let mut context = NetworkContext { gossip: self, network, engine_id };
					v.validate(&mut context, &who, &message)
				});

			let validation_result = match validation {
				Some(ValidationResult::ProcessAndKeep(topic)) => Some((topic, true)),
				Some(ValidationResult::ProcessAndDiscard(topic)) => Some((topic, false)),
				Some(ValidationResult::Discard) => None,
				None => {
					trace!(target:"gossip", "Unknown message engine id {:?} from {}", engine_id, who);
					network.report_peer(who.clone(), rep::UNKNOWN_GOSSIP);
					network.disconnect_peer(who.clone());
					continue;
				}
			};

			if let Some((topic, keep)) = validation_result {
				network.report_peer(who.clone(), rep::GOSSIP_SUCCESS);
				if let Some(ref mut peer) = self.peers.get_mut(&who) {
					peer.known_messages.insert(message_hash);
					if let Entry::Occupied(mut entry) = self.live_message_sinks.entry((engine_id, topic)) {
						debug!(target: "gossip", "Pushing consensus message to sinks for {}.", topic);
						entry.get_mut().retain(|sink| {
							if let Err(e) = sink.unbounded_send(TopicNotification {
								message: message.clone(),
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
						self.register_message_hashed(message_hash, topic, engine_id, message, Some(who.clone()));
					}
				} else {
					trace!(target:"gossip", "Ignored statement from unregistered peer {}", who);
					network.report_peer(who.clone(), rep::UNREGISTERED_TOPIC);
				}
			} else {
				trace!(target:"gossip", "Handled valid one hop message from peer {}", who);
			}
		}
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&mut self,
		network: &mut dyn Network<B>,
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

		if let Some(ref mut peer) = self.peers.get_mut(who) {
			for entry in self.messages.iter().filter(|m| m.topic == topic && m.engine_id == engine_id) {
				let intent = if force {
					MessageIntent::ForcedBroadcast
				} else {
					MessageIntent::Broadcast
				};

				if !force && peer.known_messages.contains(&entry.message_hash) {
					continue;
				}

				if !message_allowed(who, intent, &entry.topic, &entry.message) {
					continue;
				}

				peer.known_messages.insert(entry.message_hash.clone());

				trace!(target: "gossip", "Sending topic message to {}: {:?}", who, entry.message);
				network.write_notification(who.clone(), engine_id, entry.message.clone());
			}
		}
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		network: &mut dyn Network<B>,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
		force: bool,
	) {
		let message_hash = HashFor::<B>::hash(&message);
		self.register_message_hashed(message_hash, topic, engine_id, message.clone(), None);
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(network, iter::once((&message_hash, &topic, engine_id, &message)), intent, &mut self.peers, &self.validators);
	}

	/// Send addressed message to a peer. The message is not kept or multicast
	/// later on.
	pub fn send_message(
		&mut self,
		network: &mut dyn Network<B>,
		who: &PeerId,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
	) {
		let peer = match self.peers.get_mut(who) {
			None => return,
			Some(peer) => peer,
		};

		let message_hash = HashFor::<B>::hash(&message);

		trace!(target: "gossip", "Sending direct to {}: {:?}", who, message);

		peer.known_messages.insert(message_hash);
		network.write_notification(who.clone(), engine_id, message);
	}
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use sp_runtime::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use futures::executor::block_on_stream;

	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	macro_rules! push_msg {
		($consensus:expr, $topic:expr, $hash: expr, $m:expr) => {
			if $consensus.known_messages.put($hash, ()).is_none() {
				$consensus.messages.push(MessageEntry {
					message_hash: $hash,
					topic: $topic,
					engine_id: [0, 0, 0, 0],
					message: $m,
					sender: None,
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
				Box::new(move |_topic, data| data[0] != 1)
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
		push_msg!(consensus, best_hash, m2_hash, m2);
		consensus.known_messages.put(m1_hash, ());
		consensus.known_messages.put(m2_hash, ());

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
		assert!(consensus.known_messages.contains(&m2_hash));
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let engine_id = [0, 0, 0, 0];
		let message = vec![4, 5, 6];
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(topic, engine_id, message.clone());
		let mut stream = block_on_stream(consensus.messages_for([0, 0, 0, 0], topic));

		assert_eq!(stream.next(), Some(TopicNotification { message: message, sender: None }));
	}

	#[test]
	fn can_keep_multiple_messages_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();

		let topic = [1; 32].into();
		let msg_a = vec![1, 2, 3];
		let msg_b = vec![4, 5, 6];

		consensus.register_message(topic, [0, 0, 0, 0], msg_a);
		consensus.register_message(topic, [0, 0, 0, 0], msg_b);

		assert_eq!(consensus.messages.len(), 2);
	}

	#[test]
	fn can_keep_multiple_subscribers_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let message = vec![4, 5, 6];
		let topic = HashFor::<Block>::hash(&[1, 2, 3]);

		consensus.register_message(topic, [0, 0, 0, 0], message.clone());

		let mut stream1 = block_on_stream(consensus.messages_for([0, 0, 0, 0], topic));
		let mut stream2 = block_on_stream(consensus.messages_for([0, 0, 0, 0], topic));

		assert_eq!(stream1.next(), Some(TopicNotification { message: message.clone(), sender: None }));
		assert_eq!(stream2.next(), Some(TopicNotification { message, sender: None }));
	}

	#[test]
	fn topics_are_localized_to_engine_id() {
		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let topic = [1; 32].into();
		let msg_a = vec![1, 2, 3];
		let msg_b = vec![4, 5, 6];

		consensus.register_message(topic, [0, 0, 0, 0], msg_a);
		consensus.register_message(topic, [0, 0, 0, 1], msg_b);

		let mut stream = block_on_stream(consensus.messages_for([0, 0, 0, 0], topic));

		assert_eq!(stream.next(), Some(TopicNotification { message: vec![1, 2, 3], sender: None }));

		let _ = consensus.live_message_sinks.remove(&([0, 0, 0, 0], topic));
		assert_eq!(stream.next(), None);
	}

	#[test]
	fn peer_is_removed_on_disconnect() {
		struct TestNetwork;
		impl Network<Block> for TestNetwork {
			fn event_stream(
				&self,
			) -> std::pin::Pin<Box<dyn futures::Stream<Item = crate::Event> + Send>> {
				unimplemented!("Not required in tests")
			}

			fn report_peer(&self, _: PeerId, _: crate::ReputationChange) {
				unimplemented!("Not required in tests")
			}

			fn disconnect_peer(&self, _: PeerId) {
				unimplemented!("Not required in tests")
			}

			fn write_notification(&self, _: PeerId, _: crate::ConsensusEngineId, _: Vec<u8>) {
				unimplemented!("Not required in tests")
			}

			fn register_notifications_protocol(
				&self,
				_: ConsensusEngineId,
				_: std::borrow::Cow<'static, [u8]>,
			) {
				unimplemented!("Not required in tests")
			}

			fn announce(&self, _: H256, _: Vec<u8>) {
				unimplemented!("Not required in tests")
			}
		}

		let mut consensus = ConsensusGossip::<Block>::new();
		consensus.register_validator_internal([0, 0, 0, 0], Arc::new(AllowAll));

		let mut network = TestNetwork;

		let peer_id = PeerId::random();
		consensus.new_peer(&mut network, peer_id.clone(), Roles::FULL);
		assert!(consensus.peers.contains_key(&peer_id));

		consensus.peer_disconnected(&mut network, peer_id.clone());
		assert!(!consensus.peers.contains_key(&peer_id));
	}
}
