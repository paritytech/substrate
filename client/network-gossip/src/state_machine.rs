// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{MessageIntent, Network, ValidationResult, Validator, ValidatorContext};

use ahash::AHashSet;
use libp2p::PeerId;
use lru::LruCache;
use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use sc_network_common::protocol::event::ObservedRole;
use sp_runtime::traits::{Block as BlockT, Hash, HashFor};
use std::{borrow::Cow, collections::HashMap, iter, sync::Arc, time, time::Instant};

// FIXME: Add additional spam/DoS attack protection: https://github.com/paritytech/substrate/issues/1115
// NOTE: The current value is adjusted based on largest production network deployment (Kusama) and
// the current main gossip user (GRANDPA). Currently there are ~800 validators on Kusama, as such,
// each GRANDPA round should generate ~1600 messages, and we currently keep track of the last 2
// completed rounds and the current live one. That makes it so that at any point we will be holding
// ~4800 live messages.
//
// Assuming that each known message is tracked with a 32 byte hash (common for `Block::Hash`), then
// this cache should take about 256 KB of memory.
const KNOWN_MESSAGES_CACHE_SIZE: usize = 8192;

const REBROADCAST_INTERVAL: time::Duration = time::Duration::from_millis(750);

pub(crate) const PERIODIC_MAINTENANCE_INTERVAL: time::Duration = time::Duration::from_millis(1100);

mod rep {
	use sc_peerset::ReputationChange as Rep;
	/// Reputation change when a peer sends us a gossip message that we didn't know about.
	pub const GOSSIP_SUCCESS: Rep = Rep::new(1 << 4, "Successful gossip");
	/// Reputation change when a peer sends us a gossip message that we already knew about.
	pub const DUPLICATE_GOSSIP: Rep = Rep::new(-(1 << 2), "Duplicate gossip");
}

struct PeerConsensus<H> {
	known_messages: AHashSet<H>,
}

/// Topic stream message with sender.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TopicNotification {
	/// Message data.
	pub message: Vec<u8>,
	/// Sender if available.
	pub sender: Option<PeerId>,
}

struct MessageEntry<B: BlockT> {
	message_hash: B::Hash,
	topic: B::Hash,
	message: Vec<u8>,
	sender: Option<PeerId>,
}

/// Local implementation of `ValidatorContext`.
struct NetworkContext<'g, 'p, B: BlockT> {
	gossip: &'g mut ConsensusGossip<B>,
	network: &'p mut dyn Network<B>,
}

impl<'g, 'p, B: BlockT> ValidatorContext<B> for NetworkContext<'g, 'p, B> {
	/// Broadcast all messages with given topic to peers that do not have it yet.
	fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.gossip.broadcast_topic(self.network, topic, force);
	}

	/// Broadcast a message to all peers that have not received it previously.
	fn broadcast_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool) {
		self.gossip.multicast(self.network, topic, message, force);
	}

	/// Send addressed message to a peer.
	fn send_message(&mut self, who: &PeerId, message: Vec<u8>) {
		self.network.write_notification(*who, self.gossip.protocol.clone(), message);
	}

	/// Send all messages with given topic to a peer.
	fn send_topic(&mut self, who: &PeerId, topic: B::Hash, force: bool) {
		self.gossip.send_topic(self.network, who, topic, force);
	}
}

fn propagate<'a, B: BlockT, I>(
	network: &mut dyn Network<B>,
	protocol: Cow<'static, str>,
	messages: I,
	intent: MessageIntent,
	peers: &mut HashMap<PeerId, PeerConsensus<B::Hash>>,
	validator: &Arc<dyn Validator<B>>,
)
// (msg_hash, topic, message)
where
	I: Clone + IntoIterator<Item = (&'a B::Hash, &'a B::Hash, &'a Vec<u8>)>,
{
	let mut message_allowed = validator.message_allowed();

	for (id, ref mut peer) in peers.iter_mut() {
		for (message_hash, topic, message) in messages.clone() {
			let intent = match intent {
				MessageIntent::Broadcast { .. } =>
					if peer.known_messages.contains(message_hash) {
						continue
					} else {
						MessageIntent::Broadcast
					},
				MessageIntent::PeriodicRebroadcast => {
					if peer.known_messages.contains(message_hash) {
						MessageIntent::PeriodicRebroadcast
					} else {
						// peer doesn't know message, so the logic should treat it as an
						// initial broadcast.
						MessageIntent::Broadcast
					}
				},
				other => other,
			};

			if !message_allowed(id, intent, topic, message) {
				continue
			}

			peer.known_messages.insert(*message_hash);

			tracing::trace!(
				target: "gossip",
				to = %id,
				%protocol,
				?message,
				"Propagating message",
			);
			network.write_notification(*id, protocol.clone(), message.clone());
		}
	}
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<PeerId, PeerConsensus<B::Hash>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: LruCache<B::Hash, ()>,
	protocol: Cow<'static, str>,
	validator: Arc<dyn Validator<B>>,
	next_broadcast: Instant,
	metrics: Option<Metrics>,
}

impl<B: BlockT> ConsensusGossip<B> {
	/// Create a new instance using the given validator.
	pub fn new(
		validator: Arc<dyn Validator<B>>,
		protocol: Cow<'static, str>,
		metrics_registry: Option<&Registry>,
	) -> Self {
		let metrics = match metrics_registry.map(Metrics::register) {
			Some(Ok(metrics)) => Some(metrics),
			Some(Err(e)) => {
				tracing::debug!(target: "gossip", "Failed to register metrics: {:?}", e);
				None
			},
			None => None,
		};

		ConsensusGossip {
			peers: HashMap::new(),
			messages: Default::default(),
			known_messages: LruCache::new(KNOWN_MESSAGES_CACHE_SIZE),
			protocol,
			validator,
			next_broadcast: Instant::now() + REBROADCAST_INTERVAL,
			metrics,
		}
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, network: &mut dyn Network<B>, who: PeerId, role: ObservedRole) {
		tracing::trace!(
			target:"gossip",
			%who,
			protocol = %self.protocol,
			?role,
			"Registering peer",
		);
		self.peers.insert(who, PeerConsensus { known_messages: Default::default() });

		let validator = self.validator.clone();
		let mut context = NetworkContext { gossip: self, network };
		validator.new_peer(&mut context, &who, role);
	}

	fn register_message_hashed(
		&mut self,
		message_hash: B::Hash,
		topic: B::Hash,
		message: Vec<u8>,
		sender: Option<PeerId>,
	) {
		if self.known_messages.put(message_hash, ()).is_none() {
			self.messages.push(MessageEntry { message_hash, topic, message, sender });

			if let Some(ref metrics) = self.metrics {
				metrics.registered_messages.inc();
			}
		}
	}

	/// Registers a message without propagating it to any peers. The message
	/// becomes available to new peers or when the service is asked to gossip
	/// the message's topic. No validation is performed on the message, if the
	/// message is already expired it should be dropped on the next garbage
	/// collection.
	pub fn register_message(&mut self, topic: B::Hash, message: Vec<u8>) {
		let message_hash = HashFor::<B>::hash(&message[..]);
		self.register_message_hashed(message_hash, topic, message, None);
	}

	/// Call when a peer has been disconnected to stop tracking gossip status.
	pub fn peer_disconnected(&mut self, network: &mut dyn Network<B>, who: PeerId) {
		let validator = self.validator.clone();
		let mut context = NetworkContext { gossip: self, network };
		validator.peer_disconnected(&mut context, &who);
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
		let messages = self
			.messages
			.iter()
			.map(|entry| (&entry.message_hash, &entry.topic, &entry.message));
		propagate(
			network,
			self.protocol.clone(),
			messages,
			MessageIntent::PeriodicRebroadcast,
			&mut self.peers,
			&self.validator,
		);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, network: &mut dyn Network<B>, topic: B::Hash, force: bool) {
		let messages = self.messages.iter().filter_map(|entry| {
			if entry.topic == topic {
				Some((&entry.message_hash, &entry.topic, &entry.message))
			} else {
				None
			}
		});
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(
			network,
			self.protocol.clone(),
			messages,
			intent,
			&mut self.peers,
			&self.validator,
		);
	}

	/// Prune old or no longer relevant consensus messages. Provide a predicate
	/// for pruning, which returns `false` when the items with a given topic should be pruned.
	pub fn collect_garbage(&mut self) {
		let known_messages = &mut self.known_messages;
		let before = self.messages.len();

		let mut message_expired = self.validator.message_expired();
		self.messages.retain(|entry| !message_expired(entry.topic, &entry.message));

		let expired_messages = before - self.messages.len();

		if let Some(ref metrics) = self.metrics {
			metrics.expired_messages.inc_by(expired_messages as u64)
		}

		tracing::trace!(
			target: "gossip",
			protocol = %self.protocol,
			"Cleaned up {} stale messages, {} left ({} known)",
			expired_messages,
			self.messages.len(),
			known_messages.len(),
		);

		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| known_messages.contains(h));
		}
	}

	/// Get valid messages received in the past for a topic (might have expired meanwhile).
	pub fn messages_for(&mut self, topic: B::Hash) -> impl Iterator<Item = TopicNotification> + '_ {
		self.messages
			.iter()
			.filter(move |e| e.topic == topic)
			.map(|entry| TopicNotification { message: entry.message.clone(), sender: entry.sender })
	}

	/// Register incoming messages and return the ones that are new and valid (according to a gossip
	/// validator) and should thus be forwarded to the upper layers.
	pub fn on_incoming(
		&mut self,
		network: &mut dyn Network<B>,
		who: PeerId,
		messages: Vec<Vec<u8>>,
	) -> Vec<(B::Hash, TopicNotification)> {
		let mut to_forward = vec![];

		if !messages.is_empty() {
			tracing::trace!(
				target: "gossip",
				messages_num = %messages.len(),
				%who,
				protocol = %self.protocol,
				"Received messages from peer",
			);
		}

		for message in messages {
			let message_hash = HashFor::<B>::hash(&message[..]);

			if self.known_messages.contains(&message_hash) {
				tracing::trace!(
					target: "gossip",
					%who,
					protocol = %self.protocol,
					"Ignored already known message",
				);
				network.report_peer(who, rep::DUPLICATE_GOSSIP);
				continue
			}

			// validate the message
			let validation = {
				let validator = self.validator.clone();
				let mut context = NetworkContext { gossip: self, network };
				validator.validate(&mut context, &who, &message)
			};

			let (topic, keep) = match validation {
				ValidationResult::ProcessAndKeep(topic) => (topic, true),
				ValidationResult::ProcessAndDiscard(topic) => (topic, false),
				ValidationResult::Discard => {
					tracing::trace!(
						target: "gossip",
						%who,
						protocol = %self.protocol,
						"Discard message from peer",
					);
					continue
				},
			};

			let peer = match self.peers.get_mut(&who) {
				Some(peer) => peer,
				None => {
					tracing::error!(
						target: "gossip",
						%who,
						protocol = %self.protocol,
						"Got message from unregistered peer",
					);
					continue
				},
			};

			network.report_peer(who, rep::GOSSIP_SUCCESS);
			peer.known_messages.insert(message_hash);
			to_forward
				.push((topic, TopicNotification { message: message.clone(), sender: Some(who) }));

			if keep {
				self.register_message_hashed(message_hash, topic, message, Some(who));
			}
		}

		to_forward
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&mut self,
		network: &mut dyn Network<B>,
		who: &PeerId,
		topic: B::Hash,
		force: bool,
	) {
		let mut message_allowed = self.validator.message_allowed();

		if let Some(ref mut peer) = self.peers.get_mut(who) {
			for entry in self.messages.iter().filter(|m| m.topic == topic) {
				let intent =
					if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };

				if !force && peer.known_messages.contains(&entry.message_hash) {
					continue
				}

				if !message_allowed(who, intent, &entry.topic, &entry.message) {
					continue
				}

				peer.known_messages.insert(entry.message_hash);

				tracing::trace!(
					target: "gossip",
					to = %who,
					protocol = %self.protocol,
					?entry.message,
					"Sending topic message",
				);
				network.write_notification(*who, self.protocol.clone(), entry.message.clone());
			}
		}
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		network: &mut dyn Network<B>,
		topic: B::Hash,
		message: Vec<u8>,
		force: bool,
	) {
		let message_hash = HashFor::<B>::hash(&message);
		self.register_message_hashed(message_hash, topic, message.clone(), None);
		let intent = if force { MessageIntent::ForcedBroadcast } else { MessageIntent::Broadcast };
		propagate(
			network,
			self.protocol.clone(),
			iter::once((&message_hash, &topic, &message)),
			intent,
			&mut self.peers,
			&self.validator,
		);
	}

	/// Send addressed message to a peer. The message is not kept or multicast
	/// later on.
	pub fn send_message(&mut self, network: &mut dyn Network<B>, who: &PeerId, message: Vec<u8>) {
		let peer = match self.peers.get_mut(who) {
			None => return,
			Some(peer) => peer,
		};

		let message_hash = HashFor::<B>::hash(&message);

		tracing::trace!(
			target: "gossip",
			to = %who,
			protocol = %self.protocol,
			?message,
			"Sending direct message",
		);

		peer.known_messages.insert(message_hash);
		network.write_notification(*who, self.protocol.clone(), message);
	}
}

struct Metrics {
	registered_messages: Counter<U64>,
	expired_messages: Counter<U64>,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			registered_messages: register(
				Counter::new(
					"substrate_network_gossip_registered_messages_total",
					"Number of registered messages by the gossip service.",
				)?,
				registry,
			)?,
			expired_messages: register(
				Counter::new(
					"substrate_network_gossip_expired_messages_total",
					"Number of expired messages by the gossip service.",
				)?,
				registry,
			)?,
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::multiaddr::Multiaddr;
	use futures::prelude::*;
	use sc_network_common::{
		protocol::event::Event,
		service::{
			NetworkBlock, NetworkEventStream, NetworkNotification, NetworkPeers,
			NotificationSender, NotificationSenderError,
		},
	};
	use sc_peerset::ReputationChange;
	use sp_runtime::{
		testing::{Block as RawBlock, ExtrinsicWrapper, H256},
		traits::NumberFor,
	};
	use std::{
		borrow::Cow,
		collections::HashSet,
		pin::Pin,
		sync::{Arc, Mutex},
	};

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	macro_rules! push_msg {
		($consensus:expr, $topic:expr, $hash: expr, $m:expr) => {
			if $consensus.known_messages.put($hash, ()).is_none() {
				$consensus.messages.push(MessageEntry {
					message_hash: $hash,
					topic: $topic,
					message: $m,
					sender: None,
				});
			}
		};
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

	struct DiscardAll;
	impl Validator<Block> for DiscardAll {
		fn validate(
			&self,
			_context: &mut dyn ValidatorContext<Block>,
			_sender: &PeerId,
			_data: &[u8],
		) -> ValidationResult<H256> {
			ValidationResult::Discard
		}
	}

	#[derive(Clone, Default)]
	struct NoOpNetwork {
		inner: Arc<Mutex<NoOpNetworkInner>>,
	}

	#[derive(Clone, Default)]
	struct NoOpNetworkInner {
		peer_reports: Vec<(PeerId, ReputationChange)>,
	}

	impl NetworkPeers for NoOpNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!();
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!();
		}

		fn add_known_address(&self, _peer_id: PeerId, _addr: Multiaddr) {
			unimplemented!();
		}

		fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
			self.inner.lock().unwrap().peer_reports.push((who, cost_benefit));
		}

		fn disconnect_peer(&self, _who: PeerId, _protocol: Cow<'static, str>) {
			unimplemented!();
		}

		fn accept_unreserved_peers(&self) {
			unimplemented!();
		}

		fn deny_unreserved_peers(&self) {
			unimplemented!();
		}

		fn add_reserved_peer(&self, _peer: String) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_reserved_peer(&self, _peer_id: PeerId) {
			unimplemented!();
		}

		fn set_reserved_peers(
			&self,
			_protocol: Cow<'static, str>,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn add_peers_to_reserved_set(
			&self,
			_protocol: Cow<'static, str>,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_peers_from_reserved_set(
			&self,
			_protocol: Cow<'static, str>,
			_peers: Vec<PeerId>,
		) {
		}

		fn add_to_peers_set(
			&self,
			_protocol: Cow<'static, str>,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_from_peers_set(&self, _protocol: Cow<'static, str>, _peers: Vec<PeerId>) {
			unimplemented!();
		}

		fn sync_num_connected(&self) -> usize {
			unimplemented!();
		}
	}

	impl NetworkEventStream for NoOpNetwork {
		fn event_stream(&self, _name: &'static str) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
			unimplemented!();
		}
	}

	impl NetworkNotification for NoOpNetwork {
		fn write_notification(
			&self,
			_target: PeerId,
			_protocol: Cow<'static, str>,
			_message: Vec<u8>,
		) {
			unimplemented!();
		}

		fn notification_sender(
			&self,
			_target: PeerId,
			_protocol: Cow<'static, str>,
		) -> Result<Box<dyn NotificationSender>, NotificationSenderError> {
			unimplemented!();
		}
	}

	impl NetworkBlock<<Block as BlockT>::Hash, NumberFor<Block>> for NoOpNetwork {
		fn announce_block(&self, _hash: <Block as BlockT>::Hash, _data: Option<Vec<u8>>) {
			unimplemented!();
		}

		fn new_best_block_imported(
			&self,
			_hash: <Block as BlockT>::Hash,
			_number: NumberFor<Block>,
		) {
			unimplemented!();
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
		let mut consensus = ConsensusGossip::<Block>::new(Arc::new(AllowAll), "/foo".into(), None);
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = vec![1, 2, 3];
		let m2 = vec![4, 5, 6];

		push_msg!(consensus, prev_hash, m1_hash, m1);
		push_msg!(consensus, best_hash, m2_hash, m2);
		consensus.known_messages.put(m1_hash, ());
		consensus.known_messages.put(m2_hash, ());

		consensus.collect_garbage();
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.known_messages.len(), 2);

		consensus.validator = Arc::new(AllowOne);

		// m2 is expired
		consensus.collect_garbage();
		assert_eq!(consensus.messages.len(), 1);
		// known messages are only pruned based on size.
		assert_eq!(consensus.known_messages.len(), 2);
		assert!(consensus.known_messages.contains(&m2_hash));
	}

	#[test]
	fn message_stream_include_those_sent_before_asking() {
		let mut consensus = ConsensusGossip::<Block>::new(Arc::new(AllowAll), "/foo".into(), None);

		// Register message.
		let message = vec![4, 5, 6];
		let topic = HashFor::<Block>::hash(&[1, 2, 3]);
		consensus.register_message(topic, message.clone());

		assert_eq!(
			consensus.messages_for(topic).next(),
			Some(TopicNotification { message, sender: None }),
		);
	}

	#[test]
	fn can_keep_multiple_messages_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new(Arc::new(AllowAll), "/foo".into(), None);

		let topic = [1; 32].into();
		let msg_a = vec![1, 2, 3];
		let msg_b = vec![4, 5, 6];

		consensus.register_message(topic, msg_a);
		consensus.register_message(topic, msg_b);

		assert_eq!(consensus.messages.len(), 2);
	}

	#[test]
	fn peer_is_removed_on_disconnect() {
		let mut consensus = ConsensusGossip::<Block>::new(Arc::new(AllowAll), "/foo".into(), None);

		let mut network = NoOpNetwork::default();

		let peer_id = PeerId::random();
		consensus.new_peer(&mut network, peer_id, ObservedRole::Full);
		assert!(consensus.peers.contains_key(&peer_id));

		consensus.peer_disconnected(&mut network, peer_id);
		assert!(!consensus.peers.contains_key(&peer_id));
	}

	#[test]
	fn on_incoming_ignores_discarded_messages() {
		let to_forward = ConsensusGossip::<Block>::new(Arc::new(DiscardAll), "/foo".into(), None)
			.on_incoming(&mut NoOpNetwork::default(), PeerId::random(), vec![vec![1, 2, 3]]);

		assert!(
			to_forward.is_empty(),
			"Expected `on_incoming` to ignore discarded message but got {:?}",
			to_forward,
		);
	}

	#[test]
	fn on_incoming_ignores_unregistered_peer() {
		let mut network = NoOpNetwork::default();
		let remote = PeerId::random();

		let to_forward = ConsensusGossip::<Block>::new(Arc::new(AllowAll), "/foo".into(), None)
			.on_incoming(
				&mut network,
				// Unregistered peer.
				remote,
				vec![vec![1, 2, 3]],
			);

		assert!(
			to_forward.is_empty(),
			"Expected `on_incoming` to ignore message from unregistered peer but got {:?}",
			to_forward,
		);
	}
}
