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
use futures::sync::mpsc;
use std::time::{Instant, Duration};
use rand::{self, Rng};
use network_libp2p::NodeIndex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash, HashFor};
use runtime_primitives::generic::BlockId;
use message::generic::{Message, ConsensusMessage};
use protocol::Context;
use service::Roles;
use specialization::Specialization;
use StatusMessage;
use generic_message;

// TODO: Add additional spam/DoS attack protection.
const MESSAGE_LIFETIME: Duration = Duration::from_secs(600);

struct PeerConsensus<H> {
	known_messages: HashSet<H>,
	is_authority: bool,
}

struct MessageEntry<B: BlockT> {
	topic: B::Hash,
	message_hash: B::Hash,
	message: ConsensusMessage,
	instant: Instant,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct ConsensusGossip<B: BlockT> {
	peers: HashMap<NodeIndex, PeerConsensus<(B::Hash, B::Hash)>>,
	live_message_sinks: HashMap<B::Hash, mpsc::UnboundedSender<ConsensusMessage>>,
	messages: Vec<MessageEntry<B>>,
	known_messages: HashSet<(B::Hash, B::Hash)>,
	session_start: Option<B::Hash>,
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
			known_messages: Default::default(),
			session_start: None
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
				known_messages.insert((entry.topic, entry.message_hash));
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

	fn propagate<F>(
		&mut self,
		protocol: &mut Context<B>,
		message_hash: B::Hash,
		topic: B::Hash,
		get_message: F,
	)
		where F: Fn() -> ConsensusMessage,
	{
		let mut non_authorities: Vec<_> = self.peers.iter()
			.filter_map(|(id, ref peer)| if !peer.is_authority && !peer.known_messages.contains(&(topic, message_hash)) { Some(*id) } else { None })
			.collect();

		rand::thread_rng().shuffle(&mut non_authorities);
		let non_authorities: HashSet<_> = if non_authorities.is_empty() {
			HashSet::new()
		} else {
			non_authorities[0..non_authorities.len().min(((non_authorities.len() as f64).sqrt() as usize).max(3))].iter().collect()
		};

		for (id, ref mut peer) in self.peers.iter_mut() {
			if peer.is_authority {
				if peer.known_messages.insert((topic.clone(), message_hash.clone())) {
					let message = get_message();
					trace!(target:"gossip", "Propagating to authority {}: {:?}", id, message);
					protocol.send_message(*id, Message::Consensus(topic, message));
				}
			} else if non_authorities.contains(&id) {
				let message = get_message();
				trace!(target:"gossip", "Propagating to {}: {:?}", id, message);
				peer.known_messages.insert((topic.clone(), message_hash.clone()));
				protocol.send_message(*id, Message::Consensus(topic, message));
			}
		}
	}

	fn register_message<F>(&mut self, message_hash: B::Hash, topic: B::Hash, get_message: F)
		where F: Fn() -> ConsensusMessage
	{
		if self.known_messages.insert((topic, message_hash)) {
			self.messages.push(MessageEntry {
				topic,
				message_hash,
				instant: Instant::now(),
				message: get_message(),
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

		let hashes = &mut self.known_messages;
		let before = self.messages.len();
		let now = Instant::now();
		self.messages.retain(|entry| {
			if entry.instant + MESSAGE_LIFETIME >= now && predicate(&entry.topic) {
				true
			} else {
				hashes.remove(&(entry.topic, entry.message_hash));
				false
			}
		});
		trace!(target:"gossip", "Cleaned up {} stale messages, {} left", before - self.messages.len(), self.messages.len());
		for (_, ref mut peer) in self.peers.iter_mut() {
			peer.known_messages.retain(|h| hashes.contains(h));
		}
	}

	/// Get all incoming messages for a topic.
	pub fn messages_for(&mut self, topic: B::Hash) -> mpsc::UnboundedReceiver<ConsensusMessage> {
		let (tx, rx) = mpsc::unbounded();
		for entry in self.messages.iter().filter(|e| e.topic == topic) {
			tx.unbounded_send(entry.message.clone()).expect("receiver known to be live; qed");
		}
		self.live_message_sinks.insert(topic, tx);

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
		topic: B::Hash,
		message: ConsensusMessage,
	) -> Option<(B::Hash, ConsensusMessage)> {
		let message_hash = HashFor::<B>::hash(&message[..]);

		if self.known_messages.contains(&(topic, message_hash)) {
			trace!(target:"gossip", "Ignored already known message from {} in {}", who, topic);
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
			peer.known_messages.insert((topic, message_hash));
			if let Entry::Occupied(mut entry) = self.live_message_sinks.entry(topic) {
				debug!(target: "gossip", "Pushing consensus message to sink for {}.", topic);
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

		self.multicast_inner(protocol, message_hash, topic, || message.clone());
		Some((topic, message))
	}

	/// Multicast a message to all peers.
	pub fn multicast(&mut self, protocol: &mut Context<B>, topic: B::Hash, message: ConsensusMessage) {
		let message_hash = HashFor::<B>::hash(&message);
		self.multicast_inner(protocol, message_hash, topic, || message.clone());
	}

	fn multicast_inner<F>(&mut self, protocol: &mut Context<B>, message_hash: B::Hash, topic: B::Hash, get_message: F)
		where F: Fn() -> ConsensusMessage
	{
		self.register_message(message_hash, topic, &get_message);
		self.propagate(protocol, message_hash, topic, get_message);
	}

	/// Note new consensus session.
	pub fn new_session(&mut self, parent_hash: B::Hash) {
		let old_session = self.session_start.take();
		self.session_start = Some(parent_hash);
		self.collect_garbage(|topic| old_session.as_ref().map_or(true, |h| topic != h));
	}
}

impl<Block: BlockT> Specialization<Block> for ConsensusGossip<Block> where
	Block::Header: HeaderT<Number=u64>
{
	fn status(&self) -> Vec<u8> {
		Vec::new()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, who: NodeIndex, status: StatusMessage<Block>) {
		self.new_peer(ctx, who, status.roles);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, who: NodeIndex) {
		self.peer_disconnected(ctx, who);
	}

	fn on_message(
		&mut self,
		ctx: &mut Context<Block>,
		who: NodeIndex,
		message: &mut Option<::message::Message<Block>>
	) {
		match message.take() {
			Some(generic_message::Message::Consensus(topic, msg)) => {
				trace!(target: "gossip", "Consensus message from {}: {:?}", who, msg);
				self.on_incoming(ctx, who, topic, msg);
			}
			r => *message = r,
		}
	}

	fn on_abort(&mut self) {
		self.abort();
	}

	fn maintain_peers(&mut self, _ctx: &mut Context<Block>) {
		self.collect_garbage(|_| true);
	}

	fn on_block_imported(
		&mut self,
		_ctx: &mut Context<Block>,
		_hash: <Block as BlockT>::Hash,
		_header: &<Block as BlockT>::Header)
	{}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use std::time::Instant;
	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	#[test]
	fn collects_garbage() {
		let prev_hash = H256::random();
		let best_hash = H256::random();
		let mut consensus = ConsensusGossip::<Block>::new();
		let now = Instant::now();
		let m1_hash = H256::random();
		let m2_hash = H256::random();
		let m1 = vec![1, 2, 3];
		let m2 = vec![4, 5, 6];

		macro_rules! push_msg {
			($topic:expr, $hash: expr, $now: expr, $m:expr) => {
				consensus.messages.push(MessageEntry {
					topic: $topic,
					message_hash: $hash,
					instant: $now,
					message: $m,
				})
			}
		}

		push_msg!(prev_hash, m1_hash, now, m1);
		push_msg!(best_hash, m2_hash, now, m2.clone());
		consensus.known_messages.insert((prev_hash, m1_hash));
		consensus.known_messages.insert((best_hash, m2_hash));

		// nothing to collect
		consensus.collect_garbage(|_t| true);
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.known_messages.len(), 2);

		// nothing to collect with default.
		consensus.collect_garbage(|&topic| topic != Default::default());
		assert_eq!(consensus.messages.len(), 2);
		assert_eq!(consensus.known_messages.len(), 2);

		// topic that was used in one message.
		consensus.collect_garbage(|topic| topic != &prev_hash);
		assert_eq!(consensus.messages.len(), 1);
		assert_eq!(consensus.known_messages.len(), 1);
		assert!(consensus.known_messages.contains(&(best_hash, m2_hash)));

		// make timestamp expired
		consensus.messages.clear();
		push_msg!(best_hash, m2_hash, now - MESSAGE_LIFETIME, m2);
		consensus.collect_garbage(|_topic| true);
		assert!(consensus.messages.is_empty());
		assert!(consensus.known_messages.is_empty());
	}

	#[test]
	fn message_stream_include_those_sent_before_asking_for_stream() {
		use futures::Stream;

		let mut consensus = ConsensusGossip::<Block>::new();

		let message = vec![1, 2, 3];

		let message_hash = HashFor::<Block>::hash(&message);
		let topic = HashFor::<Block>::hash(&[1,2,3]);

		consensus.register_message(message_hash, topic, || message.clone());
		let stream = consensus.messages_for(topic);

		assert_eq!(stream.wait().next(), Some(Ok(message)));
	}

	#[test]
	fn can_keep_multiple_messages_per_topic() {
		let mut consensus = ConsensusGossip::<Block>::new();

		let topic = [1; 32].into();
		let msg_a = vec![1, 2, 3];
		let msg_b = vec![4, 5, 6];

		consensus.register_message(HashFor::<Block>::hash(&msg_a), topic, || msg_a.clone());
		consensus.register_message(HashFor::<Block>::hash(&msg_b), topic, || msg_b.clone());

		assert_eq!(consensus.messages.len(), 2);
	}
}
