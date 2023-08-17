// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::{
	state_machine::{ConsensusGossip, TopicNotification, PERIODIC_MAINTENANCE_INTERVAL},
	Network, Syncing, Validator,
};

use sc_network::{event::Event, types::ProtocolName, ReputationChange};
use sc_network_common::sync::SyncEvent;

use futures::{
	channel::mpsc::{channel, Receiver, Sender},
	prelude::*,
};
use libp2p::PeerId;
use log::trace;
use prometheus_endpoint::Registry;
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{HashMap, VecDeque},
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
};

/// Wraps around an implementation of the [`Network`] trait and provides gossiping capabilities on
/// top of it.
pub struct GossipEngine<B: BlockT> {
	state_machine: ConsensusGossip<B>,
	network: Box<dyn Network<B> + Send>,
	sync: Box<dyn Syncing<B>>,
	periodic_maintenance_interval: futures_timer::Delay,
	protocol: ProtocolName,

	/// Incoming events from the network.
	network_event_stream: Pin<Box<dyn Stream<Item = Event> + Send>>,
	/// Incoming events from the syncing service.
	sync_event_stream: Pin<Box<dyn Stream<Item = SyncEvent> + Send>>,
	/// Outgoing events to the consumer.
	message_sinks: HashMap<B::Hash, Vec<Sender<TopicNotification>>>,
	/// Buffered messages (see [`ForwardingState`]).
	forwarding_state: ForwardingState<B>,

	is_terminated: bool,
}

/// A gossip engine receives messages from the network via the `network_event_stream` and forwards
/// them to upper layers via the `message_sinks`. In the scenario where messages have been received
/// from the network but a subscribed message sink is not yet ready to receive the messages, the
/// messages are buffered. To model this process a gossip engine can be in two states.
enum ForwardingState<B: BlockT> {
	/// The gossip engine is currently not forwarding any messages and will poll the network for
	/// more messages to forward.
	Idle,
	/// The gossip engine is in the progress of forwarding messages and thus will not poll the
	/// network for more messages until it has send all current messages into the subscribed
	/// message sinks.
	Busy(VecDeque<(B::Hash, TopicNotification)>),
}

impl<B: BlockT> Unpin for GossipEngine<B> {}

impl<B: BlockT> GossipEngine<B> {
	/// Create a new instance.
	pub fn new<N, S>(
		network: N,
		sync: S,
		protocol: impl Into<ProtocolName>,
		validator: Arc<dyn Validator<B>>,
		metrics_registry: Option<&Registry>,
	) -> Self
	where
		B: 'static,
		N: Network<B> + Send + Clone + 'static,
		S: Syncing<B> + Send + Clone + 'static,
	{
		let protocol = protocol.into();
		let network_event_stream = network.event_stream("network-gossip");
		let sync_event_stream = sync.event_stream("network-gossip");

		GossipEngine {
			state_machine: ConsensusGossip::new(validator, protocol.clone(), metrics_registry),
			network: Box::new(network),
			sync: Box::new(sync),
			periodic_maintenance_interval: futures_timer::Delay::new(PERIODIC_MAINTENANCE_INTERVAL),
			protocol,

			network_event_stream,
			sync_event_stream,
			message_sinks: HashMap::new(),
			forwarding_state: ForwardingState::Idle,

			is_terminated: false,
		}
	}

	pub fn report(&self, who: PeerId, reputation: ReputationChange) {
		self.network.report_peer(who, reputation);
	}

	/// Registers a message without propagating it to any peers. The message
	/// becomes available to new peers or when the service is asked to gossip
	/// the message's topic. No validation is performed on the message, if the
	/// message is already expired it should be dropped on the next garbage
	/// collection.
	pub fn register_gossip_message(&mut self, topic: B::Hash, message: Vec<u8>) {
		self.state_machine.register_message(topic, message);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.state_machine.broadcast_topic(&mut *self.network, topic, force);
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile).
	pub fn messages_for(&mut self, topic: B::Hash) -> Receiver<TopicNotification> {
		let past_messages = self.state_machine.messages_for(topic).collect::<Vec<_>>();
		// The channel length is not critical for correctness. By the implementation of `channel`
		// each sender is guaranteed a single buffer slot, making it a non-rendezvous channel and
		// thus preventing direct dead-locks. A minimum channel length of 10 is an estimate based on
		// the fact that despite `NotificationsReceived` having a `Vec` of messages, it only ever
		// contains a single message.
		let (mut tx, rx) = channel(usize::max(past_messages.len(), 10));

		for notification in past_messages {
			tx.try_send(notification)
				.expect("receiver known to be live, and buffer size known to suffice; qed");
		}

		self.message_sinks.entry(topic).or_default().push(tx);

		rx
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(&mut self, who: &PeerId, topic: B::Hash, force: bool) {
		self.state_machine.send_topic(&mut *self.network, who, topic, force)
	}

	/// Multicast a message to all peers.
	pub fn gossip_message(&mut self, topic: B::Hash, message: Vec<u8>, force: bool) {
		self.state_machine.multicast(&mut *self.network, topic, message, force)
	}

	/// Send addressed message to the given peers. The message is not kept or multicast
	/// later on.
	pub fn send_message(&mut self, who: Vec<PeerId>, data: Vec<u8>) {
		for who in &who {
			self.state_machine.send_message(&mut *self.network, who, data.clone());
		}
	}

	/// Notify everyone we're connected to that we have the given block.
	///
	/// Note: this method isn't strictly related to gossiping and should eventually be moved
	/// somewhere else.
	pub fn announce(&self, block: B::Hash, associated_data: Option<Vec<u8>>) {
		self.sync.announce_block(block, associated_data);
	}
}

impl<B: BlockT> Future for GossipEngine<B> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = &mut *self;

		'outer: loop {
			match &mut this.forwarding_state {
				ForwardingState::Idle => {
					let net_event_stream = this.network_event_stream.poll_next_unpin(cx);
					let sync_event_stream = this.sync_event_stream.poll_next_unpin(cx);

					if net_event_stream.is_pending() && sync_event_stream.is_pending() {
						break
					}

					match net_event_stream {
						Poll::Ready(Some(event)) => match event {
							Event::NotificationStreamOpened { remote, protocol, role, .. } =>
								if protocol == this.protocol {
									this.state_machine.new_peer(&mut *this.network, remote, role);
								},
							Event::NotificationStreamClosed { remote, protocol } => {
								if protocol == this.protocol {
									this.state_machine
										.peer_disconnected(&mut *this.network, remote);
								}
							},
							Event::NotificationsReceived { remote, messages } => {
								let messages = messages
									.into_iter()
									.filter_map(|(engine, data)| {
										if engine == this.protocol {
											Some(data.to_vec())
										} else {
											None
										}
									})
									.collect();

								let to_forward = this.state_machine.on_incoming(
									&mut *this.network,
									remote,
									messages,
								);

								this.forwarding_state = ForwardingState::Busy(to_forward.into());
							},
							Event::Dht(_) => {},
						},
						// The network event stream closed. Do the same for [`GossipValidator`].
						Poll::Ready(None) => {
							self.is_terminated = true;
							return Poll::Ready(())
						},
						Poll::Pending => {},
					}

					match sync_event_stream {
						Poll::Ready(Some(event)) => match event {
							SyncEvent::PeerConnected(remote) =>
								this.network.add_set_reserved(remote, this.protocol.clone()),
							SyncEvent::PeerDisconnected(remote) =>
								this.network.remove_set_reserved(remote, this.protocol.clone()),
						},
						// The sync event stream closed. Do the same for [`GossipValidator`].
						Poll::Ready(None) => {
							self.is_terminated = true;
							return Poll::Ready(())
						},
						Poll::Pending => {},
					}
				},
				ForwardingState::Busy(to_forward) => {
					let (topic, notification) = match to_forward.pop_front() {
						Some(n) => n,
						None => {
							this.forwarding_state = ForwardingState::Idle;
							continue
						},
					};

					let sinks = match this.message_sinks.get_mut(&topic) {
						Some(sinks) => sinks,
						None => continue,
					};

					// Make sure all sinks for the given topic are ready.
					for sink in sinks.iter_mut() {
						match sink.poll_ready(cx) {
							Poll::Ready(Ok(())) => {},
							// Receiver has been dropped. Ignore for now, filtered out in (1).
							Poll::Ready(Err(_)) => {},
							Poll::Pending => {
								// Push back onto queue for later.
								to_forward.push_front((topic, notification));
								break 'outer
							},
						}
					}

					// Filter out all closed sinks.
					sinks.retain(|sink| !sink.is_closed()); // (1)

					if sinks.is_empty() {
						this.message_sinks.remove(&topic);
						continue
					}

					trace!(
						target: "gossip",
						"Pushing consensus message to sinks for {}.", topic,
					);

					// Send the notification on each sink.
					for sink in sinks {
						match sink.start_send(notification.clone()) {
							Ok(()) => {},
							Err(e) if e.is_full() => {
								unreachable!("Previously ensured that all sinks are ready; qed.")
							},
							// Receiver got dropped. Will be removed in next iteration (See (1)).
							Err(_) => {},
						}
					}
				},
			}
		}

		while let Poll::Ready(()) = this.periodic_maintenance_interval.poll_unpin(cx) {
			this.periodic_maintenance_interval.reset(PERIODIC_MAINTENANCE_INTERVAL);
			this.state_machine.tick(&mut *this.network);

			this.message_sinks.retain(|_, sinks| {
				sinks.retain(|sink| !sink.is_closed());
				!sinks.is_empty()
			});
		}

		Poll::Pending
	}
}

impl<B: BlockT> futures::future::FusedFuture for GossipEngine<B> {
	fn is_terminated(&self) -> bool {
		self.is_terminated
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{multiaddr::Multiaddr, ValidationResult, ValidatorContext};
	use futures::{
		channel::mpsc::{unbounded, UnboundedSender},
		executor::{block_on, block_on_stream},
		future::poll_fn,
	};
	use quickcheck::{Arbitrary, Gen, QuickCheck};
	use sc_network::{
		config::MultiaddrWithPeerId, NetworkBlock, NetworkEventStream, NetworkNotification,
		NetworkPeers, NotificationSenderError, NotificationSenderT as NotificationSender,
	};
	use sc_network_common::{role::ObservedRole, sync::SyncEventStream};
	use sp_runtime::{
		testing::H256,
		traits::{Block as BlockT, NumberFor},
	};
	use std::{
		collections::HashSet,
		sync::{Arc, Mutex},
	};
	use substrate_test_runtime_client::runtime::Block;

	#[derive(Clone, Default)]
	struct TestNetwork {
		inner: Arc<Mutex<TestNetworkInner>>,
	}

	#[derive(Clone, Default)]
	struct TestNetworkInner {
		event_senders: Vec<UnboundedSender<Event>>,
	}

	impl NetworkPeers for TestNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!();
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!();
		}

		fn add_known_address(&self, _peer_id: PeerId, _addr: Multiaddr) {
			unimplemented!();
		}

		fn report_peer(&self, _who: PeerId, _cost_benefit: ReputationChange) {}

		fn disconnect_peer(&self, _who: PeerId, _protocol: ProtocolName) {
			unimplemented!();
		}

		fn accept_unreserved_peers(&self) {
			unimplemented!();
		}

		fn deny_unreserved_peers(&self) {
			unimplemented!();
		}

		fn add_reserved_peer(&self, _peer: MultiaddrWithPeerId) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_reserved_peer(&self, _peer_id: PeerId) {
			unimplemented!();
		}

		fn set_reserved_peers(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn add_peers_to_reserved_set(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_peers_from_reserved_set(
			&self,
			_protocol: ProtocolName,
			_peers: Vec<PeerId>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn sync_num_connected(&self) -> usize {
			unimplemented!();
		}
	}

	impl NetworkEventStream for TestNetwork {
		fn event_stream(&self, _name: &'static str) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
			let (tx, rx) = unbounded();
			self.inner.lock().unwrap().event_senders.push(tx);

			Box::pin(rx)
		}
	}

	impl NetworkNotification for TestNetwork {
		fn write_notification(&self, _target: PeerId, _protocol: ProtocolName, _message: Vec<u8>) {
			unimplemented!();
		}

		fn notification_sender(
			&self,
			_target: PeerId,
			_protocol: ProtocolName,
		) -> Result<Box<dyn NotificationSender>, NotificationSenderError> {
			unimplemented!();
		}

		fn set_notification_handshake(&self, _protocol: ProtocolName, _handshake: Vec<u8>) {
			unimplemented!();
		}
	}

	impl NetworkBlock<<Block as BlockT>::Hash, NumberFor<Block>> for TestNetwork {
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

	#[derive(Clone, Default)]
	struct TestSync {
		inner: Arc<Mutex<TestSyncInner>>,
	}

	#[derive(Clone, Default)]
	struct TestSyncInner {
		event_senders: Vec<UnboundedSender<SyncEvent>>,
	}

	impl SyncEventStream for TestSync {
		fn event_stream(
			&self,
			_name: &'static str,
		) -> Pin<Box<dyn Stream<Item = SyncEvent> + Send>> {
			let (tx, rx) = unbounded();
			self.inner.lock().unwrap().event_senders.push(tx);

			Box::pin(rx)
		}
	}

	impl NetworkBlock<<Block as BlockT>::Hash, NumberFor<Block>> for TestSync {
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

	/// Regression test for the case where the `GossipEngine.network_event_stream` closes. One
	/// should not ignore a `Poll::Ready(None)` as `poll_next_unpin` will panic on subsequent calls.
	///
	/// See https://github.com/paritytech/substrate/issues/5000 for details.
	#[test]
	fn returns_when_network_event_stream_closes() {
		let network = TestNetwork::default();
		let sync = Arc::new(TestSync::default());
		let mut gossip_engine = GossipEngine::<Block>::new(
			network.clone(),
			sync,
			"/my_protocol",
			Arc::new(AllowAll {}),
			None,
		);

		// Drop network event stream sender side.
		drop(network.inner.lock().unwrap().event_senders.pop());

		block_on(poll_fn(move |ctx| {
			if let Poll::Pending = gossip_engine.poll_unpin(ctx) {
				panic!(
					"Expected gossip engine to finish on first poll, given that \
					 `GossipEngine.network_event_stream` closes right away."
				)
			}
			Poll::Ready(())
		}))
	}

	#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
	async fn keeps_multiple_subscribers_per_topic_updated_with_both_old_and_new_messages() {
		let topic = H256::default();
		let protocol = ProtocolName::from("/my_protocol");
		let remote_peer = PeerId::random();
		let network = TestNetwork::default();
		let sync = Arc::new(TestSync::default());

		let mut gossip_engine = GossipEngine::<Block>::new(
			network.clone(),
			sync.clone(),
			protocol.clone(),
			Arc::new(AllowAll {}),
			None,
		);

		let mut event_sender = network.inner.lock().unwrap().event_senders.pop().unwrap();

		// Register the remote peer.
		event_sender
			.start_send(Event::NotificationStreamOpened {
				remote: remote_peer,
				protocol: protocol.clone(),
				negotiated_fallback: None,
				role: ObservedRole::Authority,
				received_handshake: vec![],
			})
			.expect("Event stream is unbounded; qed.");

		let messages = vec![vec![1], vec![2]];
		let events = messages
			.iter()
			.cloned()
			.map(|m| Event::NotificationsReceived {
				remote: remote_peer,
				messages: vec![(protocol.clone(), m.into())],
			})
			.collect::<Vec<_>>();

		// Send first event before subscribing.
		event_sender
			.start_send(events[0].clone())
			.expect("Event stream is unbounded; qed.");

		let mut subscribers = vec![];
		for _ in 0..2 {
			subscribers.push(gossip_engine.messages_for(topic));
		}

		// Send second event after subscribing.
		event_sender
			.start_send(events[1].clone())
			.expect("Event stream is unbounded; qed.");

		tokio::spawn(gossip_engine);

		// Note: `block_on_stream()`-derived iterator will block the current thread,
		//       so we need a `multi_thread` `tokio::test` runtime flavor.
		let mut subscribers =
			subscribers.into_iter().map(|s| block_on_stream(s)).collect::<Vec<_>>();

		// Expect each subscriber to receive both events.
		for message in messages {
			for subscriber in subscribers.iter_mut() {
				assert_eq!(
					subscriber.next(),
					Some(TopicNotification { message: message.clone(), sender: Some(remote_peer) }),
				);
			}
		}
	}

	#[test]
	fn forwarding_to_different_size_and_topic_channels() {
		#[derive(Clone, Debug)]
		struct ChannelLengthAndTopic {
			length: usize,
			topic: H256,
		}

		impl Arbitrary for ChannelLengthAndTopic {
			fn arbitrary(g: &mut Gen) -> Self {
				let possible_length = (0..100).collect::<Vec<usize>>();
				let possible_topics = (0..10).collect::<Vec<u64>>();
				Self {
					length: *g.choose(&possible_length).unwrap(),
					// Make sure channel topics and message topics overlap by choosing a small
					// range.
					topic: H256::from_low_u64_ne(*g.choose(&possible_topics).unwrap()),
				}
			}
		}

		#[derive(Clone, Debug)]
		struct Message {
			topic: H256,
		}

		impl Arbitrary for Message {
			fn arbitrary(g: &mut Gen) -> Self {
				let possible_topics = (0..10).collect::<Vec<u64>>();
				Self {
					// Make sure channel topics and message topics overlap by choosing a small
					// range.
					topic: H256::from_low_u64_ne(*g.choose(&possible_topics).unwrap()),
				}
			}
		}

		/// Validator that always returns `ProcessAndKeep` interpreting the first 32 bytes of data
		/// as the message topic.
		struct TestValidator;

		impl Validator<Block> for TestValidator {
			fn validate(
				&self,
				_context: &mut dyn ValidatorContext<Block>,
				_sender: &PeerId,
				data: &[u8],
			) -> ValidationResult<H256> {
				ValidationResult::ProcessAndKeep(H256::from_slice(&data[0..32]))
			}
		}

		fn prop(channels: Vec<ChannelLengthAndTopic>, notifications: Vec<Vec<Message>>) {
			let protocol = ProtocolName::from("/my_protocol");
			let remote_peer = PeerId::random();
			let network = TestNetwork::default();
			let sync = Arc::new(TestSync::default());

			let num_channels_per_topic = channels.iter().fold(
				HashMap::new(),
				|mut acc, ChannelLengthAndTopic { topic, .. }| {
					acc.entry(topic).and_modify(|e| *e += 1).or_insert(1);
					acc
				},
			);

			let expected_msgs_per_topic_all_chan = notifications
				.iter()
				.fold(HashMap::new(), |mut acc, messages| {
					for message in messages {
						acc.entry(message.topic).and_modify(|e| *e += 1).or_insert(1);
					}
					acc
				})
				.into_iter()
				// Messages are cloned for each channel with the corresponding topic, thus multiply
				// with the amount of channels per topic. If there is no channel for a given topic,
				// don't expect any messages for the topic to be received.
				.map(|(topic, num)| (topic, num_channels_per_topic.get(&topic).unwrap_or(&0) * num))
				.collect::<HashMap<H256, _>>();

			let mut gossip_engine = GossipEngine::<Block>::new(
				network.clone(),
				sync.clone(),
				protocol.clone(),
				Arc::new(TestValidator {}),
				None,
			);

			// Create channels.
			let (txs, mut rxs) = channels
				.iter()
				.map(|ChannelLengthAndTopic { length, topic }| (*topic, channel(*length)))
				.fold((vec![], vec![]), |mut acc, (topic, (tx, rx))| {
					acc.0.push((topic, tx));
					acc.1.push((topic, rx));
					acc
				});

			// Insert sender sides into `gossip_engine`.
			for (topic, tx) in txs {
				match gossip_engine.message_sinks.get_mut(&topic) {
					Some(entry) => entry.push(tx),
					None => {
						gossip_engine.message_sinks.insert(topic, vec![tx]);
					},
				}
			}

			let mut event_sender = network.inner.lock().unwrap().event_senders.pop().unwrap();

			// Register the remote peer.
			event_sender
				.start_send(Event::NotificationStreamOpened {
					remote: remote_peer,
					protocol: protocol.clone(),
					negotiated_fallback: None,
					role: ObservedRole::Authority,
					received_handshake: vec![],
				})
				.expect("Event stream is unbounded; qed.");

			// Send messages into the network event stream.
			for (i_notification, messages) in notifications.iter().enumerate() {
				let messages = messages
					.into_iter()
					.enumerate()
					.map(|(i_message, Message { topic })| {
						// Embed the topic in the first 256 bytes of the message to be extracted by
						// the [`TestValidator`] later on.
						let mut message = topic.as_bytes().to_vec();

						// Make sure the message is unique via `i_notification` and `i_message` to
						// ensure [`ConsensusBridge`] does not deduplicate it.
						message.push(i_notification.try_into().unwrap());
						message.push(i_message.try_into().unwrap());

						(protocol.clone(), message.into())
					})
					.collect();

				event_sender
					.start_send(Event::NotificationsReceived { remote: remote_peer, messages })
					.expect("Event stream is unbounded; qed.");
			}

			let mut received_msgs_per_topic_all_chan = HashMap::<H256, _>::new();

			// Poll both gossip engine and each receiver and track the amount of received messages.
			block_on(poll_fn(|cx| {
				loop {
					if let Poll::Ready(()) = gossip_engine.poll_unpin(cx) {
						unreachable!(
							"Event stream sender side is not dropped, thus gossip engine does not \
							 terminate",
						);
					}

					let mut progress = false;

					for (topic, rx) in rxs.iter_mut() {
						match rx.poll_next_unpin(cx) {
							Poll::Ready(Some(_)) => {
								progress = true;
								received_msgs_per_topic_all_chan
									.entry(*topic)
									.and_modify(|e| *e += 1)
									.or_insert(1);
							},
							Poll::Ready(None) => {
								unreachable!("Sender side of channel is never dropped")
							},
							Poll::Pending => {},
						}
					}

					if !progress {
						break
					}
				}
				Poll::Ready(())
			}));

			// Compare amount of expected messages with amount of received messages.
			for (expected_topic, expected_num) in expected_msgs_per_topic_all_chan.iter() {
				assert_eq!(
					received_msgs_per_topic_all_chan.get(&expected_topic).unwrap_or(&0),
					expected_num,
				);
			}
			for (received_topic, received_num) in expected_msgs_per_topic_all_chan.iter() {
				assert_eq!(
					expected_msgs_per_topic_all_chan.get(&received_topic).unwrap_or(&0),
					received_num,
				);
			}
		}

		// Past regressions.
		prop(vec![], vec![vec![Message { topic: H256::default() }]]);
		prop(
			vec![ChannelLengthAndTopic { length: 71, topic: H256::default() }],
			vec![vec![Message { topic: H256::default() }]],
		);

		QuickCheck::new().quickcheck(prop as fn(_, _))
	}
}
