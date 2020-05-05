// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::{Network, Validator};
use crate::state_machine::{ConsensusGossip, TopicNotification, PERIODIC_MAINTENANCE_INTERVAL};

use sc_network::{Event, ReputationChange};

use futures::prelude::*;
use libp2p::PeerId;
use log::trace;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};
use std::{
	borrow::Cow,
	collections::{HashMap, hash_map::Entry},
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
};

/// Wraps around an implementation of the `Network` crate and provides gossiping capabilities on
/// top of it.
pub struct GossipEngine<B: BlockT> {
	state_machine: ConsensusGossip<B>,
	network: Box<dyn Network<B> + Send>,
	periodic_maintenance_interval: futures_timer::Delay,
	engine_id: ConsensusEngineId,

	/// Incoming events from the network.
	network_event_stream: Pin<Box<dyn Stream<Item = Event> + Send>>,
	/// Outgoing events to the consumer.
	message_sinks: HashMap<B::Hash, Vec<TracingUnboundedSender<TopicNotification>>>,
}

impl<B: BlockT> Unpin for GossipEngine<B> {}

impl<B: BlockT> GossipEngine<B> {
	/// Create a new instance.
	pub fn new<N: Network<B> + Send + Clone + 'static>(
		network: N,
		engine_id: ConsensusEngineId,
		protocol_name: impl Into<Cow<'static, [u8]>>,
		validator: Arc<dyn Validator<B>>,
	) -> Self where B: 'static {
		// We grab the event stream before registering the notifications protocol, otherwise we
		// might miss events.
		let network_event_stream = network.event_stream();
		network.register_notifications_protocol(engine_id, protocol_name.into());

		GossipEngine {
			state_machine: ConsensusGossip::new(validator, engine_id),
			network: Box::new(network),
			periodic_maintenance_interval: futures_timer::Delay::new(PERIODIC_MAINTENANCE_INTERVAL),
			engine_id,

			network_event_stream,
			message_sinks: HashMap::new(),
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
	pub fn register_gossip_message(
		&mut self,
		topic: B::Hash,
		message: Vec<u8>,
	) {
		self.state_machine.register_message(topic, message);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.state_machine.broadcast_topic(&mut *self.network, topic, force);
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile).
	pub fn messages_for(&mut self, topic: B::Hash)
		-> TracingUnboundedReceiver<TopicNotification>
	{
		let (tx, rx) = tracing_unbounded("mpsc_gossip_messages_for");

		for notification in self.state_machine.messages_for(topic) {
			tx.unbounded_send(notification).expect("receiver known to be live; qed");
		}

		self.message_sinks.entry(topic).or_default().push(tx);

		rx
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&mut self,
		who: &PeerId,
		topic: B::Hash,
		force: bool
	) {
		self.state_machine.send_topic(&mut *self.network, who, topic, force)
	}

	/// Multicast a message to all peers.
	pub fn gossip_message(
		&mut self,
		topic: B::Hash,
		message: Vec<u8>,
		force: bool,
	) {
		self.state_machine.multicast(&mut *self.network, topic, message, force)
	}

	/// Send addressed message to the given peers. The message is not kept or multicast
	/// later on.
	pub fn send_message(&mut self, who: Vec<sc_network::PeerId>, data: Vec<u8>) {
		for who in &who {
			self.state_machine.send_message(&mut *self.network, who, data.clone());
		}
	}

	/// Notify everyone we're connected to that we have the given block.
	///
	/// Note: this method isn't strictly related to gossiping and should eventually be moved
	/// somewhere else.
	pub fn announce(&self, block: B::Hash, associated_data: Vec<u8>) {
		self.network.announce(block, associated_data);
	}
}

impl<B: BlockT> Future for GossipEngine<B> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = &mut *self;

		loop {
			match this.network_event_stream.poll_next_unpin(cx) {
				Poll::Ready(Some(event)) => match event {
					Event::NotificationStreamOpened { remote, engine_id: msg_engine_id, role } => {
						if msg_engine_id != this.engine_id {
							continue;
						}
						this.state_machine.new_peer(&mut *this.network, remote, role);
					}
					Event::NotificationStreamClosed { remote, engine_id: msg_engine_id } => {
						if msg_engine_id != this.engine_id {
							continue;
						}
						this.state_machine.peer_disconnected(&mut *this.network, remote);
					},
					Event::NotificationsReceived { remote, messages } => {
						let messages = messages.into_iter().filter_map(|(engine, data)| {
							if engine == this.engine_id {
								Some(data.to_vec())
							} else {
								None
							}
						}).collect();

						let to_forward = this.state_machine.on_incoming(
							&mut *this.network,
							remote,
							messages,
						);

						for (topic, notification) in to_forward {
							if let Entry::Occupied(mut entry) = this.message_sinks.entry(topic) {
								trace!(
									target: "gossip",
									"Pushing consensus message to sinks for {}.", topic,
								);
								entry.get_mut().retain(move |sink| {
									if let Err(e) = sink.unbounded_send(notification.clone()) {
										trace!(
											target: "gossip",
											"Error broadcasting message notification: {:?}", e,
										);
									}
									!sink.is_closed()
								});
								if entry.get().is_empty() {
									entry.remove_entry();
								}
							}
						}
					},
					Event::Dht(_) => {}
				}
				// The network event stream closed. Do the same for [`GossipValidator`].
				Poll::Ready(None) => return Poll::Ready(()),
				Poll::Pending => break,
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

#[cfg(test)]
mod tests {
	use async_std::task::spawn;
	use crate::{ValidationResult, ValidatorContext};
	use futures::{channel::mpsc::{channel, Sender}, executor::block_on_stream};
	use sc_network::ObservedRole;
	use sp_runtime::{testing::H256, traits::{Block as BlockT}};
	use std::sync::{Arc, Mutex};
	use substrate_test_runtime_client::runtime::Block;
	use super::*;

	#[derive(Clone, Default)]
	struct TestNetwork {
		inner: Arc<Mutex<TestNetworkInner>>,
	}

	#[derive(Clone, Default)]
	struct TestNetworkInner {
		event_senders: Vec<Sender<Event>>,
	}

	impl<B: BlockT> Network<B> for TestNetwork {
		fn event_stream(&self) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
			let (tx, rx) = channel(100);
			self.inner.lock().unwrap().event_senders.push(tx);

			Box::pin(rx)
		}

		fn report_peer(&self, _: PeerId, _: ReputationChange) {
		}

		fn disconnect_peer(&self, _: PeerId) {
			unimplemented!();
		}

		fn write_notification(&self, _: PeerId, _: ConsensusEngineId, _: Vec<u8>) {
			unimplemented!();
		}

		fn register_notifications_protocol(&self, _: ConsensusEngineId, _: Cow<'static, [u8]>) {}

		fn announce(&self, _: B::Hash, _: Vec<u8>) {
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
		let mut gossip_engine = GossipEngine::<Block>::new(
			network.clone(),
			[1, 2, 3, 4],
			"my_protocol".as_bytes(),
			Arc::new(AllowAll{}),
		);

		// Drop network event stream sender side.
		drop(network.inner.lock().unwrap().event_senders.pop());

		futures::executor::block_on(futures::future::poll_fn(move |ctx| {
			if let Poll::Pending = gossip_engine.poll_unpin(ctx) {
				panic!(
					"Expected gossip engine to finish on first poll, given that \
					 `GossipEngine.network_event_stream` closes right away."
				)
			}
			Poll::Ready(())
		}))
	}

	#[test]
	fn keeps_multiple_subscribers_per_topic_updated_with_both_old_and_new_messages() {
		let topic = H256::default();
		let engine_id = [1, 2, 3, 4];
		let remote_peer = PeerId::random();
		let network = TestNetwork::default();

		let mut gossip_engine = GossipEngine::<Block>::new(
			network.clone(),
			engine_id.clone(),
			"my_protocol".as_bytes(),
			Arc::new(AllowAll{}),
		);

		let mut event_sender = network.inner.lock()
			.unwrap()
			.event_senders
			.pop()
			.unwrap();

		// Register the remote peer.
		event_sender.start_send(
			Event::NotificationStreamOpened {
				remote: remote_peer.clone(),
				engine_id: engine_id.clone(),
				role: ObservedRole::Authority,
			}
		).unwrap();

		let messages = vec![vec![1], vec![2]];
		let events = messages.iter().cloned().map(|m| {
			Event::NotificationsReceived {
				remote: remote_peer.clone(),
				messages: vec![(engine_id, m.into())]
			}
		}).collect::<Vec<_>>();

		// Send first event before subscribing.
		event_sender.start_send(events[0].clone()).unwrap();

		let mut subscribers = vec![];
		for _ in 0..2 {
			subscribers.push(gossip_engine.messages_for(topic));
		}

		// Send second event after subscribing.
		event_sender.start_send(events[1].clone()).unwrap();

		spawn(gossip_engine);

		let mut subscribers = subscribers.into_iter()
			.map(|s| block_on_stream(s))
			.collect::<Vec<_>>();

		// Expect each subscriber to receive both events.
		for message in messages {
			for subscriber in subscribers.iter_mut() {
				assert_eq!(
					subscriber.next(),
					Some(TopicNotification {
						message: message.clone(),
						sender: Some(remote_peer.clone()),
					}),
				);
			}
		}
	}
}
