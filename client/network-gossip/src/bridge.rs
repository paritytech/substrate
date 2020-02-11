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

use sc_network::message::generic::ConsensusMessage;
use sc_network::{Event, ReputationChange};

use futures::{prelude::*, channel::mpsc, compat::Compat01As03};
use futures01::stream::Stream as Stream01;
use libp2p::PeerId;
use parking_lot::Mutex;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use std::{pin::Pin, sync::Arc, task::{Context, Poll}};

/// Wraps around an implementation of the `Network` crate and provides gossiping capabilities on
/// top of it.
pub struct GossipEngine<B: BlockT> {
	inner: Arc<Mutex<GossipEngineInner<B>>>,
	engine_id: ConsensusEngineId,
}

struct GossipEngineInner<B: BlockT> {
	state_machine: ConsensusGossip<B>,
	network: Box<dyn Network<B> + Send>,
	periodic_maintenance_interval: futures_timer::Delay,
	network_event_stream: Compat01As03<Box<dyn Stream01<Error = (), Item = Event> + Send>>,
	engine_id: ConsensusEngineId,
}

impl<B: BlockT> Unpin for GossipEngineInner<B> {}

impl<B: BlockT> GossipEngine<B> {
	/// Create a new instance.
	pub fn new<N: Network<B> + Send + Clone + 'static>(
		mut network: N,
		engine_id: ConsensusEngineId,
		validator: Arc<dyn Validator<B>>,
	) -> Self where B: 'static {
		let mut state_machine = ConsensusGossip::new();

		// We grab the event stream before registering the notifications protocol, otherwise we
		// might miss events.
		let network_event_stream = network.event_stream();

		network.register_notifications_protocol(engine_id);
		state_machine.register_validator(&mut network, engine_id, validator);

		let inner = Arc::new(Mutex::new(GossipEngineInner {
			state_machine,
			network: Box::new(network),
			periodic_maintenance_interval: futures_timer::Delay::new(PERIODIC_MAINTENANCE_INTERVAL),
			network_event_stream: Compat01As03::new(network_event_stream),
			engine_id,
		}));

		let gossip_engine = GossipEngine {
			inner: inner.clone(),
			engine_id,
		};

		gossip_engine
	}

	pub fn report(&self, who: PeerId, reputation: ReputationChange) {
		self.inner.lock().network.report_peer(who, reputation);
	}

	/// Registers a message without propagating it to any peers. The message
	/// becomes available to new peers or when the service is asked to gossip
	/// the message's topic. No validation is performed on the message, if the
	/// message is already expired it should be dropped on the next garbage
	/// collection.
	pub fn register_gossip_message(
		&self,
		topic: B::Hash,
		message: Vec<u8>,
	) {
		let message = ConsensusMessage {
			engine_id: self.engine_id,
			data: message,
		};

		self.inner.lock().state_machine.register_message(topic, message);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&self, topic: B::Hash, force: bool) {
		let mut inner = self.inner.lock();
		let inner = &mut *inner;
		inner.state_machine.broadcast_topic(&mut *inner.network, topic, force);
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile).
	pub fn messages_for(&self, topic: B::Hash)
		-> mpsc::UnboundedReceiver<TopicNotification>
	{
		self.inner.lock().state_machine.messages_for(self.engine_id, topic)
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&self,
		who: &PeerId,
		topic: B::Hash,
		force: bool
	) {
		let mut inner = self.inner.lock();
		let inner = &mut *inner;
		inner.state_machine.send_topic(&mut *inner.network, who, topic, self.engine_id, force)
	}

	/// Multicast a message to all peers.
	pub fn gossip_message(
		&self,
		topic: B::Hash,
		message: Vec<u8>,
		force: bool,
	) {
		let message = ConsensusMessage {
			engine_id: self.engine_id,
			data: message,
		};

		let mut inner = self.inner.lock();
		let inner = &mut *inner;
		inner.state_machine.multicast(&mut *inner.network, topic, message, force)
	}

	/// Send addressed message to the given peers. The message is not kept or multicast
	/// later on.
	pub fn send_message(&self, who: Vec<sc_network::PeerId>, data: Vec<u8>) {
		let mut inner = self.inner.lock();
		let inner = &mut *inner;

		for who in &who {
			inner.state_machine.send_message(&mut *inner.network, who, ConsensusMessage {
				engine_id: self.engine_id,
				data: data.clone(),
			});
		}
	}

	/// Notify everyone we're connected to that we have the given block.
	///
	/// Note: this method isn't strictly related to gossiping and should eventually be moved
	/// somewhere else.
	pub fn announce(&self, block: B::Hash, associated_data: Vec<u8>) {
		self.inner.lock().network.announce(block, associated_data);
	}
}

impl<B: BlockT> Future for GossipEngine<B> {
	type Output = ();

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		self.inner.lock().poll_unpin(cx)
	}
}

impl<B: BlockT> Future for GossipEngineInner<B> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = &mut *self;

		while let Poll::Ready(Some(Ok(event))) = this.network_event_stream.poll_next_unpin(cx) {
			match event {
				Event::NotificationStreamOpened { remote, engine_id: msg_engine_id, roles } => {
					if msg_engine_id != this.engine_id {
						continue;
					}
					this.state_machine.new_peer(&mut *this.network, remote, roles);
				}
				Event::NotificationStreamClosed { remote, engine_id: msg_engine_id } => {
					if msg_engine_id != this.engine_id {
						continue;
					}
					this.state_machine.peer_disconnected(&mut *this.network, remote);
				},
				Event::NotificationsReceived { remote, messages } => {
					let engine_id = this.engine_id.clone();
					this.state_machine.on_incoming(
						&mut *this.network,
						remote,
						messages.into_iter()
							.filter_map(|(engine, data)| if engine == engine_id {
								Some(ConsensusMessage { engine_id: engine, data: data.to_vec() })
							} else { None })
							.collect()
					);
				},
				Event::Dht(_) => {}
			}
		}

		while let Poll::Ready(()) = this.periodic_maintenance_interval.poll_unpin(cx) {
			this.periodic_maintenance_interval.reset(PERIODIC_MAINTENANCE_INTERVAL);
			this.state_machine.tick(&mut *this.network);
		}

		Poll::Pending
	}
}

impl<B: BlockT> Clone for GossipEngine<B> {
	fn clone(&self) -> Self {
		GossipEngine {
			inner: self.inner.clone(),
			engine_id: self.engine_id.clone(),
		}
	}
}
