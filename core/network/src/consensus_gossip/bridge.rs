// Copyright 2019 Parity Technologies (UK) Ltd.
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

use crate::protocol::Context;
use crate::protocol::message::generic::ConsensusMessage;
use crate::protocol::specialization::NetworkSpecialization;
use crate::consensus_gossip::state_machine::{ConsensusGossip, Validator, TopicNotification};
use crate::service::{NetworkService, ExHashT};
use crate::{Event, config::Roles};

use futures03::{prelude::*, channel::mpsc, compat::Compat01As03};
use libp2p::PeerId;
use parking_lot::Mutex;
use sr_primitives::{traits::{Block as BlockT, Header as HeaderT}, ConsensusEngineId};
use std::{borrow::Cow, sync::Arc, time::Duration};

pub struct GossipEngine<B: BlockT> {
	inner: Arc<Mutex<GossipEngineInner<B>>>,
}

struct GossipEngineInner<B: BlockT> {
	state_machine: ConsensusGossip<B>,
	context: Box<dyn Context<B> + Send>,
}

impl<B: BlockT> GossipEngine<B> {
	/// Create a new instance.
	pub fn new<S: NetworkSpecialization<B>, H: ExHashT>(
		network_service: NetworkService<B, S, H>,
		proto_name: impl Into<Cow<'static, [u8]>>,
		engine_id: ConsensusEngineId,
		validator: Arc<dyn Validator<B>>,
	) -> Self where B: 'static, S: 'static, H: 'static {
		let proto_name = proto_name.into();

		let mut state_machine = ConsensusGossip::new();
		let mut context = Box::new(ContextOverService {
			network_service: network_service.clone(),
			proto_name: proto_name.clone(),
		});

		state_machine.register_validator(&mut *context, engine_id, validator);

		let inner = Arc::new(Mutex::new(GossipEngineInner {
			state_machine,
			context,
		}));

		let gossip_engine = GossipEngine {
			inner: inner.clone(),
		};

		async_std::task::spawn({
			let inner = Arc::downgrade(&inner);
			async move {
				loop {
					async_std::task::sleep(Duration::from_millis(1100)).await;
					if let Some(inner) = inner.upgrade() {
						let mut inner = inner.lock();
						let mut inner = &mut *inner;
						inner.state_machine.tick(&mut *inner.context);
					} else {
						break;
					}
				}
			}
		});

		async_std::task::spawn(async move {
			let mut stream = Compat01As03::new(network_service.events_stream());
			while let Some(Ok(event)) = stream.next().await {
				match event {
					Event::NotifOpened { remote, proto_name } => {
						if proto_name != proto_name {
							continue;
						}
						let mut inner = inner.lock();
						let mut inner = &mut *inner;
						// TODO: for now we hard-code the roles to FULL; fix that
						inner.state_machine.new_peer(&mut *inner.context, remote, Roles::FULL);
					}
					Event::NotifClosed { remote, proto_name } => {
						if proto_name != proto_name {
							continue;
						}
						let mut inner = inner.lock();
						let mut inner = &mut *inner;
						inner.state_machine.peer_disconnected(&mut *inner.context, remote);
					},
					Event::NotifMessages { remote, messages } => {
						let mut inner = inner.lock();
						let mut inner = &mut *inner;
						inner.state_machine.on_incoming(
							&mut *inner.context,
							remote,
							messages.into_iter()
								.filter_map(|(proto, data)| if proto == proto_name {
									Some(ConsensusMessage { engine_id, data })
								} else { None })
								.collect()
						);
					},
					Event::Dht(_) => {}
				}
			}
		});

		gossip_engine
	}

	/// Closes all notification streams.
	pub fn abort(&self) {
		self.inner.lock().state_machine.abort();
	}

	/// Registers a message without propagating it to any peers. The message
	/// becomes available to new peers or when the service is asked to GossipEngine
	/// the message's topic. No validation is performed on the message, if the
	/// message is already expired it should be dropped on the next garbage
	/// collection.
	pub fn register_message(
		&self,
		topic: B::Hash,
		message: ConsensusMessage,
	) {
		self.inner.lock().state_machine.register_message(topic, message);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&self, topic: B::Hash, force: bool) {
		let mut inner = self.inner.lock();
		let mut inner = &mut *inner;
		inner.state_machine.broadcast_topic(&mut *inner.context, topic, force);
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile)
	pub fn messages_for(&self, engine_id: ConsensusEngineId, topic: B::Hash)
		-> mpsc::UnboundedReceiver<TopicNotification>
	{
		self.inner.lock().state_machine.messages_for(engine_id, topic)
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&self,
		who: &PeerId,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		force: bool
	) {
		let mut inner = self.inner.lock();
		let mut inner = &mut *inner;
		inner.state_machine.send_topic(&mut *inner.context, who, topic, engine_id, force)
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&self,
		topic: B::Hash,
		message: ConsensusMessage,
		force: bool,
	) {
		let mut inner = self.inner.lock();
		let mut inner = &mut *inner;
		inner.state_machine.multicast(&mut *inner.context, topic, message, force)
	}

	/// Send addressed message to a peer. The message is not kept or multicast
	/// later on.
	pub fn send_message(
		&self,
		who: &PeerId,
		message: ConsensusMessage,
	) {
		let mut inner = self.inner.lock();
		let mut inner = &mut *inner;
		inner.state_machine.send_message(&mut *inner.context, who, message);
	}

	// TODO: bad API?
	pub async fn process() {

	}
}

impl<B: BlockT> Clone for GossipEngine<B> {
	fn clone(&self) -> Self {
		GossipEngine {
			inner: self.inner.clone()
		}
	}
}

struct ContextOverService<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	network_service: NetworkService<B, S, H>,
	proto_name: Cow<'static, [u8]>,
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Context<B> for ContextOverService<B, S, H> {
	fn report_peer(&mut self, who: PeerId, reputation: i32) {
		unimplemented!() // self.peerset_handle.report_peer(who, reputation)
	}

	fn disconnect_peer(&mut self, who: PeerId) {
		unimplemented!() // self.behaviour.disconnect_peer(&who)
	}

	fn send_consensus(&mut self, who: PeerId, messages: Vec<ConsensusMessage>) {
		// TODO: send batch
		for message in messages {
			self.network_service.write_notif(who.clone(), self.proto_name.clone(), message);
		}
	}

	fn send_chain_specific(&mut self, who: PeerId, message: Vec<u8>) {
		unreachable!()		// TODO: handle that
	}
}

