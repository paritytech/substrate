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

use futures03::{prelude::*, channel::mpsc, compat::Compat01As03};
use libp2p::{Multiaddr, PeerId};
use libp2p::core::{ConnectedPoint, nodes::Substream, muxing::StreamMuxerBox};
use libp2p::swarm::{ProtocolsHandler, IntoProtocolsHandler};
use libp2p::swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use primitives::storage::StorageKey;
use consensus::{
	BlockOrigin,
	block_validation::BlockAnnounceValidator,
	import_queue::{BlockImportResult, BlockImportError, IncomingBlock, Origin}
};
use codec::{Decode, Encode};
use sr_primitives::{generic::BlockId, ConsensusEngineId, Justification};
use sr_primitives::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, One, Zero,
	CheckedSub, SaturatedConversion
};
use crate::protocol::Context;
use crate::protocol::message::{BlockAnnounce, BlockAttributes, Direction, FromBlock, Message, RequestId};
use crate::protocol::message::generic::{Message as GenericMessage, ConsensusMessage};
use crate::protocol::specialization::NetworkSpecialization;
use crate::consensus_gossip::state_machine::{ConsensusGossip, MessageRecipient as GossipMessageRecipient, Validator, TopicNotification};
use crate::service::{NetworkService, ExHashT};
use std::borrow::Cow;
use std::sync::Arc;

pub struct Gossip<B: BlockT> {
	state_machine: ConsensusGossip<B>,
	context: Box<dyn Context<B> + Send>,
}

impl<B: BlockT> Gossip<B> {
	/// Create a new instance.
	pub fn new<S: NetworkSpecialization<B>, H: ExHashT>(
		network_service: NetworkService<B, S, H>,
		proto_name: impl Into<Cow<'static, [u8]>>,
		engine_id: ConsensusEngineId,
	) -> Self {
		let state_machine = ConsensusGossip::new();
		let context = Box::new(ContextOverService { network_service });

		async_std::task::spawn(async {
			let mut stream = Compat01As03::new(network_service.events_stream());
			while let Some(event) = stream.next().await {
				match event {
					_ => unimplemented!()
				}
			}
		});

		Gossip {
			state_machine,
			context,
		}
	}

	/// Closes all notification streams.
	pub fn abort(&mut self) {
		self.state_machine.abort();
	}

	/// Register message validator for a message type.
	pub fn register_validator(
		&mut self,
		protocol: &mut dyn Context<B>,
		engine_id: ConsensusEngineId,
		validator: Arc<dyn Validator<B>>
	) {
		unimplemented!()		// TODO:
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
		self.state_machine.register_message(topic, message);
	}

	/// Broadcast all messages with given topic.
	pub fn broadcast_topic(&mut self, topic: B::Hash, force: bool) {
		self.state_machine.broadcast_topic(topic, force);
	}

	/// Get data of valid, incoming messages for a topic (but might have expired meanwhile)
	pub fn messages_for(&mut self, engine_id: ConsensusEngineId, topic: B::Hash)
		-> mpsc::UnboundedReceiver<TopicNotification>
	{
		self.state_machine.messages_for(&mut context, engine_id, topic)
	}

	/// Send all messages with given topic to a peer.
	pub fn send_topic(
		&mut self,
		who: &PeerId,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		force: bool
	) {
		self.send_topic(who, topic, engine_id, force)
	}

	/// Multicast a message to all peers.
	pub fn multicast(
		&mut self,
		topic: B::Hash,
		message: ConsensusMessage,
		force: bool,
	) {
		self.state_machine.multicast(topic, message, force)
	}

	/// Send addressed message to a peer. The message is not kept or multicast
	/// later on.
	pub fn send_message(
		&mut self,
		who: &PeerId,
		message: ConsensusMessage,
	) {
		self.state_machine.send_message(&mut context, who, message);
	}

	// TODO: bad API?
	pub async fn process() {

	}
}

struct ContextOverService<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	network_service: NetworkService<B, S, H>,
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Context<B> for ContextOverService<B, S, H> {
	fn report_peer(&mut self, who: PeerId, reputation: i32) {
		self.peerset_handle.report_peer(who, reputation)
	}

	fn disconnect_peer(&mut self, who: PeerId) {
		self.behaviour.disconnect_peer(&who)
	}

	fn send_consensus(&mut self, who: PeerId, messages: Vec<ConsensusMessage>) {
		// TODO: send batch
		for message in messages {
			self.network_service.write_notif(who, message);
		}
	}

	fn send_chain_specific(&mut self, who: PeerId, message: Vec<u8>) {
		unreachable!()		// TODO: handle that
	}
}

