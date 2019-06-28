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

//! Implementation of libp2p's `NetworkBehaviour` trait that handles everything Substrate-specific.

use crate::{ExHashT, DiscoveryNetBehaviour, ProtocolId};
use crate::custom_proto::{CustomProto, CustomProtoOut};
use crate::chain::{Client, FinalityProofProvider};
use crate::protocol::{self, event::Event, CustomMessageOutcome, Protocol, ProtocolConfig, sync::SyncState};
use crate::protocol::{PeerInfo, NetworkOut, message::Message, on_demand::RequestData};
use crate::protocol::consensus_gossip::MessageRecipient as GossipMessageRecipient;
use crate::protocol::specialization::NetworkSpecialization;
use crate::service::TransactionPool;

use client::light::fetcher::FetchChecker;
use futures::prelude::*;
use consensus::import_queue::SharedFinalityProofRequestBuilder;
use log::debug;
use libp2p::{PeerId, Multiaddr};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use libp2p::core::{nodes::Substream, muxing::StreamMuxerBox};
use libp2p::core::protocols_handler::{ProtocolsHandler, IntoProtocolsHandler};
use runtime_primitives::{traits::{Block as BlockT, NumberFor}, ConsensusEngineId};
use std::sync::Arc;

/// Implementation of `NetworkBehaviour` that handles everything related to Substrate and Polkadot.
pub struct ProtocolBehaviour<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	/// Handles opening the unique substream and sending and receiving raw messages.
	behaviour: CustomProto<Message<B>, Substream<StreamMuxerBox>>,
	/// Handles the logic behind the raw messages that we receive.
	protocol: Protocol<B, S, H>,
	/// Used to report reputation changes.
	peerset_handle: peerset::PeersetHandle,
	transaction_pool: Arc<dyn TransactionPool<H, B>>,
	/// When asked for a proof of finality, we use this struct to build one.
	finality_proof_provider: Option<Arc<dyn FinalityProofProvider<B>>>,
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> ProtocolBehaviour<B, S, H> {
	/// Builds a new `ProtocolBehaviour`.
	pub fn new(
		config: ProtocolConfig,
		chain: Arc<dyn Client<B>>,
		checker: Arc<dyn FetchChecker<B>>,
		specialization: S,
		transaction_pool: Arc<dyn TransactionPool<H, B>>,
		finality_proof_provider: Option<Arc<dyn FinalityProofProvider<B>>>,
		protocol_id: ProtocolId,
		versions: &[u8],
		peerset: peerset::Peerset,
		peerset_handle: peerset::PeersetHandle,
	) -> crate::error::Result<Self> {
		let protocol = Protocol::new(config, chain, checker, specialization)?;
		let behaviour = CustomProto::new(protocol_id, versions, peerset);

		Ok(ProtocolBehaviour {
			protocol,
			behaviour,
			peerset_handle,
			transaction_pool,
			finality_proof_provider,
		})
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.open_peers()
	}

	/// Returns true if we have a channel open with this node.
	pub fn is_open(&self, peer_id: &PeerId) -> bool {
		self.behaviour.is_open(peer_id)
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId) {
		self.behaviour.disconnect_peer(peer_id)
	}

	/// Adjusts the reputation of a node.
	pub fn report_peer(&mut self, who: PeerId, reputation: i32) {
		self.peerset_handle.report_peer(who, reputation)
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		self.behaviour.is_enabled(peer_id)
	}

	/// Sends a message to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	pub fn send_packet(&mut self, target: &PeerId, message: Message<B>) {
		self.behaviour.send_packet(target, message)
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.behaviour.peerset_debug_info()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.protocol.num_connected_peers()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.protocol.num_active_peers()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncState {
		self.protocol.sync_state()
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.protocol.best_seen_block()
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.protocol.num_sync_peers()
	}

	/// Starts a new data demand request.
	///
	/// The parameter contains a `Sender` where the result, once received, must be sent.
	pub(crate) fn add_on_demand_request(&mut self, rq: RequestData<B>) {
		self.protocol.add_on_demand_request(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			rq
		);
	}

	/// Returns information about all the peers we are connected to after the handshake message.
	pub fn peers_info(&self) -> impl Iterator<Item = (&PeerId, &PeerInfo<B>)> {
		self.protocol.peers_info()
	}

	/// Locks `self` and gives access to the protocol and a context that can be used in order to
	/// use `consensus_gossip_lock` or `specialization_lock`.
	///
	/// **Important**: ONLY USE THIS FUNCTION TO CALL `consensus_gossip_lock` or `specialization_lock`.
	/// This function is a very bad API.
	pub fn protocol_context_lock<'a>(
		&'a mut self,
	) -> (&'a mut Protocol<B, S, H>, LocalNetworkOut<'a, B>) {
		let net_out = LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle };
		(&mut self.protocol, net_out)
	}

	/// Gossip a consensus message to the network.
	pub fn gossip_consensus_message(
		&mut self,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
		recipient: GossipMessageRecipient,
	) {
		self.protocol.gossip_consensus_message(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			topic,
			engine_id,
			message,
			recipient
		);
	}

	/// Call when we must propagate ready extrinsics to peers.
	pub fn propagate_extrinsics(&mut self) {
		self.protocol.propagate_extrinsics(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			&*self.transaction_pool
		)
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&mut self, hash: B::Hash) {
		self.protocol.announce_block(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			hash
		)
	}

	/// Call this when a block has been imported in the import queue and we should announce it on
	/// the network.
	pub fn on_block_imported(&mut self, hash: B::Hash, header: &B::Header) {
		self.protocol.on_block_imported(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			hash,
			header
		)
	}

	/// Call this when a block has been finalized. The sync layer may have some additional
	/// requesting to perform.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: &B::Header) {
		self.protocol.on_block_finalized(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			hash,
			header
		)
	}

	/// Request a justification for the given block.
	///
	/// Uses `protocol` to queue a new justification request and tries to dispatch all pending
	/// requests.
	pub fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		self.protocol.request_justification(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			hash,
			number
		)
	}

	/// Clears all pending justification requests.
	pub fn clear_justification_requests(&mut self) {
		self.protocol.clear_justification_requests()
	}

	/// A batch of blocks have been processed, with or without errors.
	/// Call this when a batch of blocks have been processed by the import queue, with or without
	/// errors.
	pub fn blocks_processed(
		&mut self,
		processed_blocks: Vec<B::Hash>,
		has_error: bool,
	) {
		self.protocol.blocks_processed(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			processed_blocks,
			has_error,
		)
	}

	/// Restart the sync process.
	pub fn restart(&mut self) {
		let mut net_out = LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle };
		self.protocol.restart(&mut net_out);
	}

	/// Notify about successful import of the given block.
	pub fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		self.protocol.block_imported(hash, number)
	}

	pub fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		self.protocol.set_finality_proof_request_builder(request_builder)
	}

	/// Call this when a justification has been processed by the import queue, with or without
	/// errors.
	pub fn justification_import_result(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		self.protocol.justification_import_result(hash, number, success)
	}

	/// The networking-level event has happened.
	pub fn on_event(&mut self, event: Event) {
		self.protocol.on_event(event);
	}

	/// Request a finality proof for the given block.
	///
	/// Queues a new finality proof request and tries to dispatch all pending requests.
	pub fn request_finality_proof(
		&mut self,
		hash: &B::Hash,
		number: NumberFor<B>,
	) {
		self.protocol.request_finality_proof(
			&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle },
			&hash,
			number,
		);
	}

	pub fn finality_proof_import_result(
		&mut self,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		self.protocol.finality_proof_import_result(request_block, finalization_result)
	}

	pub fn tick(&mut self) {
		self.protocol.tick(&mut LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle });
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> NetworkBehaviour for
ProtocolBehaviour<B, S, H> {
	type ProtocolsHandler = <CustomProto<Message<B>, Substream<StreamMuxerBox>> as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = CustomMessageOutcome<B>;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		self.behaviour.new_handler()
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		self.behaviour.addresses_of_peer(peer_id)
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		self.behaviour.inject_connected(peer_id, endpoint)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		self.behaviour.inject_disconnected(peer_id, endpoint)
	}

	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent,
	) {
		self.behaviour.inject_node_event(peer_id, event)
	}

	fn poll(
		&mut self,
		params: &mut impl PollParameters,
	) -> Async<
		NetworkBehaviourAction<
			<<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::InEvent,
			Self::OutEvent
		>
	> {
		let mut net_out = LocalNetworkOut { inner: &mut self.behaviour, peerset_handle: &self.peerset_handle };
		match self.protocol.poll(&mut net_out, &*self.transaction_pool) {
			Ok(Async::Ready(v)) => void::unreachable(v),
			Ok(Async::NotReady) => {}
			Err(err) => void::unreachable(err),
		}

		let event = match self.behaviour.poll(params) {
			Async::NotReady => return Async::NotReady,
			Async::Ready(NetworkBehaviourAction::GenerateEvent(ev)) => ev,
			Async::Ready(NetworkBehaviourAction::DialAddress { address }) =>
				return Async::Ready(NetworkBehaviourAction::DialAddress { address }),
			Async::Ready(NetworkBehaviourAction::DialPeer { peer_id }) =>
				return Async::Ready(NetworkBehaviourAction::DialPeer { peer_id }),
			Async::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }) =>
				return Async::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }),
			Async::Ready(NetworkBehaviourAction::ReportObservedAddr { address }) =>
				return Async::Ready(NetworkBehaviourAction::ReportObservedAddr { address }),
		};

		let mut network_out = LocalNetworkOut {
			inner: &mut self.behaviour,
			peerset_handle: &self.peerset_handle,
		};

		let outcome = match event {
			CustomProtoOut::CustomProtocolOpen { peer_id, version, .. } => {
				debug_assert!(
					version <= protocol::CURRENT_VERSION as u8
					&& version >= protocol::MIN_VERSION as u8
				);
				self.protocol.on_peer_connected(&mut network_out, peer_id);
				CustomMessageOutcome::None
			}
			CustomProtoOut::CustomProtocolClosed { peer_id, .. } => {
				self.protocol.on_peer_disconnected(&mut network_out, peer_id);
				CustomMessageOutcome::None
			},
			CustomProtoOut::CustomMessage { peer_id, message } =>
				self.protocol.on_custom_message(
					&mut network_out,
					&*self.transaction_pool,
					peer_id,
					message,
					self.finality_proof_provider.as_ref().map(|p| &**p)
				),
			CustomProtoOut::Clogged { peer_id, messages } => {
				debug!(target: "sync", "{} clogging messages:", messages.len());
				for msg in messages.into_iter().take(5) {
					debug!(target: "sync", "{:?}", msg);
					self.protocol.on_clogged_peer(&mut network_out, peer_id.clone(), Some(msg));
				}
				CustomMessageOutcome::None
			}
		};

		if let CustomMessageOutcome::None = outcome {
			Async::NotReady
		} else {
			Async::Ready(NetworkBehaviourAction::GenerateEvent(outcome))
		}
	}

	fn inject_replaced(&mut self, peer_id: PeerId, closed_endpoint: ConnectedPoint, new_endpoint: ConnectedPoint) {
		self.behaviour.inject_replaced(peer_id, closed_endpoint, new_endpoint)
	}

	fn inject_addr_reach_failure(
		&mut self,
		peer_id: Option<&PeerId>,
		addr: &Multiaddr,
		error: &dyn std::error::Error
	) {
		self.behaviour.inject_addr_reach_failure(peer_id, addr, error)
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.behaviour.inject_dial_failure(peer_id)
	}

	fn inject_new_listen_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_new_listen_addr(addr)
	}

	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_expired_listen_addr(addr)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_new_external_addr(addr)
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> DiscoveryNetBehaviour
	for ProtocolBehaviour<B, S, H> {
	fn add_discovered_nodes(&mut self, peer_ids: impl Iterator<Item = PeerId>) {
		self.behaviour.add_discovered_nodes(peer_ids)
	}
}

/// Has to be public for stupid API reasons. This should be made private again ASAP.
pub struct LocalNetworkOut<'a, B: BlockT> {
	inner: &'a mut CustomProto<Message<B>, Substream<StreamMuxerBox>>,
	peerset_handle: &'a peerset::PeersetHandle,
}

impl<'a, B: BlockT> NetworkOut<B> for LocalNetworkOut<'a, B> {
	fn report_peer(&mut self, who: PeerId, reputation: i32) {
		self.peerset_handle.report_peer(who, reputation)
	}

	fn disconnect_peer(&mut self, who: PeerId) {
		self.inner.disconnect_peer(&who)
	}

	fn send_message(&mut self, who: PeerId, message: Message<B>) {
		self.inner.send_packet(&who, message)
	}
}
