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

#![allow(missing_docs)]

#[cfg(test)]
mod block_import;
#[cfg(test)]
mod sync;

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use crate::AlwaysBadChecker;
use log::trace;
use crate::chain::FinalityProofProvider;
use client::{self, ClientInfo, BlockchainEvents, FinalityNotifications};
use client::{in_mem::Backend as InMemoryBackend, error::Result as ClientResult};
use client::block_builder::BlockBuilder;
use client::backend::AuxStore;
use crate::config::Roles;
use consensus::import_queue::{BasicQueue, ImportQueue, IncomingBlock};
use consensus::import_queue::{
	Link, SharedBlockImport, SharedJustificationImport, Verifier, SharedFinalityProofImport,
	SharedFinalityProofRequestBuilder,
};
use consensus::{Error as ConsensusError, well_known_cache_keys::{self, Id as CacheKeyId}};
use consensus::{BlockOrigin, ForkChoiceStrategy, ImportBlock, JustificationImport};
use crate::consensus_gossip::{ConsensusGossip, MessageRecipient as GossipMessageRecipient, TopicNotification};
use futures::{prelude::*, sync::{mpsc, oneshot}};
use log::info;
use crate::message::Message;
use libp2p::PeerId;
use parking_lot::{Mutex, RwLock};
use primitives::{H256, Blake2Hasher};
use crate::protocol::{Context, Protocol, ProtocolConfig, ProtocolStatus, CustomMessageOutcome, NetworkOut};
use runtime_primitives::generic::{BlockId, OpaqueDigestItemId};
use runtime_primitives::traits::{Block as BlockT, Header, NumberFor};
use runtime_primitives::{Justification, ConsensusEngineId};
use crate::service::{NetworkMsg, ProtocolMsg, TransactionPool};
use crate::specialization::NetworkSpecialization;
use test_client::{self, AccountKeyring};

pub use test_client::runtime::{Block, Extrinsic, Hash, Transfer};
pub use test_client::TestClient;

type AuthorityId = primitives::sr25519::Public;

#[cfg(any(test, feature = "test-helpers"))]
/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
pub struct PassThroughVerifier(pub bool);

#[cfg(any(test, feature = "test-helpers"))]
/// This `Verifier` accepts all data as valid.
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let maybe_keys = header.digest()
			.log(|l| l.try_as_raw(OpaqueDigestItemId::Consensus(b"aura"))
				.or_else(|| l.try_as_raw(OpaqueDigestItemId::Consensus(b"babe")))
			)
			.map(|blob| vec![(well_known_cache_keys::AUTHORITIES, blob.to_vec())]);

		Ok((ImportBlock {
			origin,
			header,
			body,
			finalized: self.0,
			justification,
			post_digests: vec![],
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		}, maybe_keys))
	}
}

/// A link implementation that does nothing.
pub struct NoopLink { }

impl<B: BlockT> Link<B> for NoopLink { }

/// A link implementation that connects to the network.
#[derive(Clone)]
pub struct NetworkLink<B: BlockT, S: NetworkSpecialization<B>> {
	/// The protocol sender
	pub(crate) protocol_sender: mpsc::UnboundedSender<ProtocolMsg<B, S>>,
	/// The network sender
	pub(crate) network_sender: mpsc::UnboundedSender<NetworkMsg<B>>,
}

impl<B: BlockT, S: NetworkSpecialization<B>> Link<B> for NetworkLink<B, S> {
	fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlockImportedSync(hash.clone(), number));
	}

	fn blocks_processed(&mut self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlocksProcessed(processed_blocks, has_error));
	}

	fn justification_imported(&mut self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::JustificationImportResult(hash.clone(), number, success));
		if !success {
			info!("Invalid justification provided by {} for #{}", who, hash);
			let _ = self.network_sender.unbounded_send(NetworkMsg::ReportPeer(who.clone(), i32::min_value()));
			let _ = self.network_sender.unbounded_send(NetworkMsg::DisconnectPeer(who.clone()));
		}
	}

	fn clear_justification_requests(&mut self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::ClearJustificationRequests);
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RequestFinalityProof(
			hash.clone(),
			number,
		));
	}

	fn finality_proof_imported(
		&mut self,
		who: PeerId,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		let success = finalization_result.is_ok();
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::FinalityProofImportResult(
			request_block,
			finalization_result,
		));
		if !success {
			info!("Invalid finality proof provided by {} for #{}", who, request_block.0);
			let _ = self.network_sender.unbounded_send(NetworkMsg::ReportPeer(who.clone(), i32::min_value()));
			let _ = self.network_sender.unbounded_send(NetworkMsg::DisconnectPeer(who.clone()));
		}
	}

	fn report_peer(&mut self, who: PeerId, reputation_change: i32) {
		let _ = self.network_sender.unbounded_send(NetworkMsg::ReportPeer(who, reputation_change));
	}

	fn restart(&mut self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RestartSync);
	}

	fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::SetFinalityProofRequestBuilder(request_builder));
	}
}

/// The test specialization.
#[derive(Clone)]
pub struct DummySpecialization;

impl NetworkSpecialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> {
		vec![]
	}

	fn on_connect(
		&mut self,
		_ctx: &mut dyn Context<Block>,
		_peer_id: PeerId,
		_status: crate::message::Status<Block>
	) {}

	fn on_disconnect(&mut self, _ctx: &mut dyn Context<Block>, _peer_id: PeerId) {}

	fn on_message(
		&mut self,
		_ctx: &mut dyn Context<Block>,
		_peer_id: PeerId,
		_message: &mut Option<crate::message::Message<Block>>,
	) {}
}

pub type PeersFullClient =
	client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>;
pub type PeersLightClient =
	client::Client<test_client::LightBackend, test_client::LightExecutor, Block, test_client::runtime::RuntimeApi>;

#[derive(Clone)]
pub enum PeersClient {
	Full(Arc<PeersFullClient>),
	Light(Arc<PeersLightClient>),
}

impl PeersClient {
	pub fn as_full(&self) -> Option<Arc<PeersFullClient>> {
		match *self {
			PeersClient::Full(ref client) => Some(client.clone()),
			_ => None,
		}
	}

	pub fn as_block_import(&self) -> SharedBlockImport<Block> {
		match *self {
			PeersClient::Full(ref client) => client.clone() as _,
			PeersClient::Light(ref client) => client.clone() as _,
		}
	}

	pub fn as_in_memory_backend(&self) -> InMemoryBackend<Block, Blake2Hasher> {
		#[allow(deprecated)]
		match *self {
			PeersClient::Full(ref client) => client.backend().as_in_memory(),
			PeersClient::Light(_) => unimplemented!("TODO"),
		}
	}

	pub fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		#[allow(deprecated)]
		match *self {
			PeersClient::Full(ref client) => client.backend().get_aux(key),
			PeersClient::Light(ref client) => client.backend().get_aux(key),
		}
	}

	pub fn info(&self) -> ClientInfo<Block> {
		match *self {
			PeersClient::Full(ref client) => client.info(),
			PeersClient::Light(ref client) => client.info(),
		}
	}

	pub fn header(&self, block: &BlockId<Block>) -> ClientResult<Option<<Block as BlockT>::Header>> {
		match *self {
			PeersClient::Full(ref client) => client.header(block),
			PeersClient::Light(ref client) => client.header(block),
		}
	}

	pub fn justification(&self, block: &BlockId<Block>) -> ClientResult<Option<Justification>> {
		match *self {
			PeersClient::Full(ref client) => client.justification(block),
			PeersClient::Light(ref client) => client.justification(block),
		}
	}

	pub fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		match *self {
			PeersClient::Full(ref client) => client.finality_notification_stream(),
			PeersClient::Light(ref client) => client.finality_notification_stream(),
		}
	}

	pub fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool
	) -> ClientResult<()> {
		match *self {
			PeersClient::Full(ref client) => client.finalize_block(id, justification, notify),
			PeersClient::Light(ref client) => client.finalize_block(id, justification, notify),
		}
	}
}

/// A Link that can wait for a block to have been imported.
pub struct TestLink<S: NetworkSpecialization<Block>> {
	link: NetworkLink<Block, S>,

	#[cfg(any(test, feature = "test-helpers"))]
	network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
}

impl<S: NetworkSpecialization<Block>> TestLink<S> {
	fn new(
		protocol_sender: mpsc::UnboundedSender<ProtocolMsg<Block, S>>,
		_network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
		network_sender: mpsc::UnboundedSender<NetworkMsg<Block>>
	) -> TestLink<S> {
		TestLink {
			#[cfg(any(test, feature = "test-helpers"))]
			network_to_protocol_sender: _network_to_protocol_sender,
			link: NetworkLink {
				protocol_sender,
				network_sender,
			}
		}
	}
}

impl<S: NetworkSpecialization<Block>> Link<Block> for TestLink<S> {
	fn block_imported(&mut self, hash: &Hash, number: NumberFor<Block>) {
		self.link.block_imported(hash, number);
	}

	fn blocks_processed(&mut self, processed_blocks: Vec<Hash>, has_error: bool) {
		self.link.blocks_processed(processed_blocks, has_error);
	}

	fn justification_imported(&mut self, who: PeerId, hash: &Hash, number:NumberFor<Block>, success: bool) {
		self.link.justification_imported(who, hash, number, success);
	}

	fn request_justification(&mut self, hash: &Hash, number: NumberFor<Block>) {
		self.link.request_justification(hash, number);
	}

	fn finality_proof_imported(
		&mut self,
		who: PeerId,
		request_block: (Hash, NumberFor<Block>),
		finalization_result: Result<(Hash, NumberFor<Block>), ()>,
	) {
		self.link.finality_proof_imported(who, request_block, finalization_result);
	}

	fn request_finality_proof(&mut self, hash: &Hash, number: NumberFor<Block>) {
		self.link.request_finality_proof(hash, number);
	}

	fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<Block>) {
		self.link.set_finality_proof_request_builder(request_builder);
	}

	fn report_peer(&mut self, who: PeerId, reputation_change: i32) {
		self.link.report_peer(who, reputation_change);
	}

	fn restart(&mut self) {
		self.link.restart();
	}

	/// Send synchronization request to the block import channel.
	///
	/// The caller should wait for the `Link::synchronized` call to ensure that it has synchronized
	/// with `ImportQueue`.
	#[cfg(any(test, feature = "test-helpers"))]
	fn synchronized(&mut self) {
		drop(self.network_to_protocol_sender.unbounded_send(FromNetworkMsg::Synchronize))
	}
}

pub struct Peer<D, S: NetworkSpecialization<Block>> {
	peer_id: PeerId,
	client: PeersClient,
	net_proto_channel: ProtocolChannel<S>,
	/// This field is used only in test code, but maintaining different
	/// instantiation paths or field names is too much hassle, hence
	/// we allow it to be unused.
	#[cfg_attr(not(test), allow(unused))]
	protocol_status: Arc<RwLock<ProtocolStatus<Block>>>,
	import_queue: Arc<Mutex<Box<BasicQueue<Block>>>>,
	pub data: D,
	best_hash: Mutex<Option<H256>>,
	finalized_hash: Mutex<Option<H256>>,
}

type MessageFilter = dyn Fn(&NetworkMsg<Block>) -> bool;

pub enum FromNetworkMsg<B: BlockT> {
	/// A peer connected.
	PeerConnected(PeerId),
	/// A peer disconnected.
	PeerDisconnected(PeerId),
	/// A custom message from another peer.
	CustomMessage(PeerId, Message<B>),
	/// Synchronization request.
	Synchronize,
}

struct ProtocolChannel<S: NetworkSpecialization<Block>> {
	/// If true, we expect a tokio executor to be available. If false, we spawn our own.
	use_tokio: bool,
	buffered_messages: Mutex<VecDeque<NetworkMsg<Block>>>,
	network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
	client_to_protocol_sender: mpsc::UnboundedSender<ProtocolMsg<Block, S>>,
	protocol_to_network_receiver: Mutex<mpsc::UnboundedReceiver<NetworkMsg<Block>>>,
}

impl<S: NetworkSpecialization<Block>> ProtocolChannel<S> {
	/// Create new buffered network port.
	pub fn new(
		use_tokio: bool,
		network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
		client_to_protocol_sender: mpsc::UnboundedSender<ProtocolMsg<Block, S>>,
		protocol_to_network_receiver: mpsc::UnboundedReceiver<NetworkMsg<Block>>,
	) -> Self {
		ProtocolChannel {
			use_tokio,
			buffered_messages: Mutex::new(VecDeque::new()),
			network_to_protocol_sender,
			client_to_protocol_sender,
			protocol_to_network_receiver: Mutex::new(protocol_to_network_receiver),
		}
	}

	/// Send message from network to protocol.
	pub fn send_from_net(&self, message: FromNetworkMsg<Block>) {
		let _ = self.network_to_protocol_sender.unbounded_send(message);

		let _ = self.network_to_protocol_sender.unbounded_send(FromNetworkMsg::Synchronize);
		let _ = self.wait_sync();
	}

	/// Send message from client to protocol.
	pub fn send_from_client(&self, message: ProtocolMsg<Block, S>) {
		let _ = self.client_to_protocol_sender.unbounded_send(message);

		let _ = self.client_to_protocol_sender.unbounded_send(ProtocolMsg::Synchronize);
		let _ = self.wait_sync();
	}

	/// Wait until synchronization response is generated by the protocol.
	pub fn wait_sync(&self) -> Result<(), ()> {
		let fut = futures::future::poll_fn(|| {
			loop {
				let mut protocol_to_network_receiver = self.protocol_to_network_receiver.lock();
				match protocol_to_network_receiver.poll() {
					Ok(Async::Ready(Some(NetworkMsg::Synchronized))) => return Ok(Async::Ready(())),
					Ok(Async::Ready(None)) | Err(_) => return Err(()),
					Ok(Async::NotReady) => return Ok(Async::NotReady),
					Ok(Async::Ready(Some(msg))) => self.buffered_messages.lock().push_back(msg),
				}
			}
		});

		if self.use_tokio {
			fut.wait()
		} else {
			tokio::runtime::current_thread::block_on_all(fut)
		}
	}

	/// Produce the next pending message to send to another peer.
	fn pending_message(&self, message_filter: &MessageFilter) -> Option<NetworkMsg<Block>> {
		if let Some(message) = self.buffered_message(message_filter) {
			return Some(message);
		}

		while let Some(message) = self.channel_message() {
			if message_filter(&message) {
				return Some(message)
			} else {
				self.buffered_messages.lock().push_back(message);
			}
		}

		None
	}

	/// Whether this peer is done syncing (has no messages to send).
	fn is_done(&self) -> bool {
		let mut buffered_messages = self.buffered_messages.lock();
		if let Some(msg) = self.channel_message() {
			buffered_messages.push_back(msg);
			false
		} else {
			buffered_messages.is_empty()
		}
	}

	/// Return oldest buffered message if it exists.
	fn buffered_message(&self, message_filter: &MessageFilter) -> Option<NetworkMsg<Block>> {
		let mut buffered_messages = self.buffered_messages.lock();
		for i in 0..buffered_messages.len() {
			if message_filter(&buffered_messages[i]) {
				return buffered_messages.remove(i);
			}
		}

		None
	}

	/// Receive message from the channel.
	fn channel_message(&self) -> Option<NetworkMsg<Block>> {
		let fut = futures::future::poll_fn(|| -> Result<_, ()> {
			Ok(Async::Ready(match self.protocol_to_network_receiver.lock().poll() {
				Ok(Async::Ready(Some(m))) => Some(m),
				Ok(Async::NotReady) => None,
				Err(_) => None,
				Ok(Async::Ready(None)) => None,
			}))
		});

		if self.use_tokio {
			fut.wait()
		} else {
			tokio::runtime::current_thread::block_on_all(fut)
		}.ok().and_then(|a| a)
	}
}

impl<D, S: NetworkSpecialization<Block>> Peer<D, S> {
	fn new(
		protocol_status: Arc<RwLock<ProtocolStatus<Block>>>,
		client: PeersClient,
		import_queue: Arc<Mutex<Box<BasicQueue<Block>>>>,
		use_tokio: bool,
		network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
		protocol_sender: mpsc::UnboundedSender<ProtocolMsg<Block, S>>,
		network_sender: mpsc::UnboundedSender<NetworkMsg<Block>>,
		network_port: mpsc::UnboundedReceiver<NetworkMsg<Block>>,
		data: D,
	) -> Self {
		let net_proto_channel = ProtocolChannel::new(
			use_tokio,
			network_to_protocol_sender.clone(),
			protocol_sender.clone(),
			network_port,
		);
		Peer {
			protocol_status,
			peer_id: PeerId::random(),
			client,
			import_queue,
			net_proto_channel,
			data,
			best_hash: Mutex::new(None),
			finalized_hash: Mutex::new(None),
		}
	}
	/// Called after blockchain has been populated to updated current state.
	fn start(&self) {
		// Update the sync state to the latest chain state.
		let info = self.client.info();
		let header = self
			.client
			.header(&BlockId::Hash(info.chain.best_hash))
			.unwrap()
			.unwrap();
		self.net_proto_channel.send_from_client(ProtocolMsg::BlockImported(info.chain.best_hash, header));
	}

	#[cfg(test)]
	fn on_block_imported(
		&self,
		hash: <Block as BlockT>::Hash,
		header: &<Block as BlockT>::Header,
	) {
		self.net_proto_channel.send_from_client(ProtocolMsg::BlockImported(hash, header.clone()));
	}

	/// SyncOracle: are we connected to any peer?
	#[cfg(test)]
	fn is_offline(&self) -> bool {
		self.protocol_status.read().sync.is_offline()
	}

	/// SyncOracle: are we in the process of catching-up with the chain?
	#[cfg(test)]
	fn is_major_syncing(&self) -> bool {
		self.protocol_status.read().sync.is_major_syncing()
	}

	/// Get protocol status.
	#[cfg(test)]
	fn protocol_status(&self) -> ProtocolStatus<Block> {
		self.protocol_status.read().clone()
	}

	/// Called on connection to other indicated peer.
	fn on_connect(&self, other: &Self) {
		self.net_proto_channel.send_from_net(FromNetworkMsg::PeerConnected(other.peer_id.clone()));
	}

	/// Called on disconnect from other indicated peer.
	fn on_disconnect(&self, other: &Self) {
		self.net_proto_channel.send_from_net(FromNetworkMsg::PeerDisconnected(other.peer_id.clone()));
	}

	/// Receive a message from another peer. Return a set of peers to disconnect.
	fn receive_message(&self, from: &PeerId, msg: Message<Block>) {
		self.net_proto_channel.send_from_net(FromNetworkMsg::CustomMessage(from.clone(), msg));
	}

	/// Produce the next pending message to send to another peer.
	fn pending_message(&self, message_filter: &MessageFilter) -> Option<NetworkMsg<Block>> {
		self.net_proto_channel.pending_message(message_filter)
	}

	/// Whether this peer is done syncing (has no messages to send).
	fn is_done(&self) -> bool {
		self.net_proto_channel.is_done()
	}

	/// Synchronize with import queue.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn import_queue_sync(&self) {
		self.import_queue.lock().synchronize();
		let _ = self.net_proto_channel.wait_sync();
	}

	/// Execute a "sync step". This is called for each peer after it sends a packet.
	fn sync_step(&self) {
		self.net_proto_channel.send_from_client(ProtocolMsg::Tick);
	}

	/// Send block import notifications.
	fn send_import_notifications(&self) {
		let info = self.client.info();

		let mut best_hash = self.best_hash.lock();
		match *best_hash {
			None => {},
			Some(hash) if hash != info.chain.best_hash => {},
			_ => return,
		}

		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		self.net_proto_channel.send_from_client(ProtocolMsg::BlockImported(info.chain.best_hash, header));
		*best_hash = Some(info.chain.best_hash);
	}

	/// Send block finalization notifications.
	fn send_finality_notifications(&self) {
		let info = self.client.info();

		let mut finalized_hash = self.finalized_hash.lock();
		match *finalized_hash {
			None => {},
			Some(hash) if hash != info.chain.finalized_hash => {},
			_ => return,
		}

		let header = self.client.header(&BlockId::Hash(info.chain.finalized_hash)).unwrap().unwrap();
		self.net_proto_channel.send_from_client(
			ProtocolMsg::BlockFinalized(info.chain.finalized_hash, header.clone())
		);
		*finalized_hash = Some(info.chain.finalized_hash);
	}

	/// Push a message into the gossip network and relay to peers.
	/// `TestNet::sync_step` needs to be called to ensure it's propagated.
	pub fn gossip_message(
		&self,
		topic: <Block as BlockT>::Hash,
		engine_id: ConsensusEngineId,
		data: Vec<u8>,
		force: bool,
	) {
		let recipient = if force {
			GossipMessageRecipient::BroadcastToAll
		} else {
			GossipMessageRecipient::BroadcastNew
		};
		self.net_proto_channel.send_from_client(
			ProtocolMsg::GossipConsensusMessage(topic, engine_id, data, recipient),
		);
	}

	/// access the underlying consensus gossip handler
	pub fn consensus_gossip_messages_for(
		&self,
		engine_id: ConsensusEngineId,
		topic: <Block as BlockT>::Hash,
	) -> mpsc::UnboundedReceiver<TopicNotification> {
		let (tx, rx) = oneshot::channel();
		self.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(engine_id, topic);
			let _ = tx.send(inner_rx);
		});
		rx.wait().ok().expect("1. Network is running, 2. it should handle the above closure successfully")
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<Block>, &mut dyn Context<Block>) + Send + 'static
	{
		self.net_proto_channel.send_from_client(ProtocolMsg::ExecuteWithGossip(Box::new(f)));
	}

	/// Announce a block to peers.
	#[cfg(test)]
	fn announce_block(&self, block: Hash) {
		self.net_proto_channel.send_from_client(ProtocolMsg::AnnounceBlock(block));
	}

	/// Request a justification for the given block.
	#[cfg(test)]
	fn request_justification(&self, hash: &::primitives::H256, number: NumberFor<Block>) {
		self.net_proto_channel.send_from_client(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&self, count: usize, origin: BlockOrigin, edit_block: F) -> H256
		where F: FnMut(BlockBuilder<Block, PeersFullClient>) -> Block
	{
		let best_hash = self.client.info().chain.best_hash;
		self.generate_blocks_at(BlockId::Hash(best_hash), count, origin, edit_block)
	}

	/// Add blocks to the peer -- edit the block before adding. The chain will
	/// start at the given block iD.
	fn generate_blocks_at<F>(
		&self,
		at: BlockId<Block>,
		count: usize,
		origin: BlockOrigin,
		mut edit_block: F
	) -> H256 where F: FnMut(BlockBuilder<Block, PeersFullClient>) -> Block {
		let full_client = self.client.as_full().expect("blocks could only be generated by full clients");
		let mut at = full_client.header(&at).unwrap().unwrap().hash();
		for _  in 0..count {
			let builder = full_client.new_block_at(&BlockId::Hash(at), Default::default()
			).unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!(
				target: "test_network",
				"Generating {}, (#{}, parent={})",
				hash,
				block.header.number,
				block.header.parent_hash
			);
			let header = block.header.clone();
			at = hash;
			self.import_queue.lock().import_blocks(
				origin,
				vec![IncomingBlock {
					origin: None,
					hash,
					header: Some(header),
					body: Some(block.extrinsics),
					justification: None,
				}],
			);

			// make sure block import has completed
			self.import_queue_sync();
		}

		at
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&self, count: usize, with_tx: bool) -> H256 {
		let best_hash = self.client.info().chain.best_hash;
		self.push_blocks_at(BlockId::Hash(best_hash), count, with_tx)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash.
	pub fn push_blocks_at(&self, at: BlockId<Block>, count: usize, with_tx: bool) -> H256 {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks_at(at, count, BlockOrigin::File, |mut builder| {
				let transfer = Transfer {
					from: AccountKeyring::Alice.into(),
					to: AccountKeyring::Alice.into(),
					amount: 1,
					nonce,
				};
				builder.push(transfer.into_signed_tx()).unwrap();
				nonce = nonce + 1;
				builder.bake().unwrap()
			})
		} else {
			self.generate_blocks_at(at, count, BlockOrigin::File, |builder| builder.bake().unwrap())
		}
	}

	pub fn push_authorities_change_block(&self, new_authorities: Vec<AuthorityId>) -> H256 {
		self.generate_blocks(1, BlockOrigin::File, |mut builder| {
			builder.push(Extrinsic::AuthoritiesChange(new_authorities.clone())).unwrap();
			builder.bake().unwrap()
		})
	}

	/// Get a reference to the client.
	pub fn client(&self) -> &PeersClient {
		&self.client
	}
}

pub struct EmptyTransactionPool;

impl TransactionPool<Hash, Block> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(Hash, Extrinsic)> {
		Vec::new()
	}

	fn import(&self, _transaction: &Extrinsic) -> Option<Hash> {
		None
	}

	fn on_broadcasted(&self, _: HashMap<Hash, Vec<String>>) {}
}

pub trait SpecializationFactory {
	fn create() -> Self;
}

impl SpecializationFactory for DummySpecialization {
	fn create() -> DummySpecialization {
		DummySpecialization
	}
}

pub trait TestNetFactory: Sized {
	type Specialization: NetworkSpecialization<Block> + SpecializationFactory;
	type Verifier: 'static + Verifier<Block>;
	type PeerData: Default;

	/// These two need to be implemented!
	fn from_config(config: &ProtocolConfig) -> Self;
	fn make_verifier(&self, client: PeersClient, config: &ProtocolConfig) -> Arc<Self::Verifier>;

	/// Get reference to peer.
	fn peer(&self, i: usize) -> &Peer<Self::PeerData, Self::Specialization>;
	fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>;
	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>)>(&mut self, closure: F);

	fn started(&self) -> bool;
	fn set_started(&mut self, now: bool);

	/// Get custom block import handle for fresh client, along with peer data.
	fn make_block_import(&self, client: PeersClient)
		-> (
			SharedBlockImport<Block>,
			Option<SharedJustificationImport<Block>>,
			Option<SharedFinalityProofImport<Block>>,
			Option<SharedFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(client.as_block_import(), None, None, None, Default::default())
	}

	/// Get finality proof provider (if supported).
	fn make_finality_proof_provider(&self, _client: PeersClient) -> Option<Arc<dyn FinalityProofProvider<Block>>> {
		None
	}

	fn default_config() -> ProtocolConfig {
		ProtocolConfig::default()
	}

	/// Must return true if the testnet is going to be used from within a tokio context.
	fn uses_tokio(&self) -> bool {
		false
	}

	/// Create new test network with this many peers.
	fn new(n: usize) -> Self {
		trace!(target: "test_network", "Creating test network");
		let config = Self::default_config();
		let mut net = Self::from_config(&config);

		for i in 0..n {
			trace!(target: "test_network", "Adding peer {}", i);
			net.add_full_peer(&config);
		}
		net
	}

	/// Add created peer.
	fn add_peer(
		&mut self,
		protocol_status: Arc<RwLock<ProtocolStatus<Block>>>,
		import_queue: Arc<Mutex<Box<BasicQueue<Block>>>>,
		tx_pool: EmptyTransactionPool,
		finality_proof_provider: Option<Arc<dyn FinalityProofProvider<Block>>>,
		mut protocol: Protocol<Block, Self::Specialization, Hash>,
		protocol_sender: mpsc::UnboundedSender<ProtocolMsg<Block, Self::Specialization>>,
		network_to_protocol_sender: mpsc::UnboundedSender<FromNetworkMsg<Block>>,
		network_sender: mpsc::UnboundedSender<NetworkMsg<Block>>,
		mut network_to_protocol_rx: mpsc::UnboundedReceiver<FromNetworkMsg<Block>>,
		mut protocol_rx: mpsc::UnboundedReceiver<ProtocolMsg<Block, Self::Specialization>>,
		peer: Arc<Peer<Self::PeerData, Self::Specialization>>,
	) {
		std::thread::spawn(move || {
			// Implementation of `protocol::NetworkOut` using the available local variables.
			struct Ctxt<'a, B: BlockT>(&'a mpsc::UnboundedSender<NetworkMsg<B>>);
			impl<'a, B: BlockT> NetworkOut<B> for Ctxt<'a, B> {
				fn report_peer(&mut self, who: PeerId, reputation: i32) {
					let _ = self.0.unbounded_send(NetworkMsg::ReportPeer(who, reputation));
				}
				fn disconnect_peer(&mut self, who: PeerId) {
					let _ = self.0.unbounded_send(NetworkMsg::DisconnectPeer(who));
				}
				fn send_message(&mut self, who: PeerId, message: Message<B>) {
					let _ = self.0.unbounded_send(NetworkMsg::Outgoing(who, message));
				}
			}

			tokio::runtime::current_thread::run(futures::future::poll_fn(move || {
				import_queue.lock().poll_actions(&mut TestLink::new(
					protocol_sender.clone(),
					network_to_protocol_sender.clone(),
					network_sender.clone(),
				));

				while let Async::Ready(msg) = network_to_protocol_rx.poll().unwrap() {
					let outcome = match msg {
						Some(FromNetworkMsg::PeerConnected(peer_id)) => {
							protocol.on_peer_connected(&mut Ctxt(&network_sender), peer_id);
							CustomMessageOutcome::None
						},
						Some(FromNetworkMsg::PeerDisconnected(peer_id)) => {
							protocol.on_peer_disconnected(&mut Ctxt(&network_sender), peer_id);
							CustomMessageOutcome::None
						},
						Some(FromNetworkMsg::CustomMessage(peer_id, message)) =>
							protocol.on_custom_message(
								&mut Ctxt(&network_sender),
								&tx_pool,
								peer_id,
								message,
								finality_proof_provider.as_ref().map(|p| &**p)
							),
						Some(FromNetworkMsg::Synchronize) => {
							let _ = network_sender.unbounded_send(NetworkMsg::Synchronized);
							CustomMessageOutcome::None
						},
						None => return Ok(Async::Ready(())),
					};

					match outcome {
						CustomMessageOutcome::BlockImport(origin, blocks) =>
							import_queue.lock().import_blocks(origin, blocks),
						CustomMessageOutcome::JustificationImport(origin, hash, nb, justification) =>
							import_queue.lock().import_justification(origin, hash, nb, justification),
						CustomMessageOutcome::FinalityProofImport(origin, hash, nb, proof) =>
							import_queue.lock().import_finality_proof(origin, hash, nb, proof),
						CustomMessageOutcome::None => {}
					}
				}

				loop {
					let msg = match protocol_rx.poll() {
						Ok(Async::Ready(Some(msg))) => msg,
						Ok(Async::Ready(None)) | Err(_) => return Ok(Async::Ready(())),
						Ok(Async::NotReady) => break,
					};

					match msg {
						ProtocolMsg::BlockImported(hash, header) =>
							protocol.on_block_imported(&mut Ctxt(&network_sender), hash, &header),
						ProtocolMsg::BlockFinalized(hash, header) =>
							protocol.on_block_finalized(&mut Ctxt(&network_sender), hash, &header),
						ProtocolMsg::ExecuteWithSpec(task) => {
							let mut ctxt = Ctxt(&network_sender);
							let (mut context, spec) = protocol.specialization_lock(&mut ctxt);
							task.call_box(spec, &mut context);
						},
						ProtocolMsg::ExecuteWithGossip(task) => {
							let mut ctxt = Ctxt(&network_sender);
							let (mut context, gossip) = protocol.consensus_gossip_lock(&mut ctxt);
							task.call_box(gossip, &mut context);
						}
						ProtocolMsg::GossipConsensusMessage(topic, engine_id, message, recipient) =>
							protocol.gossip_consensus_message(
								&mut Ctxt(&network_sender),
								topic,
								engine_id,
								message,
								recipient
							),
						ProtocolMsg::BlocksProcessed(hashes, has_error) =>
							protocol.blocks_processed(&mut Ctxt(&network_sender), hashes, has_error),
						ProtocolMsg::RestartSync =>
							protocol.restart(&mut Ctxt(&network_sender)),
						ProtocolMsg::AnnounceBlock(hash) =>
							protocol.announce_block(&mut Ctxt(&network_sender), hash),
						ProtocolMsg::BlockImportedSync(hash, number) =>
							protocol.block_imported(&hash, number),
						ProtocolMsg::ClearJustificationRequests =>
							protocol.clear_justification_requests(),
						ProtocolMsg::RequestJustification(hash, number) =>
							protocol.request_justification(&mut Ctxt(&network_sender), &hash, number),
						ProtocolMsg::JustificationImportResult(hash, number, success) =>
							protocol.justification_import_result(hash, number, success),
						ProtocolMsg::SetFinalityProofRequestBuilder(builder) =>
							protocol.set_finality_proof_request_builder(builder),
						ProtocolMsg::RequestFinalityProof(hash, number) =>
							protocol.request_finality_proof(&mut Ctxt(&network_sender), &hash, number),
						ProtocolMsg::FinalityProofImportResult(requested_block, finalziation_result) =>
							protocol.finality_proof_import_result(requested_block, finalziation_result),
						ProtocolMsg::PropagateExtrinsics =>
							protocol.propagate_extrinsics(&mut Ctxt(&network_sender), &tx_pool),
						#[cfg(any(test, feature = "test-helpers"))]
						ProtocolMsg::Tick => protocol.tick(&mut Ctxt(&network_sender)),
						#[cfg(any(test, feature = "test-helpers"))]
						ProtocolMsg::Synchronize => {
							trace!(target: "sync", "handle_client_msg: received Synchronize msg");
							let _ = network_sender.unbounded_send(NetworkMsg::Synchronized);
						}
					}
				}

				if let Async::Ready(_) = protocol.poll(&mut Ctxt(&network_sender), &tx_pool).unwrap() {
					return Ok(Async::Ready(()))
				}

				*protocol_status.write() = protocol.status();
				Ok(Async::NotReady)
			}));
		});

		if self.started() {
			peer.start();
			self.peers().iter().for_each(|other| {
				other.on_connect(&*peer);
				peer.on_connect(other);
			});
		}

		self.mut_peers(|peers| {
			peers.push(peer)
		});
	}

	/// Add a full peer.
	fn add_full_peer(&mut self, config: &ProtocolConfig) {
		let client = Arc::new(test_client::new());
		let verifier = self.make_verifier(PeersClient::Full(client.clone()), config);
		let (block_import, justification_import, finality_proof_import, finality_proof_request_builder, data)
			= self.make_block_import(PeersClient::Full(client.clone()));
		let (network_sender, network_port) = mpsc::unbounded();

		let import_queue = Arc::new(Mutex::new(Box::new(BasicQueue::new(
			verifier,
			block_import,
			justification_import,
			finality_proof_import,
			finality_proof_request_builder,
		))));
		let specialization = self::SpecializationFactory::create();

		let (network_to_protocol_sender, network_to_protocol_rx) = mpsc::unbounded();
		let (protocol_sender, protocol_rx) = mpsc::unbounded();

		let protocol = Protocol::new(
			config.clone(),
			client.clone(),
			Arc::new(AlwaysBadChecker),
			specialization,
		).unwrap();

		let protocol_status = Arc::new(RwLock::new(protocol.status()));
		self.add_peer(
			protocol_status.clone(),
			import_queue.clone(),
			EmptyTransactionPool,
			self.make_finality_proof_provider(PeersClient::Full(client.clone())),
			protocol,
			protocol_sender.clone(),
			network_to_protocol_sender.clone(),
			network_sender.clone(),
			network_to_protocol_rx,
			protocol_rx,
			Arc::new(Peer::new(
				protocol_status,
				PeersClient::Full(client),
				import_queue,
				self.uses_tokio(),
				network_to_protocol_sender,
				protocol_sender,
				network_sender,
				network_port,
				data,
			)),
		);
	}

	/// Add a light peer.
	fn add_light_peer(&mut self, config: &ProtocolConfig) {
		let mut config = config.clone();
		config.roles = Roles::LIGHT;

		let client = Arc::new(test_client::new_light());
		let verifier = self.make_verifier(PeersClient::Light(client.clone()), &config);
		let (block_import, justification_import, finality_proof_import, finality_proof_request_builder, data)
			= self.make_block_import(PeersClient::Light(client.clone()));
		let (network_sender, network_port) = mpsc::unbounded();

		let import_queue = Arc::new(Mutex::new(Box::new(BasicQueue::new(
			verifier,
			block_import,
			justification_import,
			finality_proof_import,
			finality_proof_request_builder,
		))));
		let specialization = self::SpecializationFactory::create();

		let (network_to_protocol_sender, network_to_protocol_rx) = mpsc::unbounded();
		let (protocol_sender, protocol_rx) = mpsc::unbounded();

		let protocol = Protocol::new(
			config,
			client.clone(),
			Arc::new(AlwaysBadChecker),
			specialization,
		).unwrap();

		let protocol_status = Arc::new(RwLock::new(protocol.status()));
		self.add_peer(
			protocol_status.clone(),
			import_queue.clone(),
			EmptyTransactionPool,
			self.make_finality_proof_provider(PeersClient::Light(client.clone())),
			protocol,
			protocol_sender.clone(),
			network_to_protocol_sender.clone(),
			network_sender.clone(),
			network_to_protocol_rx,
			protocol_rx,
			Arc::new(Peer::new(
				protocol_status,
				PeersClient::Light(client),
				import_queue,
				self.uses_tokio(),
				network_to_protocol_sender,
				protocol_sender,
				network_sender,
				network_port,
				data,
			)),
		);
	}

	/// Start network.
	fn start(&mut self) {
		if self.started() {
			return;
		}
		for peer in self.peers() {
			peer.start();
			for client in self.peers() {
				if peer.peer_id != client.peer_id {
					peer.on_connect(client);
				}
			}
		}

		loop {
			// we only deliver Status messages during start
			let need_continue = self.route_single(true, None, &|msg| match *msg {
				NetworkMsg::Outgoing(_, crate::message::generic::Message::Status(_)) => true,
				NetworkMsg::Outgoing(_, _) => false,
				NetworkMsg::DisconnectPeer(_) |
				NetworkMsg::ReportPeer(_, _) | NetworkMsg::Synchronized => true,
			});
			if !need_continue {
				break;
			}
		}

		self.set_started(true);
	}

	/// Do single round of message routing: single message from every peer is routed.
	fn route_single(
		&mut self,
		disconnect: bool,
		disconnected: Option<HashSet<usize>>,
		message_filter: &MessageFilter,
	) -> bool {
		let mut had_messages = false;
		let mut to_disconnect = HashSet::new();
		let peers = self.peers();
		for peer in peers {
			if let Some(message) = peer.pending_message(message_filter) {
				match message {
					NetworkMsg::Outgoing(recipient_id, packet) => {
						had_messages = true;

						let sender_pos = peers.iter().position(|p| p.peer_id == peer.peer_id).unwrap();
						let recipient_pos = peers.iter().position(|p| p.peer_id == recipient_id).unwrap();
						if disconnect {
							if let Some(ref disconnected) = disconnected {
								let mut current = HashSet::new();
								current.insert(sender_pos);
								current.insert(recipient_pos);
								// Not routing message between "disconnected" nodes.
								if disconnected.is_subset(&current) {
									continue;
								}
							}
						}

						peers[recipient_pos].receive_message(&peer.peer_id, packet);
					},
					NetworkMsg::DisconnectPeer(who) => {
						if disconnect {
							to_disconnect.insert(who);
						}
					},
					_ => (),
				}
			}
		}

		for d in to_disconnect {
			if let Some(d) = peers.iter().find(|p| p.peer_id == d) {
				for peer in 0..peers.len() {
					peers[peer].on_disconnect(d);
				}
			}
		}

		// make sure that the protocol(s) has processed all messages that have been queued
		self.peers().iter().for_each(|peer| peer.import_queue_sync());

		had_messages
	}

	/// Send block import notifications for all peers.
	fn send_import_notifications(&mut self) {
		self.peers().iter().for_each(|peer| peer.send_import_notifications())
	}

	/// Send block finalization notifications for all peers.
	fn send_finality_notifications(&mut self) {
		self.peers().iter().for_each(|peer| peer.send_finality_notifications())
	}

	/// Perform synchronization until complete, if provided the
	/// given nodes set are excluded from sync.
	fn sync_with(&mut self, disconnect: bool, disconnected: Option<HashSet<usize>>) {
		self.start();
		while self.route_single(disconnect, disconnected.clone(), &|_| true) {
			// give protocol a chance to do its maintain procedures
			self.peers().iter().for_each(|peer| peer.sync_step());
		}
	}

	/// Deliver at most 1 pending message from every peer.
	fn sync_step(&mut self) {
		self.route_single(true, None, &|_| true);
	}

	/// Maintain sync for a peer.
	fn tick_peer(&mut self, i: usize) {
		self.peers()[i].sync_step();
	}

	/// Deliver pending messages until there are no more.
	fn sync(&mut self) {
		self.sync_with(true, None)
	}

	/// Deliver pending messages until there are no more. Do not disconnect nodes.
	fn sync_without_disconnects(&mut self) {
		self.sync_with(false, None)
	}

	/// Whether all peers have no pending outgoing messages.
	fn done(&self) -> bool {
		self.peers().iter().all(|p| p.is_done())
	}
}

pub struct TestNet {
	peers: Vec<Arc<Peer<(), DummySpecialization>>>,
	started: bool,
}

impl TestNetFactory for TestNet {
	type Specialization = DummySpecialization;
	type Verifier = PassThroughVerifier;
	type PeerData = ();

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		TestNet {
			peers: Vec::new(),
			started: false
		}
	}

	fn make_verifier(&self, _client: PeersClient, _config: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		Arc::new(PassThroughVerifier(false))
	}

	fn peer(&self, i: usize) -> &Peer<(), Self::Specialization> {
		&self.peers[i]
	}

	fn peers(&self) -> &Vec<Arc<Peer<(), Self::Specialization>>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<(), Self::Specialization>>>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}

	fn started(&self) -> bool {
		self.started
	}

	fn set_started(&mut self, new: bool) {
		self.started = new;
	}
}

pub struct ForceFinalized(PeersClient);

impl JustificationImport<Block> for ForceFinalized {
	type Error = ConsensusError;

	fn import_justification(
		&self,
		hash: H256,
		_number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.0.finalize_block(BlockId::Hash(hash), Some(justification), true)
			.map_err(|_| ConsensusError::InvalidJustification.into())
	}
}

pub struct JustificationTestNet(TestNet);

impl TestNetFactory for JustificationTestNet {
	type Specialization = DummySpecialization;
	type Verifier = PassThroughVerifier;
	type PeerData = ();

	fn from_config(config: &ProtocolConfig) -> Self {
		JustificationTestNet(TestNet::from_config(config))
	}

	fn make_verifier(&self, client: PeersClient, config: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		self.0.make_verifier(client, config)
	}

	fn peer(&self, i: usize) -> &Peer<Self::PeerData, Self::Specialization> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, Self::Specialization>>> {
		self.0.peers()
	}

	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>)>(&mut self, closure: F) {
		self.0.mut_peers(closure)
	}

	fn started(&self) -> bool {
		self.0.started()
	}

	fn set_started(&mut self, new: bool) {
		self.0.set_started(new)
	}

	fn make_block_import(&self, client: PeersClient)
		-> (
			SharedBlockImport<Block>,
			Option<SharedJustificationImport<Block>>,
			Option<SharedFinalityProofImport<Block>>,
			Option<SharedFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(client.as_block_import(), Some(Arc::new(ForceFinalized(client))), None, None, Default::default())
	}
}
