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

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use log::{warn, debug, error, info};
use futures::{prelude::*, sync::oneshot, sync::mpsc};
use parking_lot::{Mutex, RwLock};
use network_libp2p::{start_service, parse_str_addr, Service as Libp2pNetService, ServiceEvent as Libp2pNetServiceEvent};
use network_libp2p::{RegisteredProtocol, NetworkState};
use peerset::PeersetHandle;
use consensus::import_queue::{ImportQueue, Link, SharedFinalityProofRequestBuilder};
use runtime_primitives::{traits::{Block as BlockT, NumberFor}, ConsensusEngineId};

use crate::AlwaysBadChecker;
use crate::chain::FinalityProofProvider;
use crate::protocol::consensus_gossip::{ConsensusGossip, MessageRecipient as GossipMessageRecipient};
use crate::protocol::message::Message;
use crate::protocol::on_demand::RequestData;
use crate::protocol::{self, Context, CustomMessageOutcome, Protocol, ConnectedPeer};
use crate::protocol::{ProtocolStatus, PeerInfo, NetworkOut};
use crate::config::Params;
use crate::error::Error;
use crate::protocol::specialization::NetworkSpecialization;

/// Interval at which we send status updates on the SyncProvider status stream.
const STATUS_INTERVAL: Duration = Duration::from_millis(5000);
/// Interval at which we update the `peers` field on the main thread.
const CONNECTED_PEERS_INTERVAL: Duration = Duration::from_millis(500);

pub use network_libp2p::PeerId;

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;

/// Sync status
pub trait SyncProvider<B: BlockT>: Send + Sync {
	/// Get a stream of sync statuses.
	fn status(&self) -> mpsc::UnboundedReceiver<ProtocolStatus<B>>;
	/// Get network state.
	fn network_state(&self) -> NetworkState;

	/// Get currently connected peers.
	///
	/// > **Warning**: This method can return outdated information and should only ever be used
	/// > when obtaining outdated information is acceptable.
	fn peers_debug_info(&self) -> Vec<(PeerId, PeerInfo<B>)>;

	/// Are we in the process of downloading the chain?
	fn is_major_syncing(&self) -> bool;
}

/// Minimum Requirements for a Hash within Networking
pub trait ExHashT:
	::std::hash::Hash + Eq + ::std::fmt::Debug + Clone + Send + Sync + 'static
{
}
impl<T> ExHashT for T where
	T: ::std::hash::Hash + Eq + ::std::fmt::Debug + Clone + Send + Sync + 'static
{
}

/// Transaction pool interface
pub trait TransactionPool<H: ExHashT, B: BlockT>: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(H, B::Extrinsic)>;
	/// Import a transaction into the pool.
	fn import(&self, transaction: &B::Extrinsic) -> Option<H>;
	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>);
}

/// A link implementation that connects to the network.
#[derive(Clone)]
pub struct NetworkLink<B: BlockT, S: NetworkSpecialization<B>> {
	/// The protocol sender
	pub(crate) protocol_sender: mpsc::UnboundedSender<ProtocolMsg<B, S>>,
	/// The network sender
	pub(crate) network_sender: mpsc::UnboundedSender<NetworkMsg<B>>,
}

impl<B: BlockT, S: NetworkSpecialization<B>> Link<B> for NetworkLink<B, S> {
	fn block_imported(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlockImportedSync(hash.clone(), number));
	}

	fn blocks_processed(&self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlocksProcessed(processed_blocks, has_error));
	}

	fn justification_imported(&self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::JustificationImportResult(hash.clone(), number, success));
		if !success {
			info!("Invalid justification provided by {} for #{}", who, hash);
			let _ = self.network_sender.unbounded_send(NetworkMsg::ReportPeer(who.clone(), i32::min_value()));
			let _ = self.network_sender.unbounded_send(NetworkMsg::DisconnectPeer(who.clone()));
		}
	}

	fn clear_justification_requests(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::ClearJustificationRequests);
	}

	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	fn request_finality_proof(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RequestFinalityProof(
			hash.clone(),
			number,
		));
	}

	fn finality_proof_imported(
		&self,
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

	fn report_peer(&self, who: PeerId, reputation_change: i32) {
		let _ = self.network_sender.unbounded_send(NetworkMsg::ReportPeer(who, reputation_change));
	}

	fn restart(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RestartSync);
	}

	fn set_finality_proof_request_builder(&self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::SetFinalityProofRequestBuilder(request_builder));
	}
}

/// A cloneable handle for reporting cost/benefits of peers.
#[derive(Clone)]
pub struct ReportHandle {
	inner: PeersetHandle, // wraps it so we don't have to worry about breaking API.
}

impl ReportHandle {
	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: i32) {
		self.inner.report_peer(who, cost_benefit);
	}
}

/// Substrate network service. Handles network IO and manages connectivity.
pub struct NetworkService<B: BlockT + 'static, S: NetworkSpecialization<B>> {
	/// Sinks to propagate status updates.
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<ProtocolStatus<B>>>>>,
	/// Are we connected to any peer?
	is_offline: Arc<AtomicBool>,
	/// Are we actively catching up with the chain?
	is_major_syncing: Arc<AtomicBool>,
	/// Peers whom we are connected with.
	peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>>,
	/// Channel for networking messages processed by the background thread.
	network_chan: mpsc::UnboundedSender<NetworkMsg<B>>,
	/// Network service
	network: Arc<Mutex<Libp2pNetService<Message<B>>>>,
	/// Peerset manager (PSM); manages the reputation of nodes and indicates the network which
	/// nodes it should be connected to or not.
	peerset: PeersetHandle,
	/// Protocol sender
	protocol_sender: mpsc::UnboundedSender<ProtocolMsg<B, S>>,
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> NetworkWorker<B, S, H> {
	/// Creates the network service.
	///
	/// Returns a `NetworkWorker` that implements `Future` and must be regularly polled in order
	/// for the network processing to advance. From it, you can extract a `NetworkService` using
	/// `worker.service()`. The `NetworkService` can be shared through the codebase.
	pub fn new(
		params: Params<B, S, H>,
	) -> Result<NetworkWorker<B, S, H>, Error> {
		let (network_chan, network_port) = mpsc::unbounded();
		let (protocol_sender, protocol_rx) = mpsc::unbounded();
		let status_sinks = Arc::new(Mutex::new(Vec::new()));

		// connect the import-queue to the network service.
		let link = NetworkLink {
			protocol_sender: protocol_sender.clone(),
			network_sender: network_chan.clone(),
		};
		params.import_queue.start(Box::new(link))?;

		// Start in off-line mode, since we're not connected to any nodes yet.
		let is_offline = Arc::new(AtomicBool::new(true));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>> = Arc::new(Default::default());
		let protocol = Protocol::new(
			protocol::ProtocolConfig { roles: params.roles },
			params.chain,
			params.on_demand.as_ref().map(|od| od.checker().clone())
				.unwrap_or(Arc::new(AlwaysBadChecker)),
			params.specialization,
		)?;
		let versions: Vec<_> = ((protocol::MIN_VERSION as u8)..=(protocol::CURRENT_VERSION as u8)).collect();
		let registered = RegisteredProtocol::new(params.protocol_id, &versions);

		// Start the main service.
		let (network, peerset) = match start_service(params.network_config, registered) {
			Ok((network, peerset)) => (Arc::new(Mutex::new(network)), peerset),
			Err(err) => {
				warn!("Error starting network: {}", err);
				return Err(err.into())
			},
		};

		let service = Arc::new(NetworkService {
			status_sinks: status_sinks.clone(),
			is_offline: is_offline.clone(),
			is_major_syncing: is_major_syncing.clone(),
			network_chan,
			peers: peers.clone(),
			peerset: peerset.clone(),
			network: network.clone(),
			protocol_sender: protocol_sender.clone(),
		});

		Ok(NetworkWorker {
			is_offline,
			is_major_syncing,
			network_service: network,
			peerset,
			service,
			protocol,
			peers,
			import_queue: params.import_queue,
			transaction_pool: params.transaction_pool,
			finality_proof_provider: params.finality_proof_provider,
			network_port,
			protocol_rx,
			status_sinks,
			on_demand_in: params.on_demand.and_then(|od| od.extract_receiver()),
			status_interval: tokio_timer::Interval::new_interval(STATUS_INTERVAL),
			connected_peers_interval: tokio_timer::Interval::new_interval(CONNECTED_PEERS_INTERVAL),
		})
	}

	/// Return a `NetworkService` that can be shared through the code base and can be used to
	/// manipulate the worker.
	pub fn service(&self) -> &Arc<NetworkService<B, S>> {
		&self.service
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> NetworkService<B, S> {
	/// Returns the downloaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_download_per_sec(&self) -> u64 {
		self.network.lock().average_download_per_sec()
	}

	/// Returns the uploaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_upload_per_sec(&self) -> u64 {
		self.network.lock().average_upload_per_sec()
	}

	/// Returns the network identity of the node.
	pub fn local_peer_id(&self) -> PeerId {
		self.network.lock().peer_id().clone()
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::BlockImported(hash, header));
	}

	/// Called when a new block is finalized by the client.
	pub fn on_block_finalized(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::BlockFinalized(hash, header));
	}

	/// Called when new transactons are imported by the client.
	pub fn trigger_repropagate(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::PropagateExtrinsics);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&self, hash: B::Hash) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::AnnounceBlock(hash));
	}

	/// Send a consensus message through the gossip
	pub fn gossip_consensus_message(
		&self,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
		recipient: GossipMessageRecipient,
	) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::GossipConsensusMessage(
				topic, engine_id, message, recipient,
			));
	}

	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: i32) {
		self.peerset.report_peer(who, cost_benefit);
	}

	/// Send a message to the given peer. Has no effect if we're not connected to this peer.
	///
	/// This method is extremely poor in terms of API and should be eventually removed.
	pub fn disconnect_peer(&self, who: PeerId) {
		let _ = self.network_chan.unbounded_send(NetworkMsg::DisconnectPeer(who));
	}

	/// Send a message to the given peer. Has no effect if we're not connected to this peer.
	///
	/// This method is extremely poor in terms of API and should be eventually removed.
	pub fn send_request(&self, who: PeerId, message: Message<B>) {
		let _ = self.network_chan.unbounded_send(NetworkMsg::Outgoing(who, message));
	}

	/// Execute a closure with the chain-specific network specialization.
	pub fn with_spec<F>(&self, f: F)
		where F: FnOnce(&mut S, &mut dyn Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::ExecuteWithSpec(Box::new(f)));
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<B>, &mut dyn Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::ExecuteWithGossip(Box::new(f)));
	}

	/// Are we in the process of downloading the chain?
	/// Used by both SyncProvider and SyncOracle.
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ::consensus::SyncOracle for NetworkService<B, S> {
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing()
	}

	fn is_offline(&self) -> bool {
		self.is_offline.load(Ordering::Relaxed)
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> SyncProvider<B> for NetworkService<B, S> {
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing()
	}

	/// Get sync status
	fn status(&self) -> mpsc::UnboundedReceiver<ProtocolStatus<B>> {
		let (sink, stream) = mpsc::unbounded();
		self.status_sinks.lock().push(sink);
		stream
	}

	fn network_state(&self) -> NetworkState {
		self.network.lock().state()
	}

	fn peers_debug_info(&self) -> Vec<(PeerId, PeerInfo<B>)> {
		let peers = (*self.peers.read()).clone();
		peers.into_iter().map(|(idx, connected)| (idx, connected.peer_info)).collect()
	}
}

/// Trait for managing network
pub trait ManageNetwork {
	/// Set to allow unreserved peers to connect
	fn accept_unreserved_peers(&self);
	/// Set to deny unreserved peers to connect
	fn deny_unreserved_peers(&self);
	/// Remove reservation for the peer
	fn remove_reserved_peer(&self, peer: PeerId);
	/// Add reserved peer
	fn add_reserved_peer(&self, peer: String) -> Result<(), String>;
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ManageNetwork for NetworkService<B, S> {
	fn accept_unreserved_peers(&self) {
		self.peerset.set_reserved_only(false);
	}

	fn deny_unreserved_peers(&self) {
		self.peerset.set_reserved_only(true);
	}

	fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset.remove_reserved_peer(peer);
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		let (peer_id, addr) = parse_str_addr(&peer).map_err(|e| format!("{:?}", e))?;
		self.peerset.add_reserved_peer(peer_id.clone());
		self.network.lock().add_known_address(peer_id, addr);
		Ok(())
	}
}

/// Messages to be handled by Libp2pNetService.
#[derive(Debug)]
pub enum NetworkMsg<B: BlockT + 'static> {
	/// Send an outgoing custom message.
	Outgoing(PeerId, Message<B>),
	/// Disconnect a peer we're connected to, or do nothing if we're not connected.
	DisconnectPeer(PeerId),
	/// Performs a reputation adjustement on a peer.
	ReportPeer(PeerId, i32),
	/// Synchronization response.
	#[cfg(any(test, feature = "test-helpers"))]
	Synchronized,
}

/// Messages sent to Protocol from elsewhere inside the system.
pub enum ProtocolMsg<B: BlockT, S: NetworkSpecialization<B>> {
	/// A batch of blocks has been processed, with or without errors.
	BlocksProcessed(Vec<B::Hash>, bool),
	/// Tell protocol to restart sync.
	RestartSync,
	/// Tell protocol to propagate extrinsics.
	PropagateExtrinsics,
	/// Tell protocol that a block was imported (sent by the import-queue).
	BlockImportedSync(B::Hash, NumberFor<B>),
	/// Tell protocol to clear all pending justification requests.
	ClearJustificationRequests,
	/// Tell protocol to request justification for a block.
	RequestJustification(B::Hash, NumberFor<B>),
	/// Inform protocol whether a justification was successfully imported.
	JustificationImportResult(B::Hash, NumberFor<B>, bool),
	/// Set finality proof request builder.
	SetFinalityProofRequestBuilder(SharedFinalityProofRequestBuilder<B>),
	/// Tell protocol to request finality proof for a block.
	RequestFinalityProof(B::Hash, NumberFor<B>),
	/// Inform protocol whether a finality proof was successfully imported.
	FinalityProofImportResult((B::Hash, NumberFor<B>), Result<(B::Hash, NumberFor<B>), ()>),
	/// Propagate a block to peers.
	AnnounceBlock(B::Hash),
	/// A block has been imported (sent by the client).
	BlockImported(B::Hash, B::Header),
	/// A block has been finalized (sent by the client).
	BlockFinalized(B::Hash, B::Header),
	/// Execute a closure with the chain-specific network specialization.
	ExecuteWithSpec(Box<dyn SpecTask<B, S> + Send + 'static>),
	/// Execute a closure with the consensus gossip.
	ExecuteWithGossip(Box<dyn GossipTask<B> + Send + 'static>),
	/// Incoming gossip consensus message.
	GossipConsensusMessage(B::Hash, ConsensusEngineId, Vec<u8>, GossipMessageRecipient),
	/// Tell protocol to perform regular maintenance.
	#[cfg(any(test, feature = "test-helpers"))]
	Tick,
	/// Synchronization request.
	#[cfg(any(test, feature = "test-helpers"))]
	Synchronize,
}

/// A task, consisting of a user-provided closure, to be executed on the Protocol thread.
pub trait SpecTask<B: BlockT, S: NetworkSpecialization<B>> {
	fn call_box(self: Box<Self>, spec: &mut S, context: &mut dyn Context<B>);
}

impl<B: BlockT, S: NetworkSpecialization<B>, F: FnOnce(&mut S, &mut dyn Context<B>)> SpecTask<B, S> for F {
	fn call_box(self: Box<F>, spec: &mut S, context: &mut dyn Context<B>) {
		(*self)(spec, context)
	}
}

/// A task, consisting of a user-provided closure, to be executed on the Protocol thread.
pub trait GossipTask<B: BlockT> {
	fn call_box(self: Box<Self>, gossip: &mut ConsensusGossip<B>, context: &mut dyn Context<B>);
}

impl<B: BlockT, F: FnOnce(&mut ConsensusGossip<B>, &mut dyn Context<B>)> GossipTask<B> for F {
	fn call_box(self: Box<F>, gossip: &mut ConsensusGossip<B>, context: &mut dyn Context<B>) {
		(*self)(gossip, context)
	}
}

/// Future tied to the `Network` service and that must be polled in order for the network to
/// advance.
#[must_use = "The NetworkWorker must be polled in order for the network to work"]
pub struct NetworkWorker<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> {
	is_offline: Arc<AtomicBool>,
	is_major_syncing: Arc<AtomicBool>,
	protocol: Protocol<B, S, H>,
	/// The network service that can be extracted and shared through the codebase.
	service: Arc<NetworkService<B, S>>,
	network_service: Arc<Mutex<Libp2pNetService<Message<B>>>>,
	peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>>,
	import_queue: Box<dyn ImportQueue<B>>,
	transaction_pool: Arc<dyn TransactionPool<H, B>>,
	finality_proof_provider: Option<Arc<dyn FinalityProofProvider<B>>>,
	network_port: mpsc::UnboundedReceiver<NetworkMsg<B>>,
	protocol_rx: mpsc::UnboundedReceiver<ProtocolMsg<B, S>>,
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<ProtocolStatus<B>>>>>,
	peerset: PeersetHandle,
	on_demand_in: Option<mpsc::UnboundedReceiver<RequestData<B>>>,

	/// Interval at which we send status updates on the `status_sinks`.
	status_interval: tokio_timer::Interval,
	/// Interval at which we update the `connected_peers` Arc.
	connected_peers_interval: tokio_timer::Interval,
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> Future for NetworkWorker<B, S, H> {
	type Item = ();
	type Error = io::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// Implementation of `protocol::NetworkOut` using the available local variables.
		struct Context<'a, B: BlockT>(&'a mut Libp2pNetService<Message<B>>, &'a PeersetHandle);
		impl<'a, B: BlockT> NetworkOut<B> for Context<'a, B> {
			fn report_peer(&mut self, who: PeerId, reputation: i32) {
				self.1.report_peer(who, reputation)
			}
			fn disconnect_peer(&mut self, who: PeerId) {
				self.0.drop_node(&who)
			}
			fn send_message(&mut self, who: PeerId, message: Message<B>) {
				self.0.send_custom_message(&who, message)
			}
		}

		while let Ok(Async::Ready(_)) = self.status_interval.poll() {
			let status = self.protocol.status();
			self.status_sinks.lock().retain(|sink| sink.unbounded_send(status.clone()).is_ok());
		}

		while let Ok(Async::Ready(_)) = self.connected_peers_interval.poll() {
			let infos = self.protocol.peers_info().map(|(id, info)| {
				(id.clone(), ConnectedPeer { peer_info: info.clone() })
			}).collect();
			*self.peers.write() = infos;
		}

		match self.protocol.poll(&mut Context(&mut self.network_service.lock(), &self.peerset), &*self.transaction_pool) {
			Ok(Async::Ready(v)) => void::unreachable(v),
			Ok(Async::NotReady) => {}
			Err(err) => void::unreachable(err),
		}

		// Check for new incoming on-demand requests.
		if let Some(on_demand_in) = self.on_demand_in.as_mut() {
			while let Ok(Async::Ready(Some(rq))) = on_demand_in.poll() {
				self.protocol.add_on_demand_request(&mut Context(&mut self.network_service.lock(), &self.peerset), rq);
			}
		}

		loop {
			match self.network_port.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(NetworkMsg::Outgoing(who, outgoing_message)))) =>
					self.network_service.lock().send_custom_message(&who, outgoing_message),
				Ok(Async::Ready(Some(NetworkMsg::ReportPeer(who, reputation)))) =>
					self.peerset.report_peer(who, reputation),
				Ok(Async::Ready(Some(NetworkMsg::DisconnectPeer(who)))) =>
					self.network_service.lock().drop_node(&who),

				#[cfg(any(test, feature = "test-helpers"))]
				Ok(Async::Ready(Some(NetworkMsg::Synchronized))) => {}

				Ok(Async::Ready(None)) | Err(_) => return Ok(Async::Ready(())),
			}
		}

		loop {
			let msg = match self.protocol_rx.poll() {
				Ok(Async::Ready(Some(msg))) => msg,
				Ok(Async::Ready(None)) | Err(_) => return Ok(Async::Ready(())),
				Ok(Async::NotReady) => break,
			};

			let mut network_service = self.network_service.lock();
			let mut network_out = Context(&mut network_service, &self.peerset);

			match msg {
				ProtocolMsg::BlockImported(hash, header) =>
					self.protocol.on_block_imported(&mut network_out, hash, &header),
				ProtocolMsg::BlockFinalized(hash, header) =>
					self.protocol.on_block_finalized(&mut network_out, hash, &header),
				ProtocolMsg::ExecuteWithSpec(task) => {
					let (mut context, spec) = self.protocol.specialization_lock(&mut network_out);
					task.call_box(spec, &mut context);
				},
				ProtocolMsg::ExecuteWithGossip(task) => {
					let (mut context, gossip) = self.protocol.consensus_gossip_lock(&mut network_out);
					task.call_box(gossip, &mut context);
				}
				ProtocolMsg::GossipConsensusMessage(topic, engine_id, message, recipient) =>
					self.protocol.gossip_consensus_message(&mut network_out, topic, engine_id, message, recipient),
				ProtocolMsg::BlocksProcessed(hashes, has_error) =>
					self.protocol.blocks_processed(&mut network_out, hashes, has_error),
				ProtocolMsg::RestartSync =>
					self.protocol.restart(&mut network_out),
				ProtocolMsg::AnnounceBlock(hash) =>
					self.protocol.announce_block(&mut network_out, hash),
				ProtocolMsg::BlockImportedSync(hash, number) =>
					self.protocol.block_imported(&hash, number),
				ProtocolMsg::ClearJustificationRequests =>
					self.protocol.clear_justification_requests(),
				ProtocolMsg::RequestJustification(hash, number) =>
					self.protocol.request_justification(&mut network_out, &hash, number),
				ProtocolMsg::JustificationImportResult(hash, number, success) =>
					self.protocol.justification_import_result(hash, number, success),
				ProtocolMsg::SetFinalityProofRequestBuilder(builder) =>
					self.protocol.set_finality_proof_request_builder(builder),
				ProtocolMsg::RequestFinalityProof(hash, number) =>
					self.protocol.request_finality_proof(&mut network_out, &hash, number),
				ProtocolMsg::FinalityProofImportResult(requested_block, finalziation_result) =>
					self.protocol.finality_proof_import_result(requested_block, finalziation_result),
				ProtocolMsg::PropagateExtrinsics =>
					self.protocol.propagate_extrinsics(&mut network_out, &*self.transaction_pool),
				#[cfg(any(test, feature = "test-helpers"))]
				ProtocolMsg::Tick => self.protocol.tick(&mut network_out),
				#[cfg(any(test, feature = "test-helpers"))]
				ProtocolMsg::Synchronize => {},
			}
		}

		loop {
			let mut network_service = self.network_service.lock();
			let poll_value = network_service.poll();
			let mut network_out = Context(&mut network_service, &self.peerset);

			let outcome = match poll_value {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(Libp2pNetServiceEvent::OpenedCustomProtocol { peer_id, version, debug_info, .. }))) => {
					debug_assert!(
						version <= protocol::CURRENT_VERSION as u8
						&& version >= protocol::MIN_VERSION as u8
					);
					self.protocol.on_peer_connected(&mut network_out, peer_id, debug_info);
					CustomMessageOutcome::None
				}
				Ok(Async::Ready(Some(Libp2pNetServiceEvent::ClosedCustomProtocol { peer_id, debug_info, .. }))) => {
					self.protocol.on_peer_disconnected(&mut network_out, peer_id, debug_info);
					CustomMessageOutcome::None
				},
				Ok(Async::Ready(Some(Libp2pNetServiceEvent::CustomMessage { peer_id, message, .. }))) =>
					self.protocol.on_custom_message(
						&mut network_out,
						&*self.transaction_pool,
						peer_id,
						message,
						self.finality_proof_provider.as_ref().map(|p| &**p)
					),
				Ok(Async::Ready(Some(Libp2pNetServiceEvent::Clogged { peer_id, messages, .. }))) => {
					debug!(target: "sync", "{} clogging messages:", messages.len());
					for msg in messages.into_iter().take(5) {
						debug!(target: "sync", "{:?}", msg);
						self.protocol.on_clogged_peer(&mut network_out, peer_id.clone(), Some(msg));
					}
					CustomMessageOutcome::None
				}
				Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
				Err(err) => {
					error!(target: "sync", "Error in the network: {:?}", err);
					return Err(err)
				}
			};

			match outcome {
				CustomMessageOutcome::BlockImport(origin, blocks) =>
					self.import_queue.import_blocks(origin, blocks),
				CustomMessageOutcome::JustificationImport(origin, hash, nb, justification) =>
					self.import_queue.import_justification(origin, hash, nb, justification),
				CustomMessageOutcome::FinalityProofImport(origin, hash, nb, proof) =>
					self.import_queue.import_finality_proof(origin, hash, nb, proof),
				CustomMessageOutcome::None => {}
			}
		}

		self.is_offline.store(self.protocol.is_offline(), Ordering::Relaxed);
		self.is_major_syncing.store(self.protocol.is_major_syncing(), Ordering::Relaxed);

		Ok(Async::NotReady)
	}
}
