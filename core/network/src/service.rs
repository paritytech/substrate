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
use std::{fs, io, path::Path};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use log::{warn, error, info};
use libp2p::core::swarm::NetworkBehaviour;
use libp2p::core::{nodes::Substream, transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::multihash::Multihash;
use futures::{prelude::*, sync::oneshot, sync::mpsc};
use parking_lot::{Mutex, RwLock};
use crate::protocol_behaviour::ProtocolBehaviour;
use crate::{behaviour::{Behaviour, BehaviourOut}, parse_str_addr};
use crate::{NetworkState, NetworkStateNotConnectedPeer, NetworkStatePeer};
use crate::{transport, config::NodeKeyConfig, config::NonReservedPeerMode};
use peerset::PeersetHandle;
use consensus::import_queue::{ImportQueue, Link, SharedFinalityProofRequestBuilder};
use runtime_primitives::{traits::{Block as BlockT, NumberFor}, ConsensusEngineId};

use crate::AlwaysBadChecker;
use crate::protocol::consensus_gossip::{ConsensusGossip, MessageRecipient as GossipMessageRecipient};
use crate::protocol::{event::Event, message::Message};
use crate::protocol::on_demand::RequestData;
use crate::protocol::{self, Context, CustomMessageOutcome, ConnectedPeer, PeerInfo};
use crate::protocol::sync::SyncState;
use crate::config::Params;
use crate::error::Error;
use crate::protocol::specialization::NetworkSpecialization;

/// Interval at which we update the `peers` field on the main thread.
const CONNECTED_PEERS_INTERVAL: Duration = Duration::from_millis(500);

pub use libp2p::PeerId;

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;

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
pub struct NetworkService<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> {
	/// Are we connected to any peer?
	is_offline: Arc<AtomicBool>,
	/// Are we actively catching up with the chain?
	is_major_syncing: Arc<AtomicBool>,
	/// Peers whom we are connected with.
	peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>>,
	/// Channel for networking messages processed by the background thread.
	network_chan: mpsc::UnboundedSender<NetworkMsg<B>>,
	/// Network service
	network: Arc<Mutex<Swarm<B, S, H>>>,
	/// Bandwidth logging system. Can be queried to know the average bandwidth consumed.
	bandwidth: Arc<transport::BandwidthSinks>,
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

		if let Some(ref path) = params.network_config.net_config_path {
			fs::create_dir_all(Path::new(path))?;
		}

		// List of multiaddresses that we know in the network.
		let mut known_addresses = Vec::new();
		let mut bootnodes = Vec::new();
		let mut reserved_nodes = Vec::new();

		// Process the bootnodes.
		for bootnode in params.network_config.boot_nodes.iter() {
			match parse_str_addr(bootnode) {
				Ok((peer_id, addr)) => {
					bootnodes.push(peer_id.clone());
					known_addresses.push((peer_id, addr));
				},
				Err(_) => warn!(target: "sub-libp2p", "Not a valid bootnode address: {}", bootnode),
			}
		}

		// Initialize the reserved peers.
		for reserved in params.network_config.reserved_nodes.iter() {
			if let Ok((peer_id, addr)) = parse_str_addr(reserved) {
				reserved_nodes.push(peer_id.clone());
				known_addresses.push((peer_id, addr));
			} else {
				warn!(target: "sub-libp2p", "Not a valid reserved node address: {}", reserved);
			}
		}

		// Build the peerset.
		let (peerset, peerset_handle) = peerset::Peerset::from_config(peerset::PeersetConfig {
			in_peers: params.network_config.in_peers,
			out_peers: params.network_config.out_peers,
			bootnodes,
			reserved_only: params.network_config.non_reserved_mode == NonReservedPeerMode::Deny,
			reserved_nodes,
		});

		// Private and public keys configuration.
		if let NodeKeyConfig::Secp256k1(_) = params.network_config.node_key {
			warn!(target: "sub-libp2p", "Secp256k1 keys are deprecated in favour of ed25519");
		}
		let local_identity = params.network_config.node_key.clone().into_keypair()?;
		let local_public = local_identity.public();
		let local_peer_id = local_public.clone().into_peer_id();
		info!(target: "sub-libp2p", "Local node identity is: {}", local_peer_id.to_base58());

		// Start in off-line mode, since we're not connected to any nodes yet.
		let is_offline = Arc::new(AtomicBool::new(true));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>> = Arc::new(Default::default());
		let protocol = ProtocolBehaviour::new(
			protocol::ProtocolConfig { roles: params.roles },
			params.chain,
			params.on_demand.as_ref().map(|od| od.checker().clone())
				.unwrap_or(Arc::new(AlwaysBadChecker)),
			params.specialization,
			params.transaction_pool,
			params.finality_proof_provider,
			params.protocol_id,
			&((protocol::MIN_VERSION as u8)..=(protocol::CURRENT_VERSION as u8)).collect::<Vec<u8>>(),
			peerset,
			peerset_handle.clone(),
		)?;

		// Build the swarm.
		let (mut swarm, bandwidth) = {
			let user_agent = format!(
				"{} ({})",
				params.network_config.client_version,
				params.network_config.node_name
			);
			let behaviour = Behaviour::new(
				protocol,
				user_agent,
				local_public,
				known_addresses,
				params.network_config.enable_mdns
			);
			let (transport, bandwidth) = transport::build_transport(
				local_identity,
				params.network_config.wasm_external_transport
			);
			(Swarm::<B, S, H>::new(transport, behaviour, local_peer_id.clone()), bandwidth)
		};

		// Listen on multiaddresses.
		for addr in &params.network_config.listen_addresses {
			if let Err(err) = Swarm::<B, S, H>::listen_on(&mut swarm, addr.clone()) {
				warn!(target: "sub-libp2p", "Can't listen on {} because: {:?}", addr, err)
			}
		}

		// Add external addresses.
		for addr in &params.network_config.public_addresses {
			Swarm::<B, S, H>::add_external_address(&mut swarm, addr.clone());
		}

		let network = Arc::new(Mutex::new(swarm));

		let service = Arc::new(NetworkService {
			bandwidth,
			is_offline: is_offline.clone(),
			is_major_syncing: is_major_syncing.clone(),
			network_chan,
			peers: peers.clone(),
			peerset: peerset_handle.clone(),
			network: network.clone(),
			protocol_sender: protocol_sender.clone(),
		});

		Ok(NetworkWorker {
			is_offline,
			is_major_syncing,
			network_service: network,
			peerset: peerset_handle,
			service,
			peers,
			import_queue: params.import_queue,
			network_port,
			protocol_rx,
			on_demand_in: params.on_demand.and_then(|od| od.extract_receiver()),
			connected_peers_interval: tokio_timer::Interval::new_interval(CONNECTED_PEERS_INTERVAL),
		})
	}

	/// Returns the downloaded bytes per second averaged over the past few seconds.
	pub fn average_download_per_sec(&self) -> u64 {
		self.service.bandwidth.average_download_per_sec()
	}

	/// Returns the uploaded bytes per second averaged over the past few seconds.
	pub fn average_upload_per_sec(&self) -> u64 {
		self.service.bandwidth.average_upload_per_sec()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.network_service.lock().user_protocol_mut().num_connected_peers()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.network_service.lock().user_protocol_mut().num_active_peers()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncState {
		self.network_service.lock().user_protocol_mut().sync_state()
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.network_service.lock().user_protocol_mut().best_seen_block()
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.network_service.lock().user_protocol_mut().num_sync_peers()
	}

	/// Return a `NetworkService` that can be shared through the code base and can be used to
	/// manipulate the worker.
	pub fn service(&self) -> &Arc<NetworkService<B, S, H>> {
		&self.service
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> NetworkService<B, S, H> {
	/// Returns the network identity of the node.
	pub fn local_peer_id(&self) -> PeerId {
		Swarm::<B, S, H>::local_peer_id(&*self.network.lock()).clone()
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
	pub fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}

	/// Get a value.
	pub fn get_value(&mut self, key: &Multihash) {
		self.network.lock().get_value(key);
	}

	/// Put a value.
	pub fn put_value(&mut self, key: Multihash, value: Vec<u8>) {
		self.network.lock().put_value(key, value);
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> NetworkService<B, S, H> {
	/// Get network state.
	pub fn network_state(&self) -> NetworkState {
		let mut swarm = self.network.lock();
		let open = swarm.user_protocol().open_peers().cloned().collect::<Vec<_>>();

		let connected_peers = {
			let swarm = &mut *swarm;
			open.iter().filter_map(move |peer_id| {
				let known_addresses = NetworkBehaviour::addresses_of_peer(&mut **swarm, peer_id)
					.into_iter().collect();

				let endpoint = if let Some(e) = swarm.node(peer_id).map(|i| i.endpoint()) {
					e.clone().into()
				} else {
					error!(target: "sub-libp2p", "Found state inconsistency between custom protocol \
						and debug information about {:?}", peer_id);
					return None
				};

				Some((peer_id.to_base58(), NetworkStatePeer {
					endpoint,
					version_string: swarm.node(peer_id)
						.and_then(|i| i.client_version().map(|s| s.to_owned())).clone(),
					latest_ping_time: swarm.node(peer_id).and_then(|i| i.latest_ping()),
					enabled: swarm.user_protocol().is_enabled(&peer_id),
					open: swarm.user_protocol().is_open(&peer_id),
					known_addresses,
				}))
			}).collect()
		};

		let not_connected_peers = {
			let swarm = &mut *swarm;
			let list = swarm.known_peers().filter(|p| open.iter().all(|n| n != *p))
				.cloned().collect::<Vec<_>>();
			list.into_iter().map(move |peer_id| {
				(peer_id.to_base58(), NetworkStateNotConnectedPeer {
					version_string: swarm.node(&peer_id)
						.and_then(|i| i.client_version().map(|s| s.to_owned())).clone(),
					latest_ping_time: swarm.node(&peer_id).and_then(|i| i.latest_ping()),
					known_addresses: NetworkBehaviour::addresses_of_peer(&mut **swarm, &peer_id)
						.into_iter().collect(),
				})
			}).collect()
		};

		NetworkState {
			peer_id: Swarm::<B, S, H>::local_peer_id(&swarm).to_base58(),
			listened_addresses: Swarm::<B, S, H>::listeners(&swarm).cloned().collect(),
			external_addresses: Swarm::<B, S, H>::external_addresses(&swarm).cloned().collect(),
			average_download_per_sec: self.bandwidth.average_download_per_sec(),
			average_upload_per_sec: self.bandwidth.average_upload_per_sec(),
			connected_peers,
			not_connected_peers,
			peerset: swarm.user_protocol_mut().peerset_debug_info(),
		}
	}

	/// Get currently connected peers.
	///
	/// > **Warning**: This method can return outdated information and should only ever be used
	/// > when obtaining outdated information is acceptable.
	pub fn peers_debug_info(&self) -> Vec<(PeerId, PeerInfo<B>)> {
		let peers = (*self.peers.read()).clone();
		peers.into_iter().map(|(idx, connected)| (idx, connected.peer_info)).collect()
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT>
	::consensus::SyncOracle for NetworkService<B, S, H> {
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing()
	}

	fn is_offline(&self) -> bool {
		self.is_offline.load(Ordering::Relaxed)
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

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> ManageNetwork for NetworkService<B, S, H> {
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
	/// The network service that can be extracted and shared through the codebase.
	service: Arc<NetworkService<B, S, H>>,
	network_service: Arc<Mutex<Swarm<B, S, H>>>,
	peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>>,
	import_queue: Box<dyn ImportQueue<B>>,
	network_port: mpsc::UnboundedReceiver<NetworkMsg<B>>,
	protocol_rx: mpsc::UnboundedReceiver<ProtocolMsg<B, S>>,
	peerset: PeersetHandle,
	on_demand_in: Option<mpsc::UnboundedReceiver<RequestData<B>>>,

	/// Interval at which we update the `connected_peers` Arc.
	connected_peers_interval: tokio_timer::Interval,
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> Future for NetworkWorker<B, S, H> {
	type Item = ();
	type Error = io::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// Implementation of `import_queue::Link` trait using the available local variables.
		struct NetworkLink<'a, B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
			protocol: &'a mut Swarm<B, S, H>,
		}
		impl<'a, B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Link<B> for NetworkLink<'a, B, S, H> {
			fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
				self.protocol.user_protocol_mut().block_imported(&hash, number)
			}
			fn blocks_processed(&mut self, hashes: Vec<B::Hash>, has_error: bool) {
				self.protocol.user_protocol_mut().blocks_processed(hashes, has_error)
			}
			fn justification_imported(&mut self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
				self.protocol.user_protocol_mut().justification_import_result(hash.clone(), number, success);
				if !success {
					info!("Invalid justification provided by {} for #{}", who, hash);
					self.protocol.user_protocol_mut().disconnect_peer(&who);
					self.protocol.user_protocol_mut().report_peer(who, i32::min_value());
				}
			}
			fn clear_justification_requests(&mut self) {
				self.protocol.user_protocol_mut().clear_justification_requests()
			}
			fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
				self.protocol.user_protocol_mut().request_justification(hash, number)
			}
			fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
				self.protocol.user_protocol_mut().request_finality_proof(hash, number)
			}
			fn finality_proof_imported(
				&mut self,
				who: PeerId,
				request_block: (B::Hash, NumberFor<B>),
				finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
			) {
				let success = finalization_result.is_ok();
				self.protocol.user_protocol_mut().finality_proof_import_result(request_block, finalization_result);
				if !success {
					info!("Invalid finality proof provided by {} for #{}", who, request_block.0);
					self.protocol.user_protocol_mut().disconnect_peer(&who);
					self.protocol.user_protocol_mut().report_peer(who, i32::min_value());
				}
			}
			fn report_peer(&mut self, who: PeerId, reputation_change: i32) {
				self.protocol.user_protocol_mut().report_peer(who, reputation_change)
			}
			fn restart(&mut self) {
				self.protocol.user_protocol_mut().restart()
			}
			fn set_finality_proof_request_builder(&mut self, builder: SharedFinalityProofRequestBuilder<B>) {
				self.protocol.user_protocol_mut().set_finality_proof_request_builder(builder)
			}
		}

		{
			let mut network_service = self.network_service.lock();
			let mut link = NetworkLink {
				protocol: &mut network_service,
			};
			self.import_queue.poll_actions(&mut link);
		}

		while let Ok(Async::Ready(_)) = self.connected_peers_interval.poll() {
			let mut network_service = self.network_service.lock();
			let infos = network_service.user_protocol_mut().peers_info().map(|(id, info)| {
				(id.clone(), ConnectedPeer { peer_info: info.clone() })
			}).collect();
			*self.peers.write() = infos;
		}

		// Check for new incoming on-demand requests.
		if let Some(on_demand_in) = self.on_demand_in.as_mut() {
			while let Ok(Async::Ready(Some(rq))) = on_demand_in.poll() {
				let mut network_service = self.network_service.lock();
				network_service.user_protocol_mut().add_on_demand_request(rq);
			}
		}

		loop {
			match self.network_port.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(NetworkMsg::Outgoing(who, outgoing_message)))) =>
					self.network_service.lock().user_protocol_mut().send_packet(&who, outgoing_message),
				Ok(Async::Ready(Some(NetworkMsg::ReportPeer(who, reputation)))) =>
					self.peerset.report_peer(who, reputation),
				Ok(Async::Ready(Some(NetworkMsg::DisconnectPeer(who)))) =>
					self.network_service.lock().user_protocol_mut().disconnect_peer(&who),

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

			match msg {
				ProtocolMsg::BlockImported(hash, header) =>
					network_service.user_protocol_mut().on_block_imported(hash, &header),
				ProtocolMsg::BlockFinalized(hash, header) =>
					network_service.user_protocol_mut().on_block_finalized(hash, &header),
				ProtocolMsg::ExecuteWithSpec(task) => {
					let (protocol, mut net_out) = network_service.user_protocol_mut().protocol_context_lock();
					let (mut context, spec) = protocol.specialization_lock(&mut net_out);
					task.call_box(spec, &mut context);
				},
				ProtocolMsg::ExecuteWithGossip(task) => {
					let (protocol, mut net_out) = network_service.user_protocol_mut().protocol_context_lock();
					let (mut context, gossip) = protocol.consensus_gossip_lock(&mut net_out);
					task.call_box(gossip, &mut context);
				}
				ProtocolMsg::GossipConsensusMessage(topic, engine_id, message, recipient) =>
					network_service.user_protocol_mut().gossip_consensus_message(topic, engine_id, message, recipient),
				ProtocolMsg::BlocksProcessed(hashes, has_error) =>
					network_service.user_protocol_mut().blocks_processed(hashes, has_error),
				ProtocolMsg::RestartSync =>
					network_service.user_protocol_mut().restart(),
				ProtocolMsg::AnnounceBlock(hash) =>
					network_service.user_protocol_mut().announce_block(hash),
				ProtocolMsg::BlockImportedSync(hash, number) =>
					network_service.user_protocol_mut().block_imported(&hash, number),
				ProtocolMsg::ClearJustificationRequests =>
					network_service.user_protocol_mut().clear_justification_requests(),
				ProtocolMsg::RequestJustification(hash, number) =>
					network_service.user_protocol_mut().request_justification(&hash, number),
				ProtocolMsg::JustificationImportResult(hash, number, success) =>
					network_service.user_protocol_mut().justification_import_result(hash, number, success),
				ProtocolMsg::SetFinalityProofRequestBuilder(builder) =>
					network_service.user_protocol_mut().set_finality_proof_request_builder(builder),
				ProtocolMsg::RequestFinalityProof(hash, number) =>
					network_service.user_protocol_mut().request_finality_proof(&hash, number),
				ProtocolMsg::FinalityProofImportResult(requested_block, finalziation_result) =>
					network_service.user_protocol_mut()
						.finality_proof_import_result(requested_block, finalziation_result),
				ProtocolMsg::PropagateExtrinsics =>
					network_service.user_protocol_mut().propagate_extrinsics(),
				#[cfg(any(test, feature = "test-helpers"))]
				ProtocolMsg::Tick => network_service.user_protocol_mut().tick(),
				#[cfg(any(test, feature = "test-helpers"))]
				ProtocolMsg::Synchronize => {},
			}
		}

		loop {
			let mut network_service = self.network_service.lock();
			let poll_value = network_service.poll();

			let outcome = match poll_value {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(BehaviourOut::Behaviour(outcome)))) => outcome,
				Ok(Async::Ready(Some(BehaviourOut::Dht(ev)))) => {
					network_service.user_protocol_mut()
						.on_event(Event::Dht(ev));
					CustomMessageOutcome::None
				},
				Ok(Async::Ready(None)) => CustomMessageOutcome::None,
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

		let mut network_service = self.network_service.lock();
		self.is_offline.store(network_service.user_protocol_mut().num_connected_peers() == 0, Ordering::Relaxed);
		self.is_major_syncing.store(match network_service.user_protocol_mut().sync_state() {
			SyncState::Idle => false,
			SyncState::Downloading => true,
		}, Ordering::Relaxed);

		Ok(Async::NotReady)
	}
}

/// The libp2p swarm, customized for our needs.
type Swarm<B, S, H> = libp2p::core::Swarm<
	Boxed<(PeerId, StreamMuxerBox), io::Error>,
	Behaviour<ProtocolBehaviour<B, S, H>, CustomMessageOutcome<B>, Substream<StreamMuxerBox>>
>;
