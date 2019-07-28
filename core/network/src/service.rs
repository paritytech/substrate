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

//! Main entry point of the substrate-network crate.
//!
//! There are two main structs in this module: [`NetworkWorker`] and [`NetworkService`].
//! The [`NetworkWorker`] *is* the network and implements the `Future` trait. It must be polled in
//! order fo the network to advance.
//! The [`NetworkService`] is merely a shared version of the [`NetworkWorker`]. You can obtain an
//! `Arc<NetworkService>` by calling [`NetworkWorker::service`].
//!
//! The methods of the [`NetworkService`] are implemented by sending a message over a channel,
//! which is then processed by [`NetworkWorker::poll`].

use std::{collections::HashMap, fs, marker::PhantomData, io, path::Path};
use std::sync::{Arc, atomic::{AtomicBool, AtomicUsize, Ordering}};

use consensus::import_queue::{ImportQueue, Link};
use consensus::import_queue::{BlockImportResult, BlockImportError};
use futures::{prelude::*, sync::mpsc};
use futures03::TryFutureExt as _;
use log::{warn, error, info};
use libp2p::{PeerId, Multiaddr, multihash::Multihash};
use libp2p::core::{transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::swarm::NetworkBehaviour;
use parking_lot::Mutex;
use peerset::PeersetHandle;
use sr_primitives::{traits::{Block as BlockT, NumberFor}, ConsensusEngineId};

use crate::{behaviour::{Behaviour, BehaviourOut}, config::parse_str_addr};
use crate::{NetworkState, NetworkStateNotConnectedPeer, NetworkStatePeer};
use crate::{transport, config::NodeKeyConfig, config::NonReservedPeerMode};
use crate::config::{Params, TransportConfig};
use crate::error::Error;
use crate::protocol::{self, Protocol, Context, CustomMessageOutcome, PeerInfo};
use crate::protocol::consensus_gossip::{ConsensusGossip, MessageRecipient as GossipMessageRecipient};
use crate::protocol::{event::Event, on_demand::{AlwaysBadChecker, RequestData}};
use crate::protocol::specialization::NetworkSpecialization;
use crate::protocol::sync::SyncState;

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
	/// Number of peers we're connected to.
	num_connected: Arc<AtomicUsize>,
	/// The local external addresses.
	external_addresses: Arc<Mutex<Vec<Multiaddr>>>,
	/// Are we actively catching up with the chain?
	is_major_syncing: Arc<AtomicBool>,
	/// Local copy of the `PeerId` of the local node.
	local_peer_id: PeerId,
	/// Bandwidth logging system. Can be queried to know the average bandwidth consumed.
	bandwidth: Arc<transport::BandwidthSinks>,
	/// Peerset manager (PSM); manages the reputation of nodes and indicates the network which
	/// nodes it should be connected to or not.
	peerset: PeersetHandle,
	/// Channel that sends messages to the actual worker.
	to_worker: mpsc::UnboundedSender<ServerToWorkerMsg<B, S>>,
	/// Marker to pin the `H` generic. Serves no purpose except to not break backwards
	/// compatibility.
	_marker: PhantomData<H>,
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
		let (to_worker, from_worker) = mpsc::unbounded();

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

		let peerset_config = peerset::PeersetConfig {
			in_peers: params.network_config.in_peers,
			out_peers: params.network_config.out_peers,
			bootnodes,
			reserved_only: params.network_config.non_reserved_mode == NonReservedPeerMode::Deny,
			reserved_nodes,
		};

		// Private and public keys configuration.
		if let NodeKeyConfig::Secp256k1(_) = params.network_config.node_key {
			warn!(target: "sub-libp2p", "Secp256k1 keys are deprecated in favour of ed25519");
		}
		let local_identity = params.network_config.node_key.clone().into_keypair()?;
		let local_public = local_identity.public();
		let local_peer_id = local_public.clone().into_peer_id();
		info!(target: "sub-libp2p", "Local node identity is: {}", local_peer_id.to_base58());

		let num_connected = Arc::new(AtomicUsize::new(0));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let (protocol, peerset_handle) = Protocol::new(
			protocol::ProtocolConfig { roles: params.roles },
			params.chain,
			params.on_demand.as_ref().map(|od| od.checker().clone())
				.unwrap_or(Arc::new(AlwaysBadChecker)),
			params.specialization,
			params.transaction_pool,
			params.finality_proof_provider,
			params.finality_proof_request_builder,
			params.protocol_id,
			peerset_config,
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
				match params.network_config.transport {
					TransportConfig::MemoryOnly => false,
					TransportConfig::Normal { enable_mdns, .. } => enable_mdns,
				}
			);
			let (transport, bandwidth) = {
				let (config_mem, config_wasm) = match params.network_config.transport {
					TransportConfig::MemoryOnly => (true, None),
					TransportConfig::Normal { wasm_external_transport, .. } =>
						(false, wasm_external_transport)
				};
				transport::build_transport(local_identity, config_mem, config_wasm)
			};
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

		let external_addresses = Arc::new(Mutex::new(Vec::new()));

		let service = Arc::new(NetworkService {
			bandwidth,
			external_addresses: external_addresses.clone(),
			num_connected: num_connected.clone(),
			is_major_syncing: is_major_syncing.clone(),
			peerset: peerset_handle,
			local_peer_id,
			to_worker: to_worker.clone(),
			_marker: PhantomData,
		});

		Ok(NetworkWorker {
			external_addresses,
			num_connected,
			is_major_syncing,
			network_service: swarm,
			service,
			import_queue: params.import_queue,
			from_worker,
			on_demand_in: params.on_demand.and_then(|od| od.extract_receiver()),
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
		self.network_service.user_protocol().num_connected_peers()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.network_service.user_protocol().num_active_peers()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncState {
		self.network_service.user_protocol().sync_state()
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.network_service.user_protocol().best_seen_block()
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.network_service.user_protocol().num_sync_peers()
	}

	/// Adds an address for a node.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.network_service.add_known_address(peer_id, addr);
	}

	/// Return a `NetworkService` that can be shared through the code base and can be used to
	/// manipulate the worker.
	pub fn service(&self) -> &Arc<NetworkService<B, S, H>> {
		&self.service
	}

	/// You must call this when a new block is imported by the client.
	pub fn on_block_imported(&mut self, hash: B::Hash, header: B::Header) {
		self.network_service.user_protocol_mut().on_block_imported(hash, &header);
	}

	/// You must call this when a new block is finalized by the client.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: B::Header) {
		self.network_service.user_protocol_mut().on_block_finalized(hash, &header);
	}

	/// Get network state.
	///
	/// **Note**: Use this only for debugging. This API is unstable. There are warnings literaly
	/// everywhere about this. Please don't use this function to retrieve actual information.
	pub fn network_state(&mut self) -> NetworkState {
		let swarm = &mut self.network_service;
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
			average_download_per_sec: self.service.bandwidth.average_download_per_sec(),
			average_upload_per_sec: self.service.bandwidth.average_upload_per_sec(),
			connected_peers,
			not_connected_peers,
			peerset: swarm.user_protocol_mut().peerset_debug_info(),
		}
	}

	/// Get currently connected peers.
	pub fn peers_debug_info(&mut self) -> Vec<(PeerId, PeerInfo<B>)> {
		self.network_service.user_protocol_mut()
			.peers_info()
			.map(|(id, info)| (id.clone(), info.clone()))
			.collect()
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> NetworkService<B, S, H> {
	/// Returns the network identity of the node.
	pub fn local_peer_id(&self) -> PeerId {
		self.local_peer_id.clone()
	}

	/// You must call this when new transactons are imported by the transaction pool.
	///
	/// The latest transactions will be fetched from the `TransactionPool` that was passed at
	/// initialization as part of the configuration.
	pub fn trigger_repropagate(&self) {
		let _ = self.to_worker.unbounded_send(ServerToWorkerMsg::PropagateExtrinsics);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced. This function forces such an announcement.
	pub fn announce_block(&self, hash: B::Hash) {
		let _ = self.to_worker.unbounded_send(ServerToWorkerMsg::AnnounceBlock(hash));
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
			.to_worker
			.unbounded_send(ServerToWorkerMsg::GossipConsensusMessage(
				topic, engine_id, message, recipient,
			));
	}

	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: i32) {
		self.peerset.report_peer(who, cost_benefit);
	}

	/// Request a justification for the given block from the network.
	///
	/// On success, the justification will be passed to the import queue that was part at
	/// initialization as part of the configuration.
	pub fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::RequestJustification(hash.clone(), number));
	}

	/// Execute a closure with the chain-specific network specialization.
	pub fn with_spec<F>(&self, f: F)
		where F: FnOnce(&mut S, &mut dyn Context<B>) + Send + 'static
	{
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::ExecuteWithSpec(Box::new(f)));
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<B>, &mut dyn Context<B>) + Send + 'static
	{
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::ExecuteWithGossip(Box::new(f)));
	}

	/// Are we in the process of downloading the chain?
	pub fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}

	/// Start getting a value from the DHT.
	///
	/// This will generate either a `ValueFound` or a `ValueNotFound` event and pass it to
	/// `on_event` on the network specialization.
	pub fn get_value(&self, key: &Multihash) {
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::GetValue(key.clone()));
	}

	/// Start putting a value in the DHT.
	///
	/// This will generate either a `ValuePut` or a `ValuePutFailed` event and pass it to
	/// `on_event` on the network specialization.
	pub fn put_value(&self, key: Multihash, value: Vec<u8>) {
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::PutValue(key, value));
	}

	/// Connect to unreserved peers and allow unreserved peers to connect.
	pub fn accept_unreserved_peers(&self) {
		self.peerset.set_reserved_only(false);
	}

	/// Disconnect from unreserved peers and deny new unreserved peers to connect.
	pub fn deny_unreserved_peers(&self) {
		self.peerset.set_reserved_only(true);
	}

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset.remove_reserved_peer(peer);
	}

	/// Adds a `PeerId` and its address as reserved.
	pub fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		let (peer_id, addr) = parse_str_addr(&peer).map_err(|e| format!("{:?}", e))?;
		self.peerset.add_reserved_peer(peer_id.clone());
		let _ = self
			.to_worker
			.unbounded_send(ServerToWorkerMsg::AddKnownAddress(peer_id, addr));
		Ok(())
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected(&self) -> usize {
		self.num_connected.load(Ordering::Relaxed)
	}

	/// Returns the local external addresses.
	pub fn external_addresses(&self) -> Vec<Multiaddr> {
		self.external_addresses.lock().clone()
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT>
	::consensus::SyncOracle for NetworkService<B, S, H> {
	fn is_major_syncing(&mut self) -> bool {
		NetworkService::is_major_syncing(self)
	}

	fn is_offline(&mut self) -> bool {
		self.num_connected.load(Ordering::Relaxed) == 0
	}
}

impl<'a, B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT>
	::consensus::SyncOracle for &'a NetworkService<B, S, H> {
	fn is_major_syncing(&mut self) -> bool {
		NetworkService::is_major_syncing(self)
	}

	fn is_offline(&mut self) -> bool {
		self.num_connected.load(Ordering::Relaxed) == 0
	}
}

/// Trait for providing information about the local network state
pub trait NetworkStateInfo {
	/// Returns the local external addresses.
	fn external_addresses(&self) -> Vec<Multiaddr>;

	/// Returns the local Peer ID.
	fn peer_id(&self) -> PeerId;
}

impl<B, S, H> NetworkStateInfo for NetworkService<B, S, H>
	where
		B: sr_primitives::traits::Block,
		S: NetworkSpecialization<B>,
		H: ExHashT,
{
	/// Returns the local external addresses.
	fn external_addresses(&self) -> Vec<Multiaddr> {
		self.external_addresses.lock().clone()
	}

	/// Returns the local Peer ID.
	fn peer_id(&self) -> PeerId {
		self.local_peer_id.clone()
	}
}

/// Messages sent from the `NetworkService` to the `NetworkWorker`.
///
/// Each entry corresponds to a method of `NetworkService`.
enum ServerToWorkerMsg<B: BlockT, S: NetworkSpecialization<B>> {
	PropagateExtrinsics,
	RequestJustification(B::Hash, NumberFor<B>),
	AnnounceBlock(B::Hash),
	ExecuteWithSpec(Box<dyn FnOnce(&mut S, &mut dyn Context<B>) + Send>),
	ExecuteWithGossip(Box<dyn FnOnce(&mut ConsensusGossip<B>, &mut dyn Context<B>) + Send>),
	GossipConsensusMessage(B::Hash, ConsensusEngineId, Vec<u8>, GossipMessageRecipient),
	GetValue(Multihash),
	PutValue(Multihash, Vec<u8>),
	AddKnownAddress(PeerId, Multiaddr),
}

/// Main network worker. Must be polled in order for the network to advance.
///
/// You are encouraged to poll this in a separate background thread or task.
#[must_use = "The NetworkWorker must be polled in order for the network to work"]
pub struct NetworkWorker<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> {
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	external_addresses: Arc<Mutex<Vec<Multiaddr>>>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	num_connected: Arc<AtomicUsize>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	is_major_syncing: Arc<AtomicBool>,
	/// The network service that can be extracted and shared through the codebase.
	service: Arc<NetworkService<B, S, H>>,
	/// The *actual* network.
	network_service: Swarm<B, S, H>,
	/// The import queue that was passed as initialization.
	import_queue: Box<dyn ImportQueue<B>>,
	/// Messages from the `NetworkService` and that must be processed.
	from_worker: mpsc::UnboundedReceiver<ServerToWorkerMsg<B, S>>,
	/// Receiver for queries from the on-demand that must be processed.
	on_demand_in: Option<mpsc::UnboundedReceiver<RequestData<B>>>,
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT> Future for NetworkWorker<B, S, H> {
	type Item = ();
	type Error = io::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// Poll the import queue for actions to perform.
		let _ = futures03::future::poll_fn(|cx| {
			self.import_queue.poll_actions(cx, &mut NetworkLink {
				protocol: &mut self.network_service,
			});
			std::task::Poll::Pending::<Result<(), ()>>
		}).compat().poll();

		// Check for new incoming on-demand requests.
		if let Some(on_demand_in) = self.on_demand_in.as_mut() {
			while let Ok(Async::Ready(Some(rq))) = on_demand_in.poll() {
				self.network_service.user_protocol_mut().add_on_demand_request(rq);
			}
		}

		loop {
			// Process the next message coming from the `NetworkService`.
			let msg = match self.from_worker.poll() {
				Ok(Async::Ready(Some(msg))) => msg,
				Ok(Async::Ready(None)) | Err(_) => return Ok(Async::Ready(())),
				Ok(Async::NotReady) => break,
			};

			match msg {
				ServerToWorkerMsg::ExecuteWithSpec(task) => {
					let protocol = self.network_service.user_protocol_mut();
					let (mut context, spec) = protocol.specialization_lock();
					task(spec, &mut context);
				},
				ServerToWorkerMsg::ExecuteWithGossip(task) => {
					let protocol = self.network_service.user_protocol_mut();
					let (mut context, gossip) = protocol.consensus_gossip_lock();
					task(gossip, &mut context);
				}
				ServerToWorkerMsg::GossipConsensusMessage(topic, engine_id, message, recipient) =>
					self.network_service.user_protocol_mut().gossip_consensus_message(topic, engine_id, message, recipient),
				ServerToWorkerMsg::AnnounceBlock(hash) =>
					self.network_service.user_protocol_mut().announce_block(hash),
				ServerToWorkerMsg::RequestJustification(hash, number) =>
					self.network_service.user_protocol_mut().request_justification(&hash, number),
				ServerToWorkerMsg::PropagateExtrinsics =>
					self.network_service.user_protocol_mut().propagate_extrinsics(),
				ServerToWorkerMsg::GetValue(key) =>
					self.network_service.get_value(&key),
				ServerToWorkerMsg::PutValue(key, value) =>
					self.network_service.put_value(key, value),
				ServerToWorkerMsg::AddKnownAddress(peer_id, addr) =>
					self.network_service.add_known_address(peer_id, addr),
			}
		}

		loop {
			// Process the next action coming from the network.
			let poll_value = self.network_service.poll();

			let outcome = match poll_value {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(BehaviourOut::SubstrateAction(outcome)))) => outcome,
				Ok(Async::Ready(Some(BehaviourOut::Dht(ev)))) => {
					self.network_service.user_protocol_mut()
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

		// Update the variables shared with the `NetworkService`.
		self.num_connected.store(self.network_service.user_protocol_mut().num_connected_peers(), Ordering::Relaxed);
		{
			let external_addresses = Swarm::<B, S, H>::external_addresses(&self.network_service).cloned().collect();
			*self.external_addresses.lock() = external_addresses;
		}
		self.is_major_syncing.store(match self.network_service.user_protocol_mut().sync_state() {
			SyncState::Idle => false,
			SyncState::Downloading => true,
		}, Ordering::Relaxed);

		Ok(Async::NotReady)
	}
}

/// The libp2p swarm, customized for our needs.
type Swarm<B, S, H> = libp2p::swarm::Swarm<
	Boxed<(PeerId, StreamMuxerBox), io::Error>,
	Behaviour<B, S, H>
>;

// Implementation of `import_queue::Link` trait using the available local variables.
struct NetworkLink<'a, B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	protocol: &'a mut Swarm<B, S, H>,
}

impl<'a, B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Link<B> for NetworkLink<'a, B, S, H> {
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>
	) {
		self.protocol.user_protocol_mut().blocks_processed(imported, count, results)
	}
	fn justification_imported(&mut self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		self.protocol.user_protocol_mut().justification_import_result(hash.clone(), number, success);
		if !success {
			info!("Invalid justification provided by {} for #{}", who, hash);
			self.protocol.user_protocol_mut().disconnect_peer(&who);
			self.protocol.user_protocol_mut().report_peer(who, i32::min_value());
		}
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
}
