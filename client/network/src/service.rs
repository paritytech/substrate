// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Main entry point of the sc-network crate.
//!
//! There are two main structs in this module: [`NetworkWorker`] and [`NetworkService`].
//! The [`NetworkWorker`] *is* the network and implements the `Future` trait. It must be polled in
//! order fo the network to advance.
//! The [`NetworkService`] is merely a shared version of the [`NetworkWorker`]. You can obtain an
//! `Arc<NetworkService>` by calling [`NetworkWorker::service`].
//!
//! The methods of the [`NetworkService`] are implemented by sending a message over a channel,
//! which is then processed by [`NetworkWorker::poll`].

use crate::{
	ExHashT, NetworkStateInfo,
	behaviour::{Behaviour, BehaviourOut},
	config::{parse_addr, parse_str_addr, NonReservedPeerMode, Params, Role, TransportConfig},
	discovery::DiscoveryConfig,
	error::Error,
	network_state::{
		NetworkState, NotConnectedPeer as NetworkStateNotConnectedPeer, Peer as NetworkStatePeer,
	},
	on_demand_layer::AlwaysBadChecker,
	light_client_handler, block_requests, finality_requests,
	protocol::{self, event::Event, LegacyConnectionKillError, sync::SyncState, PeerInfo, Protocol},
	transport, ReputationChange,
};
use futures::prelude::*;
use libp2p::{PeerId, Multiaddr};
use libp2p::core::{ConnectedPoint, Executor, connection::{ConnectionError, PendingConnectionError}, either::EitherError};
use libp2p::kad::record;
use libp2p::ping::handler::PingFailure;
use libp2p::swarm::{NetworkBehaviour, SwarmBuilder, SwarmEvent, protocols_handler::NodeHandlerWrapperError};
use log::{error, info, trace, warn};
use parking_lot::Mutex;
use prometheus_endpoint::{
	register, Counter, CounterVec, Gauge, GaugeVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry, U64,
};
use sc_peerset::PeersetHandle;
use sp_consensus::import_queue::{BlockImportError, BlockImportResult, ImportQueue, Link};
use sp_runtime::{
	traits::{Block as BlockT, NumberFor},
	ConsensusEngineId,
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use std::{
	borrow::Cow,
	collections::HashSet,
	fs, io,
	marker::PhantomData,
	pin::Pin,
	str,
	sync::{
		atomic::{AtomicBool, AtomicUsize, Ordering},
		Arc,
	},
	task::Poll,
};

mod out_events;
#[cfg(test)]
mod tests;

/// Substrate network service. Handles network IO and manages connectivity.
pub struct NetworkService<B: BlockT + 'static, H: ExHashT> {
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
	to_worker: TracingUnboundedSender<ServiceToWorkerMsg<B, H>>,
	/// Marker to pin the `H` generic. Serves no purpose except to not break backwards
	/// compatibility.
	_marker: PhantomData<H>,
}

impl<B: BlockT + 'static, H: ExHashT> NetworkWorker<B, H> {
	/// Creates the network service.
	///
	/// Returns a `NetworkWorker` that implements `Future` and must be regularly polled in order
	/// for the network processing to advance. From it, you can extract a `NetworkService` using
	/// `worker.service()`. The `NetworkService` can be shared through the codebase.
	pub fn new(params: Params<B, H>) -> Result<NetworkWorker<B, H>, Error> {
		let (to_worker, from_worker) = tracing_unbounded("mpsc_network_worker");

		if let Some(path) = params.network_config.net_config_path {
			fs::create_dir_all(&path)?;
		}

		// List of multiaddresses that we know in the network.
		let mut known_addresses = Vec::new();
		let mut bootnodes = Vec::new();
		let mut boot_node_ids = HashSet::new();

		// Process the bootnodes.
		for bootnode in params.network_config.boot_nodes.iter() {
			bootnodes.push(bootnode.peer_id.clone());
			boot_node_ids.insert(bootnode.peer_id.clone());
			known_addresses.push((bootnode.peer_id.clone(), bootnode.multiaddr.clone()));
		}

		let boot_node_ids = Arc::new(boot_node_ids);

		// Check for duplicate bootnodes.
		known_addresses.iter()
			.try_for_each(|(peer_id, addr)|
				if let Some(other) = known_addresses
					.iter()
					.find(|o| o.1 == *addr && o.0 != *peer_id)
				{
					Err(Error::DuplicateBootnode {
						address: addr.clone(),
						first_id: peer_id.clone(),
						second_id: other.0.clone(),
					})
				} else {
					Ok(())
				}
			)?;

		// Initialize the peers we should always be connected to.
		let priority_groups = {
			let mut reserved_nodes = HashSet::new();
			for reserved in params.network_config.reserved_nodes.iter() {
				reserved_nodes.insert(reserved.peer_id.clone());
				known_addresses.push((reserved.peer_id.clone(), reserved.multiaddr.clone()));
			}

			let mut sentries_and_validators = HashSet::new();
			match &params.role {
				Role::Sentry { validators } => {
					for validator in validators {
						sentries_and_validators.insert(validator.peer_id.clone());
						known_addresses.push((validator.peer_id.clone(), validator.multiaddr.clone()));
					}
				}
				Role::Authority { sentry_nodes } => {
					for sentry_node in sentry_nodes {
						sentries_and_validators.insert(sentry_node.peer_id.clone());
						known_addresses.push((sentry_node.peer_id.clone(), sentry_node.multiaddr.clone()));
					}
				}
				_ => {}
			}

			vec![
				("reserved".to_owned(), reserved_nodes),
				("sentries_and_validators".to_owned(), sentries_and_validators),
			]
		};

		let peerset_config = sc_peerset::PeersetConfig {
			in_peers: params.network_config.in_peers,
			out_peers: params.network_config.out_peers,
			bootnodes,
			reserved_only: params.network_config.non_reserved_mode == NonReservedPeerMode::Deny,
			priority_groups,
		};

		// Private and public keys configuration.
		let local_identity = params.network_config.node_key.clone().into_keypair()?;
		let local_public = local_identity.public();
		let local_peer_id = local_public.clone().into_peer_id();
		info!(target: "sub-libp2p", "🏷  Local node identity is: {}", local_peer_id.to_base58());

		// Initialize the metrics.
		let metrics = match &params.metrics_registry {
			Some(registry) => Some(Metrics::register(&registry)?),
			None => None
		};

		let checker = params.on_demand.as_ref()
			.map(|od| od.checker().clone())
			.unwrap_or(Arc::new(AlwaysBadChecker));

		let num_connected = Arc::new(AtomicUsize::new(0));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let (protocol, peerset_handle) = Protocol::new(
			protocol::ProtocolConfig {
				roles: From::from(&params.role),
				max_parallel_downloads: params.network_config.max_parallel_downloads,
			},
			params.chain.clone(),
			params.transaction_pool,
			params.finality_proof_provider.clone(),
			params.finality_proof_request_builder,
			params.protocol_id.clone(),
			peerset_config,
			params.block_announce_validator,
			params.metrics_registry.as_ref(),
			boot_node_ids.clone(),
			params.network_config.use_new_block_requests_protocol,
			metrics.as_ref().map(|m| m.notifications_queues_size.clone()),
		)?;

		// Build the swarm.
		let (mut swarm, bandwidth): (Swarm<B, H>, _) = {
			let user_agent = format!(
				"{} ({})",
				params.network_config.client_version,
				params.network_config.node_name
			);
			let block_requests = {
				let config = block_requests::Config::new(&params.protocol_id);
				block_requests::BlockRequests::new(config, params.chain.clone())
			};
			let finality_proof_requests = {
				let config = finality_requests::Config::new(&params.protocol_id);
				finality_requests::FinalityProofRequests::new(config, params.finality_proof_provider.clone())
			};
			let light_client_handler = {
				let config = light_client_handler::Config::new(&params.protocol_id);
				light_client_handler::LightClientHandler::new(
					config,
					params.chain,
					checker,
					peerset_handle.clone(),
				)
			};

			let discovery_config = {
				let mut config = DiscoveryConfig::new(local_public.clone());
				config.with_user_defined(known_addresses);
				config.discovery_limit(u64::from(params.network_config.out_peers) + 15);
				config.add_protocol(params.protocol_id.clone());
				config.allow_non_globals_in_dht(params.network_config.allow_non_globals_in_dht);

				match params.network_config.transport {
					TransportConfig::MemoryOnly => {
						config.with_mdns(false);
						config.allow_private_ipv4(false);
					}
					TransportConfig::Normal { enable_mdns, allow_private_ipv4, .. } => {
						config.with_mdns(enable_mdns);
						config.allow_private_ipv4(allow_private_ipv4);
					}
				}

				config
			};

			let mut behaviour = Behaviour::new(
				protocol,
				params.role,
				user_agent,
				local_public,
				block_requests,
				finality_proof_requests,
				light_client_handler,
				discovery_config
			);

			for (engine_id, protocol_name) in &params.network_config.notifications_protocols {
				behaviour.register_notifications_protocol(*engine_id, protocol_name.clone());
			}
			let (transport, bandwidth) = {
				let (config_mem, config_wasm, flowctrl) = match params.network_config.transport {
					TransportConfig::MemoryOnly => (true, None, false),
					TransportConfig::Normal { wasm_external_transport, use_yamux_flow_control, .. } =>
						(false, wasm_external_transport, use_yamux_flow_control)
				};
				transport::build_transport(local_identity, config_mem, config_wasm, flowctrl)
			};
			let mut builder = SwarmBuilder::new(transport, behaviour, local_peer_id.clone())
				.peer_connection_limit(crate::MAX_CONNECTIONS_PER_PEER);
			if let Some(spawner) = params.executor {
				struct SpawnImpl<F>(F);
				impl<F: Fn(Pin<Box<dyn Future<Output = ()> + Send>>)> Executor for SpawnImpl<F> {
					fn exec(&self, f: Pin<Box<dyn Future<Output = ()> + Send>>) {
						(self.0)(f)
					}
				}
				builder = builder.executor(Box::new(SpawnImpl(spawner)));
			}
			(builder.build(), bandwidth)
		};

		// Listen on multiaddresses.
		for addr in &params.network_config.listen_addresses {
			if let Err(err) = Swarm::<B, H>::listen_on(&mut swarm, addr.clone()) {
				warn!(target: "sub-libp2p", "Can't listen on {} because: {:?}", addr, err)
			}
		}

		// Add external addresses.
		for addr in &params.network_config.public_addresses {
			Swarm::<B, H>::add_external_address(&mut swarm, addr.clone());
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
			light_client_rqs: params.on_demand.and_then(|od| od.extract_receiver()),
			event_streams: out_events::OutChannels::new(params.metrics_registry.as_ref())?,
			metrics,
			boot_node_ids,
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

	/// Number of blocks in the import queue.
	pub fn num_queued_blocks(&self) -> u32 {
		self.network_service.user_protocol().num_queued_blocks()
	}

	/// Returns the number of processed blocks.
	pub fn num_processed_blocks(&self) -> usize {
		self.network_service.user_protocol().num_processed_blocks()
	}

	/// Number of active sync requests.
	pub fn num_sync_requests(&self) -> usize {
		self.network_service.user_protocol().num_sync_requests()
	}

	/// Adds an address for a node.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.network_service.add_known_address(peer_id, addr);
	}

	/// Return a `NetworkService` that can be shared through the code base and can be used to
	/// manipulate the worker.
	pub fn service(&self) -> &Arc<NetworkService<B, H>> {
		&self.service
	}

	/// You must call this when a new block is imported by the client.
	pub fn on_block_imported(&mut self, header: B::Header, is_best: bool) {
		self.network_service.user_protocol_mut().on_block_imported(&header, is_best);
	}

	/// You must call this when a new block is finalized by the client.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: B::Header) {
		self.network_service.user_protocol_mut().on_block_finalized(hash, &header);
	}

	/// Returns the local `PeerId`.
	pub fn local_peer_id(&self) -> &PeerId {
		Swarm::<B, H>::local_peer_id(&self.network_service)
	}

	/// Returns the list of addresses we are listening on.
	///
	/// Does **NOT** include a trailing `/p2p/` with our `PeerId`.
	pub fn listen_addresses(&self) -> impl Iterator<Item = &Multiaddr> {
		Swarm::<B, H>::listeners(&self.network_service)
	}

	/// Get network state.
	///
	/// **Note**: Use this only for debugging. This API is unstable. There are warnings literally
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
			peer_id: Swarm::<B, H>::local_peer_id(&swarm).to_base58(),
			listened_addresses: Swarm::<B, H>::listeners(&swarm).cloned().collect(),
			external_addresses: Swarm::<B, H>::external_addresses(&swarm).cloned().collect(),
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

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.service.remove_reserved_peer(peer);
	}

	/// Adds a `PeerId` and its address as reserved. The string should encode the address
	/// and peer ID of the remote node.
	pub fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.service.add_reserved_peer(peer)
	}
}

impl<B: BlockT + 'static, H: ExHashT> NetworkService<B, H> {
	/// Returns the local `PeerId`.
	pub fn local_peer_id(&self) -> &PeerId {
		&self.local_peer_id
	}

	/// Writes a message on an open notifications channel. Has no effect if the notifications
	/// channel with this protocol name is closed.
	///
	/// > **Note**: The reason why this is a no-op in the situation where we have no channel is
	/// >			that we don't guarantee message delivery anyway. Networking issues can cause
	/// >			connections to drop at any time, and higher-level logic shouldn't differentiate
	/// >			between the remote voluntarily closing a substream or a network error
	/// >			preventing the message from being delivered.
	///
	/// The protocol must have been registered with `register_notifications_protocol`.
	///
	pub fn write_notification(&self, target: PeerId, engine_id: ConsensusEngineId, message: Vec<u8>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::WriteNotification {
			target,
			engine_id,
			message,
		});
	}

	/// Returns a stream containing the events that happen on the network.
	///
	/// If this method is called multiple times, the events are duplicated.
	///
	/// The stream never ends (unless the `NetworkWorker` gets shut down).
	///
	/// The name passed is used to identify the channel in the Prometheus metrics. Note that the
	/// parameter is a `&'static str`, and not a `String`, in order to avoid accidentally having
	/// an unbounded set of Prometheus metrics, which would be quite bad in terms of memory
	pub fn event_stream(&self, name: &'static str) -> impl Stream<Item = Event> {
		// Note: when transitioning to stable futures, remove the `Error` entirely
		let (tx, rx) = out_events::channel(name);
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::EventStream(tx));
		rx
	}

	/// Registers a new notifications protocol.
	///
	/// After that, you can call `write_notifications`.
	///
	/// Please call `event_stream` before registering a protocol, otherwise you may miss events
	/// about the protocol that you have registered.
	///
	/// You are very strongly encouraged to call this method very early on. Any connection open
	/// will retain the protocols that were registered then, and not any new one.
	pub fn register_notifications_protocol(
		&self,
		engine_id: ConsensusEngineId,
		protocol_name: impl Into<Cow<'static, [u8]>>,
	) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::RegisterNotifProtocol {
			engine_id,
			protocol_name: protocol_name.into(),
		});
	}

	/// You may call this when new transactons are imported by the transaction pool.
	///
	/// All transactions will be fetched from the `TransactionPool` that was passed at
	/// initialization as part of the configuration and propagated to peers.
	pub fn trigger_repropagate(&self) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::PropagateExtrinsics);
	}

	/// You must call when new transaction is imported by the transaction pool.
	///
	/// This transaction will be fetched from the `TransactionPool` that was passed at
	/// initialization as part of the configuration and propagated to peers.
	pub fn propagate_extrinsic(&self, hash: H) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::PropagateExtrinsic(hash));
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced. This function forces such an announcement.
	pub fn announce_block(&self, hash: B::Hash, data: Vec<u8>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::AnnounceBlock(hash, data));
	}

	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		self.peerset.report_peer(who, cost_benefit);
	}

	/// Disconnect from a node as soon as possible.
	///
	/// This triggers the same effects as if the connection had closed itself spontaneously.
	pub fn disconnect_peer(&self, who: PeerId) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::DisconnectPeer(who));
	}

	/// Request a justification for the given block from the network.
	///
	/// On success, the justification will be passed to the import queue that was part at
	/// initialization as part of the configuration.
	pub fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::RequestJustification(hash.clone(), number));
	}

	/// Are we in the process of downloading the chain?
	pub fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}

	/// Start getting a value from the DHT.
	///
	/// This will generate either a `ValueFound` or a `ValueNotFound` event and pass it as an
	/// item on the [`NetworkWorker`] stream.
	pub fn get_value(&self, key: &record::Key) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::GetValue(key.clone()));
	}

	/// Start putting a value in the DHT.
	///
	/// This will generate either a `ValuePut` or a `ValuePutFailed` event and pass it as an
	/// item on the [`NetworkWorker`] stream.
	pub fn put_value(&self, key: record::Key, value: Vec<u8>) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::PutValue(key, value));
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

	/// Adds a `PeerId` and its address as reserved. The string should encode the address
	/// and peer ID of the remote node.
	pub fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		let (peer_id, addr) = parse_str_addr(&peer).map_err(|e| format!("{:?}", e))?;
		self.peerset.add_reserved_peer(peer_id.clone());
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
		Ok(())
	}

	/// Configure an explicit fork sync request.
	/// Note that this function should not be used for recent blocks.
	/// Sync should be able to download all the recent forks normally.
	/// `set_sync_fork_request` should only be used if external code detects that there's
	/// a stale fork missing.
	/// Passing empty `peers` set effectively removes the sync request.
	pub fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::SyncFork(peers, hash, number));
	}

	/// Modify a peerset priority group.
	pub fn set_priority_group(&self, group_id: String, peers: HashSet<Multiaddr>) -> Result<(), String> {
		let peers = peers.into_iter().map(|p| {
			parse_addr(p).map_err(|e| format!("{:?}", e))
		}).collect::<Result<Vec<(PeerId, Multiaddr)>, String>>()?;

		let peer_ids = peers.iter().map(|(peer_id, _addr)| peer_id.clone()).collect();
		self.peerset.set_priority_group(group_id, peer_ids);

		for (peer_id, addr) in peers.into_iter() {
			let _ = self
				.to_worker
				.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
		}

		Ok(())
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected(&self) -> usize {
		self.num_connected.load(Ordering::Relaxed)
	}
}

impl<B: BlockT + 'static, H: ExHashT> sp_consensus::SyncOracle
	for NetworkService<B, H>
{
	fn is_major_syncing(&mut self) -> bool {
		NetworkService::is_major_syncing(self)
	}

	fn is_offline(&mut self) -> bool {
		self.num_connected.load(Ordering::Relaxed) == 0
	}
}

impl<'a, B: BlockT + 'static, H: ExHashT> sp_consensus::SyncOracle
	for &'a NetworkService<B, H>
{
	fn is_major_syncing(&mut self) -> bool {
		NetworkService::is_major_syncing(self)
	}

	fn is_offline(&mut self) -> bool {
		self.num_connected.load(Ordering::Relaxed) == 0
	}
}

impl<B, H> NetworkStateInfo for NetworkService<B, H>
	where
		B: sp_runtime::traits::Block,
		H: ExHashT,
{
	/// Returns the local external addresses.
	fn external_addresses(&self) -> Vec<Multiaddr> {
		self.external_addresses.lock().clone()
	}

	/// Returns the local Peer ID.
	fn local_peer_id(&self) -> PeerId {
		self.local_peer_id.clone()
	}
}

/// Messages sent from the `NetworkService` to the `NetworkWorker`.
///
/// Each entry corresponds to a method of `NetworkService`.
enum ServiceToWorkerMsg<B: BlockT, H: ExHashT> {
	PropagateExtrinsic(H),
	PropagateExtrinsics,
	RequestJustification(B::Hash, NumberFor<B>),
	AnnounceBlock(B::Hash, Vec<u8>),
	GetValue(record::Key),
	PutValue(record::Key, Vec<u8>),
	AddKnownAddress(PeerId, Multiaddr),
	SyncFork(Vec<PeerId>, B::Hash, NumberFor<B>),
	EventStream(out_events::Sender),
	WriteNotification {
		message: Vec<u8>,
		engine_id: ConsensusEngineId,
		target: PeerId,
	},
	RegisterNotifProtocol {
		engine_id: ConsensusEngineId,
		protocol_name: Cow<'static, [u8]>,
	},
	DisconnectPeer(PeerId),
}

/// Main network worker. Must be polled in order for the network to advance.
///
/// You are encouraged to poll this in a separate background thread or task.
#[must_use = "The NetworkWorker must be polled in order for the network to work"]
pub struct NetworkWorker<B: BlockT + 'static, H: ExHashT> {
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	external_addresses: Arc<Mutex<Vec<Multiaddr>>>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	num_connected: Arc<AtomicUsize>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	is_major_syncing: Arc<AtomicBool>,
	/// The network service that can be extracted and shared through the codebase.
	service: Arc<NetworkService<B, H>>,
	/// The *actual* network.
	network_service: Swarm<B, H>,
	/// The import queue that was passed as initialization.
	import_queue: Box<dyn ImportQueue<B>>,
	/// Messages from the `NetworkService` and that must be processed.
	from_worker: TracingUnboundedReceiver<ServiceToWorkerMsg<B, H>>,
	/// Receiver for queries from the light client that must be processed.
	light_client_rqs: Option<TracingUnboundedReceiver<light_client_handler::Request<B>>>,
	/// Senders for events that happen on the network.
	event_streams: out_events::OutChannels,
	/// Prometheus network metrics.
	metrics: Option<Metrics>,
	/// The `PeerId`'s of all boot nodes.
	boot_node_ids: Arc<HashSet<PeerId>>,
}

struct Metrics {
	// This list is ordered alphabetically
	connections_closed_total: CounterVec<U64>,
	connections_opened_total: CounterVec<U64>,
	import_queue_blocks_submitted: Counter<U64>,
	import_queue_finality_proofs_submitted: Counter<U64>,
	import_queue_justifications_submitted: Counter<U64>,
	incoming_connections_errors_total: CounterVec<U64>,
	incoming_connections_total: Counter<U64>,
	is_major_syncing: Gauge<U64>,
	issued_light_requests: Counter<U64>,
	kademlia_random_queries_total: CounterVec<U64>,
	kademlia_records_count: GaugeVec<U64>,
	kademlia_records_sizes_total: GaugeVec<U64>,
	kbuckets_num_nodes: GaugeVec<U64>,
	listeners_local_addresses: Gauge<U64>,
	listeners_errors_total: Counter<U64>,
	network_per_sec_bytes: GaugeVec<U64>,
	notifications_queues_size: HistogramVec,
	notifications_sizes: HistogramVec,
	notifications_streams_closed_total: CounterVec<U64>,
	notifications_streams_opened_total: CounterVec<U64>,
	peers_count: Gauge<U64>,
	peerset_num_discovered: Gauge<U64>,
	peerset_num_requested: Gauge<U64>,
	pending_connections: Gauge<U64>,
	pending_connections_errors_total: CounterVec<U64>,
	requests_in_total: HistogramVec,
	requests_out_finished: HistogramVec,
	requests_out_started_total: CounterVec<U64>,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			// This list is ordered alphabetically
			connections_closed_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_connections_closed_total",
					"Total number of connections closed, by reason and direction"
				),
				&["direction", "reason"]
			)?, registry)?,
			connections_opened_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_connections_opened_total",
					"Total number of connections opened"
				),
				&["direction"]
			)?, registry)?,
			import_queue_blocks_submitted: register(Counter::new(
				"import_queue_blocks_submitted",
				"Number of blocks submitted to the import queue.",
			)?, registry)?,
			import_queue_finality_proofs_submitted: register(Counter::new(
				"import_queue_finality_proofs_submitted",
				"Number of finality proofs submitted to the import queue.",
			)?, registry)?,
			import_queue_justifications_submitted: register(Counter::new(
				"import_queue_justifications_submitted",
				"Number of justifications submitted to the import queue.",
			)?, registry)?,
			incoming_connections_errors_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_incoming_connections_handshake_errors_total",
					"Total number of incoming connections that have failed during the \
					initial handshake"
				),
				&["reason"]
			)?, registry)?,
			incoming_connections_total: register(Counter::new(
				"sub_libp2p_incoming_connections_total",
				"Total number of incoming connections on the listening sockets"
			)?, registry)?,
			is_major_syncing: register(Gauge::new(
				"sub_libp2p_is_major_syncing", "Whether the node is performing a major sync or not.",
			)?, registry)?,
			issued_light_requests: register(Counter::new(
				"issued_light_requests",
				"Number of light client requests that our node has issued.",
			)?, registry)?,
			kademlia_random_queries_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_kademlia_random_queries_total",
					"Number of random Kademlia queries started"
				),
				&["protocol"]
			)?, registry)?,
			kademlia_records_count: register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kademlia_records_count",
					"Number of records in the Kademlia records store"
				),
				&["protocol"]
			)?, registry)?,
			kademlia_records_sizes_total: register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kademlia_records_sizes_total",
					"Total size of all the records in the Kademlia records store"
				),
				&["protocol"]
			)?, registry)?,
			kbuckets_num_nodes: register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kbuckets_num_nodes",
					"Number of nodes in the Kademlia k-buckets"
				),
				&["protocol"]
			)?, registry)?,
			listeners_local_addresses: register(Gauge::new(
				"sub_libp2p_listeners_local_addresses", "Number of local addresses we're listening on"
			)?, registry)?,
			listeners_errors_total: register(Counter::new(
				"sub_libp2p_listeners_errors_total",
				"Total number of non-fatal errors reported by a listener"
			)?, registry)?,
			network_per_sec_bytes: register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_network_per_sec_bytes",
					"Average bandwidth usage per second"
				),
				&["direction"]
			)?, registry)?,
			notifications_queues_size: register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_notifications_queues_size",
						"Total size of all the notification queues"
					),
					buckets: vec![0.0, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0, 256.0, 511.0, 512.0],
				},
				&["protocol"]
			)?, registry)?,
			notifications_sizes: register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_notifications_sizes",
						"Sizes of the notifications send to and received from all nodes"
					),
					buckets: prometheus_endpoint::exponential_buckets(64.0, 4.0, 8)
						.expect("parameters are always valid values; qed"),
				},
				&["direction", "protocol"]
			)?, registry)?,
			notifications_streams_closed_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_notifications_streams_closed_total",
					"Total number of notification substreams that have been closed"
				),
				&["protocol"]
			)?, registry)?,
			notifications_streams_opened_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_notifications_streams_opened_total",
					"Total number of notification substreams that have been opened"
				),
				&["protocol"]
			)?, registry)?,
			peers_count: register(Gauge::new(
				"sub_libp2p_peers_count", "Number of network gossip peers",
			)?, registry)?,
			peerset_num_discovered: register(Gauge::new(
				"sub_libp2p_peerset_num_discovered", "Number of nodes stored in the peerset manager",
			)?, registry)?,
			peerset_num_requested: register(Gauge::new(
				"sub_libp2p_peerset_num_requested", "Number of nodes that the peerset manager wants us to be connected to",
			)?, registry)?,
			pending_connections: register(Gauge::new(
				"sub_libp2p_pending_connections",
				"Number of connections in the process of being established",
			)?, registry)?,
			pending_connections_errors_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_pending_connections_errors_total",
					"Total number of pending connection errors"
				),
				&["reason"]
			)?, registry)?,
			requests_in_total: register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_requests_in_total",
						"Total number of requests received and answered"
					),
					buckets: prometheus_endpoint::exponential_buckets(0.001, 2.0, 16)
						.expect("parameters are always valid values; qed"),
				},
				&["protocol"]
			)?, registry)?,
			requests_out_finished: register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_requests_out_finished",
						"Time between a request's start and finish (successful or not)"
					),
					buckets: prometheus_endpoint::exponential_buckets(0.001, 2.0, 16)
						.expect("parameters are always valid values; qed"),
				},
				&["protocol"]
			)?, registry)?,
			requests_out_started_total: register(CounterVec::new(
				Opts::new(
					"sub_libp2p_requests_out_started_total",
					"Total number of requests emitted"
				),
				&["protocol"]
			)?, registry)?,
		})
	}

	fn update_with_network_event(&self, event: &Event) {
		match event {
			Event::NotificationStreamOpened { engine_id, .. } => {
				self.notifications_streams_opened_total
					.with_label_values(&[&maybe_utf8_bytes_to_string(engine_id)]).inc();
			},
			Event::NotificationStreamClosed { engine_id, .. } => {
				self.notifications_streams_closed_total
					.with_label_values(&[&maybe_utf8_bytes_to_string(engine_id)]).inc();
			},
			Event::NotificationsReceived { messages, .. } => {
				for (engine_id, message) in messages {
					self.notifications_sizes
						.with_label_values(&["in", &maybe_utf8_bytes_to_string(engine_id)])
						.observe(message.len() as f64);
				}
			},
			_ => {}
		}
	}
}

impl<B: BlockT + 'static, H: ExHashT> Future for NetworkWorker<B, H> {
	type Output = Result<(), io::Error>;

	fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<Self::Output> {
		let this = &mut *self;

		// Poll the import queue for actions to perform.
		this.import_queue.poll_actions(cx, &mut NetworkLink {
			protocol: &mut this.network_service,
		});

		// Check for new incoming light client requests.
		if let Some(light_client_rqs) = this.light_client_rqs.as_mut() {
			while let Poll::Ready(Some(rq)) = light_client_rqs.poll_next_unpin(cx) {
				// This can error if there are too many queued requests already.
				if this.network_service.light_client_request(rq).is_err() {
					log::warn!("Couldn't start light client request: too many pending requests");
				}
				if let Some(metrics) = this.metrics.as_ref() {
					metrics.issued_light_requests.inc();
				}
			}
		}

		loop {
			// Process the next message coming from the `NetworkService`.
			let msg = match this.from_worker.poll_next_unpin(cx) {
				Poll::Ready(Some(msg)) => msg,
				Poll::Ready(None) => return Poll::Ready(Ok(())),
				Poll::Pending => break,
			};

			match msg {
				ServiceToWorkerMsg::AnnounceBlock(hash, data) =>
					this.network_service.user_protocol_mut().announce_block(hash, data),
				ServiceToWorkerMsg::RequestJustification(hash, number) =>
					this.network_service.user_protocol_mut().request_justification(&hash, number),
				ServiceToWorkerMsg::PropagateExtrinsic(hash) =>
					this.network_service.user_protocol_mut().propagate_extrinsic(&hash),
				ServiceToWorkerMsg::PropagateExtrinsics =>
					this.network_service.user_protocol_mut().propagate_extrinsics(),
				ServiceToWorkerMsg::GetValue(key) =>
					this.network_service.get_value(&key),
				ServiceToWorkerMsg::PutValue(key, value) =>
					this.network_service.put_value(key, value),
				ServiceToWorkerMsg::AddKnownAddress(peer_id, addr) =>
					this.network_service.add_known_address(peer_id, addr),
				ServiceToWorkerMsg::SyncFork(peer_ids, hash, number) =>
					this.network_service.user_protocol_mut().set_sync_fork_request(peer_ids, &hash, number),
				ServiceToWorkerMsg::EventStream(sender) =>
					this.event_streams.push(sender),
				ServiceToWorkerMsg::WriteNotification { message, engine_id, target } => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.notifications_sizes
							.with_label_values(&["out", &maybe_utf8_bytes_to_string(&engine_id)])
							.observe(message.len() as f64);
					}
					this.network_service.user_protocol_mut().write_notification(target, engine_id, message)
				},
				ServiceToWorkerMsg::RegisterNotifProtocol { engine_id, protocol_name } => {
					this.network_service
						.register_notifications_protocol(engine_id, protocol_name);
				},
				ServiceToWorkerMsg::DisconnectPeer(who) =>
					this.network_service.user_protocol_mut().disconnect_peer(&who),
			}
		}

		loop {
			// Process the next action coming from the network.
			let next_event = this.network_service.next_event();
			futures::pin_mut!(next_event);
			let poll_value = next_event.poll_unpin(cx);

			match poll_value {
				Poll::Pending => break,
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::BlockImport(origin, blocks))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.import_queue_blocks_submitted.inc();
					}
					this.import_queue.import_blocks(origin, blocks);
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::JustificationImport(origin, hash, nb, justification))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.import_queue_justifications_submitted.inc();
					}
					this.import_queue.import_justification(origin, hash, nb, justification);
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::FinalityProofImport(origin, hash, nb, proof))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.import_queue_finality_proofs_submitted.inc();
					}
					this.import_queue.import_finality_proof(origin, hash, nb, proof);
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::AnsweredRequest { protocol, build_time, .. })) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.requests_in_total
							.with_label_values(&[&maybe_utf8_bytes_to_string(&protocol)])
							.observe(build_time.as_secs_f64());
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::RequestStarted { protocol, .. })) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.requests_out_started_total
							.with_label_values(&[&maybe_utf8_bytes_to_string(&protocol)])
							.inc();
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::RequestFinished { protocol, request_duration, .. })) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.requests_out_finished
							.with_label_values(&[&maybe_utf8_bytes_to_string(&protocol)])
							.observe(request_duration.as_secs_f64());
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::RandomKademliaStarted(protocol))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.kademlia_random_queries_total
							.with_label_values(&[&maybe_utf8_bytes_to_string(protocol.as_bytes())])
							.inc();
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::Event(ev))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.update_with_network_event(&ev);
					}
					this.event_streams.send(ev);
				},
				Poll::Ready(SwarmEvent::ConnectionEstablished { peer_id, endpoint, .. }) => {
					trace!(target: "sub-libp2p", "Libp2p => Connected({:?})", peer_id);
					if let Some(metrics) = this.metrics.as_ref() {
						match endpoint {
							ConnectedPoint::Dialer { .. } =>
								metrics.connections_opened_total.with_label_values(&["out"]).inc(),
							ConnectedPoint::Listener { .. } =>
								metrics.connections_opened_total.with_label_values(&["in"]).inc(),
						}
					}
				},
				Poll::Ready(SwarmEvent::ConnectionClosed { peer_id, cause, endpoint, .. }) => {
					trace!(target: "sub-libp2p", "Libp2p => Disconnected({:?}, {:?})", peer_id, cause);
					if let Some(metrics) = this.metrics.as_ref() {
						let dir = match endpoint {
							ConnectedPoint::Dialer { .. } => "out",
							ConnectedPoint::Listener { .. } => "in",
						};

						match cause {
							ConnectionError::IO(_) =>
								metrics.connections_closed_total.with_label_values(&[dir, "transport-error"]).inc(),
							ConnectionError::Handler(NodeHandlerWrapperError::Handler(EitherError::A(EitherError::A(
								EitherError::A(EitherError::A(EitherError::B(
								EitherError::A(PingFailure::Timeout)))))))) =>
								metrics.connections_closed_total.with_label_values(&[dir, "ping-timeout"]).inc(),
							ConnectionError::Handler(NodeHandlerWrapperError::Handler(EitherError::A(EitherError::A(
								EitherError::A(EitherError::A(EitherError::A(
								EitherError::B(LegacyConnectionKillError)))))))) =>
								metrics.connections_closed_total.with_label_values(&[dir, "force-closed"]).inc(),
							ConnectionError::Handler(NodeHandlerWrapperError::Handler(_)) =>
								metrics.connections_closed_total.with_label_values(&[dir, "protocol-error"]).inc(),
							ConnectionError::Handler(NodeHandlerWrapperError::KeepAliveTimeout) =>
								metrics.connections_closed_total.with_label_values(&[dir, "keep-alive-timeout"]).inc(),
						}
					}
				},
				Poll::Ready(SwarmEvent::NewListenAddr(addr)) => {
					trace!(target: "sub-libp2p", "Libp2p => NewListenAddr({})", addr);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.inc();
					}
				},
				Poll::Ready(SwarmEvent::ExpiredListenAddr(addr)) => {
					trace!(target: "sub-libp2p", "Libp2p => ExpiredListenAddr({})", addr);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.dec();
					}
				},
				Poll::Ready(SwarmEvent::UnreachableAddr { peer_id, address, error, .. }) => {
					trace!(
						target: "sub-libp2p", "Libp2p => Failed to reach {:?} through {:?}: {}",
						peer_id,
						address,
						error,
					);

					if this.boot_node_ids.contains(&peer_id) {
						if let PendingConnectionError::InvalidPeerId = error {
							error!(
								"💔 The bootnode you want to connect to at `{}` provided a different peer ID than the one you expect: `{}`.",
								address,
								peer_id,
							);
						}
					}

					if let Some(metrics) = this.metrics.as_ref() {
						match error {
							PendingConnectionError::ConnectionLimit(_) =>
								metrics.pending_connections_errors_total.with_label_values(&["limit-reached"]).inc(),
							PendingConnectionError::InvalidPeerId =>
								metrics.pending_connections_errors_total.with_label_values(&["invalid-peer-id"]).inc(),
							PendingConnectionError::Transport(_) | PendingConnectionError::IO(_) =>
								metrics.pending_connections_errors_total.with_label_values(&["transport-error"]).inc(),
						}
					}
				}
				Poll::Ready(SwarmEvent::Dialing(peer_id)) =>
					trace!(target: "sub-libp2p", "Libp2p => Dialing({:?})", peer_id),
				Poll::Ready(SwarmEvent::IncomingConnection { local_addr, send_back_addr }) => {
					trace!(target: "sub-libp2p", "Libp2p => IncomingConnection({},{}))",
						local_addr, send_back_addr);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.incoming_connections_total.inc();
					}
				},
				Poll::Ready(SwarmEvent::IncomingConnectionError { local_addr, send_back_addr, error }) => {
					trace!(target: "sub-libp2p", "Libp2p => IncomingConnectionError({},{}): {}",
						local_addr, send_back_addr, error);
					if let Some(metrics) = this.metrics.as_ref() {
						let reason = match error {
							PendingConnectionError::ConnectionLimit(_) => "limit-reached",
							PendingConnectionError::InvalidPeerId => "invalid-peer-id",
							PendingConnectionError::Transport(_) |
							PendingConnectionError::IO(_) => "transport-error",
						};

						metrics.incoming_connections_errors_total.with_label_values(&[reason]).inc();
					}
				},
				Poll::Ready(SwarmEvent::BannedPeer { peer_id, endpoint }) => {
					trace!(target: "sub-libp2p", "Libp2p => BannedPeer({}). Connected via {:?}.",
						peer_id, endpoint);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.incoming_connections_errors_total.with_label_values(&["banned"]).inc();
					}
				},
				Poll::Ready(SwarmEvent::UnknownPeerUnreachableAddr { address, error }) =>
					trace!(target: "sub-libp2p", "Libp2p => UnknownPeerUnreachableAddr({}): {}",
						address, error),
				Poll::Ready(SwarmEvent::ListenerClosed { reason, addresses }) => {
					warn!(target: "sub-libp2p", "Libp2p => ListenerClosed: {:?}", reason);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.sub(addresses.len() as u64);
					}
				},
				Poll::Ready(SwarmEvent::ListenerError { error }) => {
					trace!(target: "sub-libp2p", "Libp2p => ListenerError: {}", error);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_errors_total.inc();
					}
				},
			};
		}

		let num_connected_peers = this.network_service.user_protocol_mut().num_connected_peers();

		// Update the variables shared with the `NetworkService`.
		this.num_connected.store(num_connected_peers, Ordering::Relaxed);
		{
			let external_addresses = Swarm::<B, H>::external_addresses(&this.network_service).cloned().collect();
			*this.external_addresses.lock() = external_addresses;
		}

		let is_major_syncing = match this.network_service.user_protocol_mut().sync_state() {
			SyncState::Idle => false,
			SyncState::Downloading => true,
		};

		this.is_major_syncing.store(is_major_syncing, Ordering::Relaxed);

		if let Some(metrics) = this.metrics.as_ref() {
			metrics.network_per_sec_bytes.with_label_values(&["in"]).set(this.service.bandwidth.average_download_per_sec());
			metrics.network_per_sec_bytes.with_label_values(&["out"]).set(this.service.bandwidth.average_upload_per_sec());
			metrics.is_major_syncing.set(is_major_syncing as u64);
			for (proto, num_entries) in this.network_service.num_kbuckets_entries() {
				let proto = maybe_utf8_bytes_to_string(proto.as_bytes());
				metrics.kbuckets_num_nodes.with_label_values(&[&proto]).set(num_entries as u64);
			}
			for (proto, num_entries) in this.network_service.num_kademlia_records() {
				let proto = maybe_utf8_bytes_to_string(proto.as_bytes());
				metrics.kademlia_records_count.with_label_values(&[&proto]).set(num_entries as u64);
			}
			for (proto, num_entries) in this.network_service.kademlia_records_total_size() {
				let proto = maybe_utf8_bytes_to_string(proto.as_bytes());
				metrics.kademlia_records_sizes_total.with_label_values(&[&proto]).set(num_entries as u64);
			}
			metrics.peers_count.set(num_connected_peers as u64);
			metrics.peerset_num_discovered.set(this.network_service.user_protocol().num_discovered_peers() as u64);
			metrics.peerset_num_requested.set(this.network_service.user_protocol().requested_peers().count() as u64);
			metrics.pending_connections.set(Swarm::network_info(&this.network_service).num_connections_pending as u64);
		}

		Poll::Pending
	}
}

impl<B: BlockT + 'static, H: ExHashT> Unpin for NetworkWorker<B, H> {
}

/// Turns bytes that are potentially UTF-8 into a reasonable representable string.
///
/// Meant to be used only for debugging or metrics-reporting purposes.
fn maybe_utf8_bytes_to_string(id: &[u8]) -> Cow<str> {
	if let Ok(s) = std::str::from_utf8(&id[..]) {
		Cow::Borrowed(s)
	} else {
		Cow::Owned(format!("{:?}", id))
	}
}

/// The libp2p swarm, customized for our needs.
type Swarm<B, H> = libp2p::swarm::Swarm<Behaviour<B, H>>;

// Implementation of `import_queue::Link` trait using the available local variables.
struct NetworkLink<'a, B: BlockT, H: ExHashT> {
	protocol: &'a mut Swarm<B, H>,
}

impl<'a, B: BlockT, H: ExHashT> Link<B> for NetworkLink<'a, B, H> {
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
			info!("💔 Invalid justification provided by {} for #{}", who, hash);
			self.protocol.user_protocol_mut().disconnect_peer(&who);
			self.protocol.user_protocol_mut().report_peer(who, ReputationChange::new_fatal("Invalid justification"));
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
			info!("💔 Invalid finality proof provided by {} for #{}", who, request_block.0);
			self.protocol.user_protocol_mut().disconnect_peer(&who);
			self.protocol.user_protocol_mut().report_peer(who, ReputationChange::new_fatal("Invalid finality proof"));
		}
	}
}
