// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Main entry point of the sc-network crate.
//!
//! There are two main structs in this module: [`NetworkWorker`] and [`NetworkService`].
//! The [`NetworkWorker`] *is* the network and implements the `Future` trait. It must be polled in
//! order for the network to advance.
//! The [`NetworkService`] is merely a shared version of the [`NetworkWorker`]. You can obtain an
//! `Arc<NetworkService>` by calling [`NetworkWorker::service`].
//!
//! The methods of the [`NetworkService`] are implemented by sending a message over a channel,
//! which is then processed by [`NetworkWorker::poll`].

use crate::{
	behaviour::{self, Behaviour, BehaviourOut},
	config::{Params, TransportConfig},
	discovery::DiscoveryConfig,
	error::Error,
	network_state::{
		NetworkState, NotConnectedPeer as NetworkStateNotConnectedPeer, Peer as NetworkStatePeer,
	},
	protocol::{
		self, message::generic::Roles, NotificationsSink, NotifsHandlerError, PeerInfo, Protocol,
		Ready,
	},
	transactions, transport, ExHashT, ReputationChange,
};

use codec::Encode as _;
use futures::{channel::oneshot, prelude::*};
use libp2p::{
	core::{either::EitherError, upgrade, ConnectedPoint, Executor},
	kad::record::Key as KademliaKey,
	multiaddr,
	ping::Failure as PingFailure,
	swarm::{
		AddressScore, ConnectionError, ConnectionLimits, DialError, NetworkBehaviour,
		PendingConnectionError, Swarm, SwarmBuilder, SwarmEvent,
	},
	Multiaddr, PeerId,
};
use log::{debug, error, info, trace, warn};
use metrics::{Histogram, HistogramVec, MetricSources, Metrics};
use parking_lot::Mutex;
use sc_consensus::{BlockImportError, BlockImportStatus, ImportQueue, Link};
use sc_network_common::{
	config::MultiaddrWithPeerId,
	protocol::event::{DhtEvent, Event},
	request_responses::{IfDisconnected, RequestFailure},
	service::{
		NetworkDHTProvider, NetworkEventStream, NetworkNotification, NetworkPeers, NetworkSigner,
		NetworkStateInfo, NetworkStatus, NetworkStatusProvider, NetworkSyncForkRequest,
		NotificationSender as NotificationSenderT, NotificationSenderError,
		NotificationSenderReady as NotificationSenderReadyT, Signature, SigningError,
	},
	sync::{SyncState, SyncStatus},
};
use sc_peerset::PeersetHandle;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{
	borrow::Cow,
	cmp,
	collections::{HashMap, HashSet},
	fs, iter,
	marker::PhantomData,
	num::NonZeroUsize,
	pin::Pin,
	str,
	sync::{
		atomic::{AtomicBool, AtomicUsize, Ordering},
		Arc,
	},
	task::Poll,
};

pub use behaviour::{InboundFailure, OutboundFailure, ResponseFailure};

mod metrics;
mod out_events;
#[cfg(test)]
mod tests;

pub use libp2p::identity::{error::DecodingError, Keypair, PublicKey};
use sc_network_common::service::{NetworkBlock, NetworkRequest, NetworkTransaction};

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
	/// The `KeyPair` that defines the `PeerId` of the local node.
	local_identity: Keypair,
	/// Bandwidth logging system. Can be queried to know the average bandwidth consumed.
	bandwidth: Arc<transport::BandwidthSinks>,
	/// Peerset manager (PSM); manages the reputation of nodes and indicates the network which
	/// nodes it should be connected to or not.
	peerset: PeersetHandle,
	/// Channel that sends messages to the actual worker.
	to_worker: TracingUnboundedSender<ServiceToWorkerMsg<B, H>>,
	/// For each peer and protocol combination, an object that allows sending notifications to
	/// that peer. Updated by the [`NetworkWorker`].
	peers_notifications_sinks: Arc<Mutex<HashMap<(PeerId, Cow<'static, str>), NotificationsSink>>>,
	/// Field extracted from the [`Metrics`] struct and necessary to report the
	/// notifications-related metrics.
	notifications_sizes_metric: Option<HistogramVec>,
	/// Marker to pin the `H` generic. Serves no purpose except to not break backwards
	/// compatibility.
	_marker: PhantomData<H>,
}

impl<B, H, Client> NetworkWorker<B, H, Client>
where
	B: BlockT + 'static,
	H: ExHashT,
	Client: sp_blockchain::HeaderBackend<B> + 'static,
{
	/// Creates the network service.
	///
	/// Returns a `NetworkWorker` that implements `Future` and must be regularly polled in order
	/// for the network processing to advance. From it, you can extract a `NetworkService` using
	/// `worker.service()`. The `NetworkService` can be shared through the codebase.
	pub fn new(mut params: Params<B, H, Client>) -> Result<Self, Error> {
		// Private and public keys configuration.
		let local_identity = params.network_config.node_key.clone().into_keypair()?;
		let local_public = local_identity.public();
		let local_peer_id = local_public.to_peer_id();

		params.network_config.boot_nodes = params
			.network_config
			.boot_nodes
			.into_iter()
			.filter(|boot_node| boot_node.peer_id != local_peer_id)
			.collect();
		params.network_config.default_peers_set.reserved_nodes = params
			.network_config
			.default_peers_set
			.reserved_nodes
			.into_iter()
			.filter(|reserved_node| {
				if reserved_node.peer_id == local_peer_id {
					warn!(
						target: "sub-libp2p",
						"Local peer ID used in reserved node, ignoring: {}",
						reserved_node,
					);
					false
				} else {
					true
				}
			})
			.collect();

		// Ensure the listen addresses are consistent with the transport.
		ensure_addresses_consistent_with_transport(
			params.network_config.listen_addresses.iter(),
			&params.network_config.transport,
		)?;
		ensure_addresses_consistent_with_transport(
			params.network_config.boot_nodes.iter().map(|x| &x.multiaddr),
			&params.network_config.transport,
		)?;
		ensure_addresses_consistent_with_transport(
			params
				.network_config
				.default_peers_set
				.reserved_nodes
				.iter()
				.map(|x| &x.multiaddr),
			&params.network_config.transport,
		)?;
		for extra_set in &params.network_config.extra_sets {
			ensure_addresses_consistent_with_transport(
				extra_set.set_config.reserved_nodes.iter().map(|x| &x.multiaddr),
				&params.network_config.transport,
			)?;
		}
		ensure_addresses_consistent_with_transport(
			params.network_config.public_addresses.iter(),
			&params.network_config.transport,
		)?;

		let (to_worker, from_service) = tracing_unbounded("mpsc_network_worker");

		if let Some(path) = &params.network_config.net_config_path {
			fs::create_dir_all(path)?;
		}

		let transactions_handler_proto = transactions::TransactionsHandlerPrototype::new(
			params.protocol_id.clone(),
			params
				.chain
				.hash(0u32.into())
				.ok()
				.flatten()
				.expect("Genesis block exists; qed"),
			params.fork_id.clone(),
		);
		params
			.network_config
			.extra_sets
			.insert(0, transactions_handler_proto.set_config());

		info!(
			target: "sub-libp2p",
			"🏷  Local node identity is: {}",
			local_peer_id.to_base58(),
		);

		let default_notif_handshake_message = Roles::from(&params.role).encode();

		let (protocol, peerset_handle, mut known_addresses) = Protocol::new(
			From::from(&params.role),
			params.chain.clone(),
			params.protocol_id.clone(),
			&params.fork_id,
			&params.network_config,
			iter::once(Vec::new())
				.chain(
					(0..params.network_config.extra_sets.len() - 1)
						.map(|_| default_notif_handshake_message.clone()),
				)
				.collect(),
			params.metrics_registry.as_ref(),
			params.chain_sync,
		)?;

		// List of multiaddresses that we know in the network.
		let mut boot_node_ids = HashSet::new();

		// Process the bootnodes.
		for bootnode in params.network_config.boot_nodes.iter() {
			boot_node_ids.insert(bootnode.peer_id);
			known_addresses.push((bootnode.peer_id, bootnode.multiaddr.clone()));
		}

		let boot_node_ids = Arc::new(boot_node_ids);

		// Check for duplicate bootnodes.
		params.network_config.boot_nodes.iter().try_for_each(|bootnode| {
			if let Some(other) = params
				.network_config
				.boot_nodes
				.iter()
				.filter(|o| o.multiaddr == bootnode.multiaddr)
				.find(|o| o.peer_id != bootnode.peer_id)
			{
				Err(Error::DuplicateBootnode {
					address: bootnode.multiaddr.clone(),
					first_id: bootnode.peer_id,
					second_id: other.peer_id,
				})
			} else {
				Ok(())
			}
		})?;

		let num_connected = Arc::new(AtomicUsize::new(0));
		let is_major_syncing = Arc::new(AtomicBool::new(false));

		// Build the swarm.
		let (mut swarm, bandwidth): (Swarm<Behaviour<B, Client>>, _) = {
			let user_agent = format!(
				"{} ({})",
				params.network_config.client_version, params.network_config.node_name
			);

			let discovery_config = {
				let mut config = DiscoveryConfig::new(local_public.clone());
				config.with_permanent_addresses(known_addresses);
				config.discovery_limit(
					u64::from(params.network_config.default_peers_set.out_peers) + 15,
				);
				config.add_protocol(params.protocol_id.clone());
				config.with_dht_random_walk(params.network_config.enable_dht_random_walk);
				config.allow_non_globals_in_dht(params.network_config.allow_non_globals_in_dht);
				config.use_kademlia_disjoint_query_paths(
					params.network_config.kademlia_disjoint_query_paths,
				);

				match params.network_config.transport {
					TransportConfig::MemoryOnly => {
						config.with_mdns(false);
						config.allow_private_ipv4(false);
					},
					TransportConfig::Normal { enable_mdns, allow_private_ipv4, .. } => {
						config.with_mdns(enable_mdns);
						config.allow_private_ipv4(allow_private_ipv4);
					},
				}

				config
			};

			let (transport, bandwidth) = {
				let config_mem = match params.network_config.transport {
					TransportConfig::MemoryOnly => true,
					TransportConfig::Normal { .. } => false,
				};

				// The yamux buffer size limit is configured to be equal to the maximum frame size
				// of all protocols. 10 bytes are added to each limit for the length prefix that
				// is not included in the upper layer protocols limit but is still present in the
				// yamux buffer. These 10 bytes correspond to the maximum size required to encode
				// a variable-length-encoding 64bits number. In other words, we make the
				// assumption that no notification larger than 2^64 will ever be sent.
				let yamux_maximum_buffer_size = {
					let requests_max = params
						.network_config
						.request_response_protocols
						.iter()
						.map(|cfg| usize::try_from(cfg.max_request_size).unwrap_or(usize::MAX));
					let responses_max =
						params.network_config.request_response_protocols.iter().map(|cfg| {
							usize::try_from(cfg.max_response_size).unwrap_or(usize::MAX)
						});
					let notifs_max = params.network_config.extra_sets.iter().map(|cfg| {
						usize::try_from(cfg.max_notification_size).unwrap_or(usize::MAX)
					});

					// A "default" max is added to cover all the other protocols: ping, identify,
					// kademlia, block announces, and transactions.
					let default_max = cmp::max(
						1024 * 1024,
						usize::try_from(protocol::BLOCK_ANNOUNCES_TRANSACTIONS_SUBSTREAM_SIZE)
							.unwrap_or(usize::MAX),
					);

					iter::once(default_max)
						.chain(requests_max)
						.chain(responses_max)
						.chain(notifs_max)
						.max()
						.expect("iterator known to always yield at least one element; qed")
						.saturating_add(10)
				};

				transport::build_transport(
					local_identity.clone(),
					config_mem,
					params.network_config.yamux_window_size,
					yamux_maximum_buffer_size,
				)
			};

			let behaviour = {
				let result = Behaviour::new(
					protocol,
					user_agent,
					local_public,
					discovery_config,
					params.block_request_protocol_config,
					params.state_request_protocol_config,
					params.warp_sync_protocol_config,
					params.bitswap,
					params.light_client_request_protocol_config,
					params.network_config.request_response_protocols,
					peerset_handle.clone(),
				);

				match result {
					Ok(b) => b,
					Err(crate::request_responses::RegisterError::DuplicateProtocol(proto)) =>
						return Err(Error::DuplicateRequestResponseProtocol { protocol: proto }),
				}
			};

			let mut builder = SwarmBuilder::new(transport, behaviour, local_peer_id)
				.connection_limits(
					ConnectionLimits::default()
						.with_max_established_per_peer(Some(crate::MAX_CONNECTIONS_PER_PEER as u32))
						.with_max_established_incoming(Some(
							crate::MAX_CONNECTIONS_ESTABLISHED_INCOMING,
						)),
				)
				.substream_upgrade_protocol_override(upgrade::Version::V1Lazy)
				.notify_handler_buffer_size(NonZeroUsize::new(32).expect("32 != 0; qed"))
				.connection_event_buffer_size(1024)
				.max_negotiating_inbound_streams(2048);
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

		// Initialize the metrics.
		let metrics = match &params.metrics_registry {
			Some(registry) => Some(metrics::register(
				registry,
				MetricSources {
					bandwidth: bandwidth.clone(),
					major_syncing: is_major_syncing.clone(),
					connected_peers: num_connected.clone(),
				},
			)?),
			None => None,
		};

		// Listen on multiaddresses.
		for addr in &params.network_config.listen_addresses {
			if let Err(err) = Swarm::<Behaviour<B, Client>>::listen_on(&mut swarm, addr.clone()) {
				warn!(target: "sub-libp2p", "Can't listen on {} because: {:?}", addr, err)
			}
		}

		// Add external addresses.
		for addr in &params.network_config.public_addresses {
			Swarm::<Behaviour<B, Client>>::add_external_address(
				&mut swarm,
				addr.clone(),
				AddressScore::Infinite,
			);
		}

		let external_addresses = Arc::new(Mutex::new(Vec::new()));
		let peers_notifications_sinks = Arc::new(Mutex::new(HashMap::new()));

		let service = Arc::new(NetworkService {
			bandwidth,
			external_addresses: external_addresses.clone(),
			num_connected: num_connected.clone(),
			is_major_syncing: is_major_syncing.clone(),
			peerset: peerset_handle,
			local_peer_id,
			local_identity,
			to_worker,
			peers_notifications_sinks: peers_notifications_sinks.clone(),
			notifications_sizes_metric: metrics
				.as_ref()
				.map(|metrics| metrics.notifications_sizes.clone()),
			_marker: PhantomData,
		});

		let (tx_handler, tx_handler_controller) = transactions_handler_proto.build(
			service.clone(),
			params.transaction_pool,
			params.metrics_registry.as_ref(),
		)?;
		(params.transactions_handler_executor)(tx_handler.run().boxed());

		Ok(NetworkWorker {
			external_addresses,
			num_connected,
			is_major_syncing,
			network_service: swarm,
			service,
			import_queue: params.import_queue,
			from_service,
			event_streams: out_events::OutChannels::new(params.metrics_registry.as_ref())?,
			peers_notifications_sinks,
			tx_handler_controller,
			metrics,
			boot_node_ids,
		})
	}

	/// High-level network status information.
	pub fn status(&self) -> NetworkStatus<B> {
		let status = self.sync_state();
		NetworkStatus {
			sync_state: status.state,
			best_seen_block: self.best_seen_block(),
			num_sync_peers: self.num_sync_peers(),
			num_connected_peers: self.num_connected_peers(),
			num_active_peers: self.num_active_peers(),
			total_bytes_inbound: self.total_bytes_inbound(),
			total_bytes_outbound: self.total_bytes_outbound(),
			state_sync: status.state_sync,
			warp_sync: status.warp_sync,
		}
	}

	/// Returns the total number of bytes received so far.
	pub fn total_bytes_inbound(&self) -> u64 {
		self.service.bandwidth.total_inbound()
	}

	/// Returns the total number of bytes sent so far.
	pub fn total_bytes_outbound(&self) -> u64 {
		self.service.bandwidth.total_outbound()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.network_service.behaviour().user_protocol().num_connected_peers()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.network_service.behaviour().user_protocol().num_active_peers()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncStatus<B> {
		self.network_service.behaviour().user_protocol().sync_state()
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.network_service.behaviour().user_protocol().best_seen_block()
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.network_service.behaviour().user_protocol().num_sync_peers()
	}

	/// Number of blocks in the import queue.
	pub fn num_queued_blocks(&self) -> u32 {
		self.network_service.behaviour().user_protocol().num_queued_blocks()
	}

	/// Returns the number of downloaded blocks.
	pub fn num_downloaded_blocks(&self) -> usize {
		self.network_service.behaviour().user_protocol().num_downloaded_blocks()
	}

	/// Number of active sync requests.
	pub fn num_sync_requests(&self) -> usize {
		self.network_service.behaviour().user_protocol().num_sync_requests()
	}

	/// Adds an address for a node.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.network_service.behaviour_mut().add_known_address(peer_id, addr);
	}

	/// Return a `NetworkService` that can be shared through the code base and can be used to
	/// manipulate the worker.
	pub fn service(&self) -> &Arc<NetworkService<B, H>> {
		&self.service
	}

	/// You must call this when a new block is finalized by the client.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: B::Header) {
		self.network_service
			.behaviour_mut()
			.user_protocol_mut()
			.on_block_finalized(hash, &header);
	}

	/// Inform the network service about new best imported block.
	pub fn new_best_block_imported(&mut self, hash: B::Hash, number: NumberFor<B>) {
		self.network_service
			.behaviour_mut()
			.user_protocol_mut()
			.new_best_block_imported(hash, number);
	}

	/// Returns the local `PeerId`.
	pub fn local_peer_id(&self) -> &PeerId {
		Swarm::<Behaviour<B, Client>>::local_peer_id(&self.network_service)
	}

	/// Returns the list of addresses we are listening on.
	///
	/// Does **NOT** include a trailing `/p2p/` with our `PeerId`.
	pub fn listen_addresses(&self) -> impl Iterator<Item = &Multiaddr> {
		Swarm::<Behaviour<B, Client>>::listeners(&self.network_service)
	}

	/// Get network state.
	///
	/// **Note**: Use this only for debugging. This API is unstable. There are warnings literally
	/// everywhere about this. Please don't use this function to retrieve actual information.
	pub fn network_state(&mut self) -> NetworkState {
		let swarm = &mut self.network_service;
		let open = swarm.behaviour_mut().user_protocol().open_peers().cloned().collect::<Vec<_>>();

		let connected_peers = {
			let swarm = &mut *swarm;
			open.iter()
				.filter_map(move |peer_id| {
					let known_addresses =
						NetworkBehaviour::addresses_of_peer(swarm.behaviour_mut(), peer_id)
							.into_iter()
							.collect();

					let endpoint = if let Some(e) =
						swarm.behaviour_mut().node(peer_id).and_then(|i| i.endpoint())
					{
						e.clone().into()
					} else {
						error!(target: "sub-libp2p", "Found state inconsistency between custom protocol \
						and debug information about {:?}", peer_id);
						return None
					};

					Some((
						peer_id.to_base58(),
						NetworkStatePeer {
							endpoint,
							version_string: swarm
								.behaviour_mut()
								.node(peer_id)
								.and_then(|i| i.client_version().map(|s| s.to_owned())),
							latest_ping_time: swarm
								.behaviour_mut()
								.node(peer_id)
								.and_then(|i| i.latest_ping()),
							known_addresses,
						},
					))
				})
				.collect()
		};

		let not_connected_peers = {
			let swarm = &mut *swarm;
			swarm
				.behaviour_mut()
				.known_peers()
				.into_iter()
				.filter(|p| open.iter().all(|n| n != p))
				.map(move |peer_id| {
					(
						peer_id.to_base58(),
						NetworkStateNotConnectedPeer {
							version_string: swarm
								.behaviour_mut()
								.node(&peer_id)
								.and_then(|i| i.client_version().map(|s| s.to_owned())),
							latest_ping_time: swarm
								.behaviour_mut()
								.node(&peer_id)
								.and_then(|i| i.latest_ping()),
							known_addresses: NetworkBehaviour::addresses_of_peer(
								swarm.behaviour_mut(),
								&peer_id,
							)
							.into_iter()
							.collect(),
						},
					)
				})
				.collect()
		};

		let peer_id = Swarm::<Behaviour<B, Client>>::local_peer_id(swarm).to_base58();
		let listened_addresses = swarm.listeners().cloned().collect();
		let external_addresses = swarm.external_addresses().map(|r| &r.addr).cloned().collect();

		NetworkState {
			peer_id,
			listened_addresses,
			external_addresses,
			connected_peers,
			not_connected_peers,
			peerset: swarm.behaviour_mut().user_protocol_mut().peerset_debug_info(),
		}
	}

	/// Get currently connected peers.
	pub fn peers_debug_info(&mut self) -> Vec<(PeerId, PeerInfo<B>)> {
		self.network_service
			.behaviour_mut()
			.user_protocol_mut()
			.peers_info()
			.map(|(id, info)| (*id, info.clone()))
			.collect()
	}

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.service.remove_reserved_peer(peer);
	}

	/// Adds a `PeerId` and its `Multiaddr` as reserved.
	pub fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String> {
		self.service.add_reserved_peer(peer)
	}

	/// Returns the list of reserved peers.
	pub fn reserved_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.network_service.behaviour().user_protocol().reserved_peers()
	}
}

impl<B: BlockT + 'static, H: ExHashT> NetworkService<B, H> {
	/// Get network state.
	///
	/// **Note**: Use this only for debugging. This API is unstable. There are warnings literally
	/// everywhere about this. Please don't use this function to retrieve actual information.
	///
	/// Returns an error if the `NetworkWorker` is no longer running.
	pub async fn network_state(&self) -> Result<NetworkState, ()> {
		let (tx, rx) = oneshot::channel();

		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::NetworkState { pending_response: tx });

		match rx.await {
			Ok(v) => v.map_err(|_| ()),
			// The channel can only be closed if the network worker no longer exists.
			Err(_) => Err(()),
		}
	}

	/// Utility function to extract `PeerId` from each `Multiaddr` for peer set updates.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn split_multiaddr_and_peer_id(
		&self,
		peers: HashSet<Multiaddr>,
	) -> Result<Vec<(PeerId, Multiaddr)>, String> {
		peers
			.into_iter()
			.map(|mut addr| {
				let peer = match addr.pop() {
					Some(multiaddr::Protocol::P2p(key)) => PeerId::from_multihash(key)
						.map_err(|_| "Invalid PeerId format".to_string())?,
					_ => return Err("Missing PeerId from address".to_string()),
				};

				// Make sure the local peer ID is never added to the PSM
				// or added as a "known address", even if given.
				if peer == self.local_peer_id {
					Err("Local peer ID in peer set.".to_string())
				} else {
					Ok((peer, addr))
				}
			})
			.collect::<Result<Vec<(PeerId, Multiaddr)>, String>>()
	}
}

impl<B: BlockT + 'static, H: ExHashT> sp_consensus::SyncOracle for NetworkService<B, H> {
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}

	fn is_offline(&self) -> bool {
		self.num_connected.load(Ordering::Relaxed) == 0
	}
}

impl<B: BlockT, H: ExHashT> sc_consensus::JustificationSyncLink<B> for NetworkService<B, H> {
	/// Request a justification for the given block from the network.
	///
	/// On success, the justification will be passed to the import queue that was part at
	/// initialization as part of the configuration.
	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::RequestJustification(*hash, number));
	}

	fn clear_justification_requests(&self) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::ClearJustificationRequests);
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
		self.local_peer_id
	}
}

impl<B, H> NetworkSigner for NetworkService<B, H>
where
	B: sp_runtime::traits::Block,
	H: ExHashT,
{
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError> {
		Signature::sign_message(msg.as_ref(), &self.local_identity)
	}
}

impl<B, H> NetworkDHTProvider for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	/// Start getting a value from the DHT.
	///
	/// This will generate either a `ValueFound` or a `ValueNotFound` event and pass it as an
	/// item on the [`NetworkWorker`] stream.
	fn get_value(&self, key: &KademliaKey) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::GetValue(key.clone()));
	}

	/// Start putting a value in the DHT.
	///
	/// This will generate either a `ValuePut` or a `ValuePutFailed` event and pass it as an
	/// item on the [`NetworkWorker`] stream.
	fn put_value(&self, key: KademliaKey, value: Vec<u8>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::PutValue(key, value));
	}
}

impl<B, H> NetworkSyncForkRequest<B::Hash, NumberFor<B>> for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	/// Configure an explicit fork sync request.
	/// Note that this function should not be used for recent blocks.
	/// Sync should be able to download all the recent forks normally.
	/// `set_sync_fork_request` should only be used if external code detects that there's
	/// a stale fork missing.
	/// Passing empty `peers` set effectively removes the sync request.
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::SyncFork(peers, hash, number));
	}
}

#[async_trait::async_trait]
impl<B, H> NetworkStatusProvider<B> for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	async fn status(&self) -> Result<NetworkStatus<B>, ()> {
		let (tx, rx) = oneshot::channel();

		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::NetworkStatus { pending_response: tx });

		match rx.await {
			Ok(v) => v.map_err(|_| ()),
			// The channel can only be closed if the network worker no longer exists.
			Err(_) => Err(()),
		}
	}
}

impl<B, H> NetworkPeers for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn set_authorized_peers(&self, peers: HashSet<PeerId>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::SetReserved(peers));
	}

	fn set_authorized_only(&self, reserved_only: bool) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::SetReservedOnly(reserved_only));
	}

	fn add_known_address(&self, peer_id: PeerId, addr: Multiaddr) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
	}

	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		self.peerset.report_peer(who, cost_benefit);
	}

	fn disconnect_peer(&self, who: PeerId, protocol: Cow<'static, str>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::DisconnectPeer(who, protocol));
	}

	fn accept_unreserved_peers(&self) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::SetReservedOnly(false));
	}

	fn deny_unreserved_peers(&self) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::SetReservedOnly(true));
	}

	fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String> {
		// Make sure the local peer ID is never added to the PSM.
		if peer.peer_id == self.local_peer_id {
			return Err("Local peer ID cannot be added as a reserved peer.".to_string())
		}

		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer.peer_id, peer.multiaddr));
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::AddReserved(peer.peer_id));
		Ok(())
	}

	fn remove_reserved_peer(&self, peer_id: PeerId) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::RemoveReserved(peer_id));
	}

	fn set_reserved_peers(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		let peers_addrs = self.split_multiaddr_and_peer_id(peers)?;

		let mut peers: HashSet<PeerId> = HashSet::with_capacity(peers_addrs.len());

		for (peer_id, addr) in peers_addrs.into_iter() {
			// Make sure the local peer ID is never added to the PSM.
			if peer_id == self.local_peer_id {
				return Err("Local peer ID cannot be added as a reserved peer.".to_string())
			}

			peers.insert(peer_id);

			if !addr.is_empty() {
				let _ = self
					.to_worker
					.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
			}
		}

		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::SetPeersetReserved(protocol, peers));

		Ok(())
	}

	fn add_peers_to_reserved_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		let peers = self.split_multiaddr_and_peer_id(peers)?;

		for (peer_id, addr) in peers.into_iter() {
			// Make sure the local peer ID is never added to the PSM.
			if peer_id == self.local_peer_id {
				return Err("Local peer ID cannot be added as a reserved peer.".to_string())
			}

			if !addr.is_empty() {
				let _ = self
					.to_worker
					.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
			}
			let _ = self
				.to_worker
				.unbounded_send(ServiceToWorkerMsg::AddSetReserved(protocol.clone(), peer_id));
		}

		Ok(())
	}

	fn remove_peers_from_reserved_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>) {
		for peer_id in peers.into_iter() {
			let _ = self
				.to_worker
				.unbounded_send(ServiceToWorkerMsg::RemoveSetReserved(protocol.clone(), peer_id));
		}
	}

	fn add_to_peers_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		let peers = self.split_multiaddr_and_peer_id(peers)?;

		for (peer_id, addr) in peers.into_iter() {
			// Make sure the local peer ID is never added to the PSM.
			if peer_id == self.local_peer_id {
				return Err("Local peer ID cannot be added as a reserved peer.".to_string())
			}

			if !addr.is_empty() {
				let _ = self
					.to_worker
					.unbounded_send(ServiceToWorkerMsg::AddKnownAddress(peer_id, addr));
			}
			let _ = self
				.to_worker
				.unbounded_send(ServiceToWorkerMsg::AddToPeersSet(protocol.clone(), peer_id));
		}

		Ok(())
	}

	fn remove_from_peers_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>) {
		for peer_id in peers.into_iter() {
			let _ = self
				.to_worker
				.unbounded_send(ServiceToWorkerMsg::RemoveFromPeersSet(protocol.clone(), peer_id));
		}
	}

	fn sync_num_connected(&self) -> usize {
		self.num_connected.load(Ordering::Relaxed)
	}
}

impl<B, H> NetworkEventStream for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn event_stream(&self, name: &'static str) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
		let (tx, rx) = out_events::channel(name);
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::EventStream(tx));
		Box::pin(rx)
	}
}

impl<B, H> NetworkNotification for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn write_notification(&self, target: PeerId, protocol: Cow<'static, str>, message: Vec<u8>) {
		// We clone the `NotificationsSink` in order to be able to unlock the network-wide
		// `peers_notifications_sinks` mutex as soon as possible.
		let sink = {
			let peers_notifications_sinks = self.peers_notifications_sinks.lock();
			if let Some(sink) = peers_notifications_sinks.get(&(target, protocol.clone())) {
				sink.clone()
			} else {
				// Notification silently discarded, as documented.
				debug!(
					target: "sub-libp2p",
					"Attempted to send notification on missing or closed substream: {}, {:?}",
					target, protocol,
				);
				return
			}
		};

		if let Some(notifications_sizes_metric) = self.notifications_sizes_metric.as_ref() {
			notifications_sizes_metric
				.with_label_values(&["out", &protocol])
				.observe(message.len() as f64);
		}

		// Sending is communicated to the `NotificationsSink`.
		trace!(
			target: "sub-libp2p",
			"External API => Notification({:?}, {:?}, {} bytes)",
			target, protocol, message.len()
		);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Sync notification", target);
		sink.send_sync_notification(message);
	}

	fn notification_sender(
		&self,
		target: PeerId,
		protocol: Cow<'static, str>,
	) -> Result<Box<dyn NotificationSenderT>, NotificationSenderError> {
		// We clone the `NotificationsSink` in order to be able to unlock the network-wide
		// `peers_notifications_sinks` mutex as soon as possible.
		let sink = {
			let peers_notifications_sinks = self.peers_notifications_sinks.lock();
			if let Some(sink) = peers_notifications_sinks.get(&(target, protocol.clone())) {
				sink.clone()
			} else {
				return Err(NotificationSenderError::Closed)
			}
		};

		let notification_size_metric = self
			.notifications_sizes_metric
			.as_ref()
			.map(|histogram| histogram.with_label_values(&["out", &protocol]));

		Ok(Box::new(NotificationSender { sink, protocol_name: protocol, notification_size_metric }))
	}
}

#[async_trait::async_trait]
impl<B, H> NetworkRequest for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	async fn request(
		&self,
		target: PeerId,
		protocol: Cow<'static, str>,
		request: Vec<u8>,
		connect: IfDisconnected,
	) -> Result<Vec<u8>, RequestFailure> {
		let (tx, rx) = oneshot::channel();

		self.start_request(target, protocol, request, tx, connect);

		match rx.await {
			Ok(v) => v,
			// The channel can only be closed if the network worker no longer exists. If the
			// network worker no longer exists, then all connections to `target` are necessarily
			// closed, and we legitimately report this situation as a "ConnectionClosed".
			Err(_) => Err(RequestFailure::Network(OutboundFailure::ConnectionClosed)),
		}
	}

	fn start_request(
		&self,
		target: PeerId,
		protocol: Cow<'static, str>,
		request: Vec<u8>,
		tx: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		connect: IfDisconnected,
	) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::Request {
			target,
			protocol: protocol.into(),
			request,
			pending_response: tx,
			connect,
		});
	}
}

impl<B, H> NetworkTransaction<H> for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn trigger_repropagate(&self) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::PropagateTransactions);
	}

	fn propagate_transaction(&self, hash: H) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::PropagateTransaction(hash));
	}
}

impl<B, H> NetworkBlock<B::Hash, NumberFor<B>> for NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn announce_block(&self, hash: B::Hash, data: Option<Vec<u8>>) {
		let _ = self.to_worker.unbounded_send(ServiceToWorkerMsg::AnnounceBlock(hash, data));
	}

	fn new_best_block_imported(&self, hash: B::Hash, number: NumberFor<B>) {
		let _ = self
			.to_worker
			.unbounded_send(ServiceToWorkerMsg::NewBestBlockImported(hash, number));
	}
}

/// A `NotificationSender` allows for sending notifications to a peer with a chosen protocol.
#[must_use]
pub struct NotificationSender {
	sink: NotificationsSink,

	/// Name of the protocol on the wire.
	protocol_name: Cow<'static, str>,

	/// Field extracted from the [`Metrics`] struct and necessary to report the
	/// notifications-related metrics.
	notification_size_metric: Option<Histogram>,
}

#[async_trait::async_trait]
impl NotificationSenderT for NotificationSender {
	async fn ready(
		&self,
	) -> Result<Box<dyn NotificationSenderReadyT + '_>, NotificationSenderError> {
		Ok(Box::new(NotificationSenderReady {
			ready: match self.sink.reserve_notification().await {
				Ok(r) => Some(r),
				Err(()) => return Err(NotificationSenderError::Closed),
			},
			peer_id: self.sink.peer_id(),
			protocol_name: &self.protocol_name,
			notification_size_metric: self.notification_size_metric.clone(),
		}))
	}
}

/// Reserved slot in the notifications buffer, ready to accept data.
#[must_use]
pub struct NotificationSenderReady<'a> {
	ready: Option<Ready<'a>>,

	/// Target of the notification.
	peer_id: &'a PeerId,

	/// Name of the protocol on the wire.
	protocol_name: &'a Cow<'static, str>,

	/// Field extracted from the [`Metrics`] struct and necessary to report the
	/// notifications-related metrics.
	notification_size_metric: Option<Histogram>,
}

impl<'a> NotificationSenderReadyT for NotificationSenderReady<'a> {
	fn send(&mut self, notification: Vec<u8>) -> Result<(), NotificationSenderError> {
		if let Some(notification_size_metric) = &self.notification_size_metric {
			notification_size_metric.observe(notification.len() as f64);
		}

		trace!(
			target: "sub-libp2p",
			"External API => Notification({:?}, {}, {} bytes)",
			self.peer_id, self.protocol_name, notification.len(),
		);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Async notification", self.peer_id);

		self.ready
			.take()
			.ok_or(NotificationSenderError::Closed)?
			.send(notification)
			.map_err(|()| NotificationSenderError::Closed)
	}
}

/// Messages sent from the `NetworkService` to the `NetworkWorker`.
///
/// Each entry corresponds to a method of `NetworkService`.
enum ServiceToWorkerMsg<B: BlockT, H: ExHashT> {
	PropagateTransaction(H),
	PropagateTransactions,
	RequestJustification(B::Hash, NumberFor<B>),
	ClearJustificationRequests,
	AnnounceBlock(B::Hash, Option<Vec<u8>>),
	GetValue(KademliaKey),
	PutValue(KademliaKey, Vec<u8>),
	AddKnownAddress(PeerId, Multiaddr),
	SetReservedOnly(bool),
	AddReserved(PeerId),
	RemoveReserved(PeerId),
	SetReserved(HashSet<PeerId>),
	SetPeersetReserved(Cow<'static, str>, HashSet<PeerId>),
	AddSetReserved(Cow<'static, str>, PeerId),
	RemoveSetReserved(Cow<'static, str>, PeerId),
	AddToPeersSet(Cow<'static, str>, PeerId),
	RemoveFromPeersSet(Cow<'static, str>, PeerId),
	SyncFork(Vec<PeerId>, B::Hash, NumberFor<B>),
	EventStream(out_events::Sender),
	Request {
		target: PeerId,
		protocol: Cow<'static, str>,
		request: Vec<u8>,
		pending_response: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		connect: IfDisconnected,
	},
	NetworkStatus {
		pending_response: oneshot::Sender<Result<NetworkStatus<B>, RequestFailure>>,
	},
	NetworkState {
		pending_response: oneshot::Sender<Result<NetworkState, RequestFailure>>,
	},
	DisconnectPeer(PeerId, Cow<'static, str>),
	NewBestBlockImported(B::Hash, NumberFor<B>),
}

/// Main network worker. Must be polled in order for the network to advance.
///
/// You are encouraged to poll this in a separate background thread or task.
#[must_use = "The NetworkWorker must be polled in order for the network to advance"]
pub struct NetworkWorker<B, H, Client>
where
	B: BlockT + 'static,
	H: ExHashT,
	Client: HeaderBackend<B> + 'static,
{
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	external_addresses: Arc<Mutex<Vec<Multiaddr>>>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	num_connected: Arc<AtomicUsize>,
	/// Updated by the `NetworkWorker` and loaded by the `NetworkService`.
	is_major_syncing: Arc<AtomicBool>,
	/// The network service that can be extracted and shared through the codebase.
	service: Arc<NetworkService<B, H>>,
	/// The *actual* network.
	network_service: Swarm<Behaviour<B, Client>>,
	/// The import queue that was passed at initialization.
	import_queue: Box<dyn ImportQueue<B>>,
	/// Messages from the [`NetworkService`] that must be processed.
	from_service: TracingUnboundedReceiver<ServiceToWorkerMsg<B, H>>,
	/// Senders for events that happen on the network.
	event_streams: out_events::OutChannels,
	/// Prometheus network metrics.
	metrics: Option<Metrics>,
	/// The `PeerId`'s of all boot nodes.
	boot_node_ids: Arc<HashSet<PeerId>>,
	/// For each peer and protocol combination, an object that allows sending notifications to
	/// that peer. Shared with the [`NetworkService`].
	peers_notifications_sinks: Arc<Mutex<HashMap<(PeerId, Cow<'static, str>), NotificationsSink>>>,
	/// Controller for the handler of incoming and outgoing transactions.
	tx_handler_controller: transactions::TransactionsHandlerController<H>,
}

impl<B, H, Client> Future for NetworkWorker<B, H, Client>
where
	B: BlockT + 'static,
	H: ExHashT,
	Client: HeaderBackend<B> + 'static,
{
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<Self::Output> {
		let this = &mut *self;

		// Poll the import queue for actions to perform.
		this.import_queue
			.poll_actions(cx, &mut NetworkLink { protocol: &mut this.network_service });

		// At the time of writing of this comment, due to a high volume of messages, the network
		// worker sometimes takes a long time to process the loop below. When that happens, the
		// rest of the polling is frozen. In order to avoid negative side-effects caused by this
		// freeze, a limit to the number of iterations is enforced below. If the limit is reached,
		// the task is interrupted then scheduled again.
		//
		// This allows for a more even distribution in the time taken by each sub-part of the
		// polling.
		let mut num_iterations = 0;
		loop {
			num_iterations += 1;
			if num_iterations >= 100 {
				cx.waker().wake_by_ref();
				break
			}

			// Process the next message coming from the `NetworkService`.
			let msg = match this.from_service.poll_next_unpin(cx) {
				Poll::Ready(Some(msg)) => msg,
				Poll::Ready(None) => return Poll::Ready(()),
				Poll::Pending => break,
			};
			match msg {
				ServiceToWorkerMsg::AnnounceBlock(hash, data) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.announce_block(hash, data),
				ServiceToWorkerMsg::RequestJustification(hash, number) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.request_justification(&hash, number),
				ServiceToWorkerMsg::ClearJustificationRequests => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.clear_justification_requests(),
				ServiceToWorkerMsg::PropagateTransaction(hash) =>
					this.tx_handler_controller.propagate_transaction(hash),
				ServiceToWorkerMsg::PropagateTransactions =>
					this.tx_handler_controller.propagate_transactions(),
				ServiceToWorkerMsg::GetValue(key) =>
					this.network_service.behaviour_mut().get_value(key),
				ServiceToWorkerMsg::PutValue(key, value) =>
					this.network_service.behaviour_mut().put_value(key, value),
				ServiceToWorkerMsg::SetReservedOnly(reserved_only) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.set_reserved_only(reserved_only),
				ServiceToWorkerMsg::SetReserved(peers) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.set_reserved_peers(peers),
				ServiceToWorkerMsg::SetPeersetReserved(protocol, peers) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.set_reserved_peerset_peers(protocol, peers),
				ServiceToWorkerMsg::AddReserved(peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.add_reserved_peer(peer_id),
				ServiceToWorkerMsg::RemoveReserved(peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.remove_reserved_peer(peer_id),
				ServiceToWorkerMsg::AddSetReserved(protocol, peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.add_set_reserved_peer(protocol, peer_id),
				ServiceToWorkerMsg::RemoveSetReserved(protocol, peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.remove_set_reserved_peer(protocol, peer_id),
				ServiceToWorkerMsg::AddKnownAddress(peer_id, addr) =>
					this.network_service.behaviour_mut().add_known_address(peer_id, addr),
				ServiceToWorkerMsg::AddToPeersSet(protocol, peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.add_to_peers_set(protocol, peer_id),
				ServiceToWorkerMsg::RemoveFromPeersSet(protocol, peer_id) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.remove_from_peers_set(protocol, peer_id),
				ServiceToWorkerMsg::SyncFork(peer_ids, hash, number) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.set_sync_fork_request(peer_ids, &hash, number),
				ServiceToWorkerMsg::EventStream(sender) => this.event_streams.push(sender),
				ServiceToWorkerMsg::Request {
					target,
					protocol,
					request,
					pending_response,
					connect,
				} => {
					this.network_service.behaviour_mut().send_request(
						&target,
						&protocol,
						request,
						pending_response,
						connect,
					);
				},
				ServiceToWorkerMsg::NetworkStatus { pending_response } => {
					let _ = pending_response.send(Ok(this.status()));
				},
				ServiceToWorkerMsg::NetworkState { pending_response } => {
					let _ = pending_response.send(Ok(this.network_state()));
				},
				ServiceToWorkerMsg::DisconnectPeer(who, protocol_name) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.disconnect_peer(&who, &protocol_name),
				ServiceToWorkerMsg::NewBestBlockImported(hash, number) => this
					.network_service
					.behaviour_mut()
					.user_protocol_mut()
					.new_best_block_imported(hash, number),
			}
		}

		// `num_iterations` serves the same purpose as in the previous loop.
		// See the previous loop for explanations.
		let mut num_iterations = 0;
		loop {
			num_iterations += 1;
			if num_iterations >= 1000 {
				cx.waker().wake_by_ref();
				break
			}

			// Process the next action coming from the network.
			let next_event = this.network_service.select_next_some();
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
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::JustificationImport(
					origin,
					hash,
					nb,
					justifications,
				))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.import_queue_justifications_submitted.inc();
					}
					this.import_queue.import_justifications(origin, hash, nb, justifications);
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::InboundRequest {
					protocol,
					result,
					..
				})) => {
					if let Some(metrics) = this.metrics.as_ref() {
						match result {
							Ok(serve_time) => {
								metrics
									.requests_in_success_total
									.with_label_values(&[&protocol])
									.observe(serve_time.as_secs_f64());
							},
							Err(err) => {
								let reason = match err {
									ResponseFailure::Network(InboundFailure::Timeout) => "timeout",
									ResponseFailure::Network(
										InboundFailure::UnsupportedProtocols,
									) =>
									// `UnsupportedProtocols` is reported for every single
									// inbound request whenever a request with an unsupported
									// protocol is received. This is not reported in order to
									// avoid confusions.
										continue,
									ResponseFailure::Network(InboundFailure::ResponseOmission) =>
										"busy-omitted",
									ResponseFailure::Network(InboundFailure::ConnectionClosed) =>
										"connection-closed",
								};

								metrics
									.requests_in_failure_total
									.with_label_values(&[&protocol, reason])
									.inc();
							},
						}
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::RequestFinished {
					protocol,
					duration,
					result,
					..
				})) =>
					if let Some(metrics) = this.metrics.as_ref() {
						match result {
							Ok(_) => {
								metrics
									.requests_out_success_total
									.with_label_values(&[&protocol])
									.observe(duration.as_secs_f64());
							},
							Err(err) => {
								let reason = match err {
									RequestFailure::NotConnected => "not-connected",
									RequestFailure::UnknownProtocol => "unknown-protocol",
									RequestFailure::Refused => "refused",
									RequestFailure::Obsolete => "obsolete",
									RequestFailure::Network(OutboundFailure::DialFailure) =>
										"dial-failure",
									RequestFailure::Network(OutboundFailure::Timeout) => "timeout",
									RequestFailure::Network(OutboundFailure::ConnectionClosed) =>
										"connection-closed",
									RequestFailure::Network(
										OutboundFailure::UnsupportedProtocols,
									) => "unsupported",
								};

								metrics
									.requests_out_failure_total
									.with_label_values(&[&protocol, reason])
									.inc();
							},
						}
					},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::RandomKademliaStarted(
					protocol,
				))) =>
					if let Some(metrics) = this.metrics.as_ref() {
						metrics
							.kademlia_random_queries_total
							.with_label_values(&[protocol.as_ref()])
							.inc();
					},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::NotificationStreamOpened {
					remote,
					protocol,
					negotiated_fallback,
					notifications_sink,
					role,
				})) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics
							.notifications_streams_opened_total
							.with_label_values(&[&protocol])
							.inc();
					}
					{
						let mut peers_notifications_sinks = this.peers_notifications_sinks.lock();
						let _previous_value = peers_notifications_sinks
							.insert((remote, protocol.clone()), notifications_sink);
						debug_assert!(_previous_value.is_none());
					}
					this.event_streams.send(Event::NotificationStreamOpened {
						remote,
						protocol,
						negotiated_fallback,
						role,
					});
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::NotificationStreamReplaced {
					remote,
					protocol,
					notifications_sink,
				})) => {
					let mut peers_notifications_sinks = this.peers_notifications_sinks.lock();
					if let Some(s) = peers_notifications_sinks.get_mut(&(remote, protocol)) {
						*s = notifications_sink;
					} else {
						error!(
							target: "sub-libp2p",
							"NotificationStreamReplaced for non-existing substream"
						);
						debug_assert!(false);
					}

					// TODO: Notifications might have been lost as a result of the previous
					// connection being dropped, and as a result it would be preferable to notify
					// the users of this fact by simulating the substream being closed then
					// reopened.
					// The code below doesn't compile because `role` is unknown. Propagating the
					// handshake of the secondary connections is quite an invasive change and
					// would conflict with https://github.com/paritytech/substrate/issues/6403.
					// Considering that dropping notifications is generally regarded as
					// acceptable, this bug is at the moment intentionally left there and is
					// intended to be fixed at the same time as
					// https://github.com/paritytech/substrate/issues/6403.
					// this.event_streams.send(Event::NotificationStreamClosed {
					// remote,
					// protocol,
					// });
					// this.event_streams.send(Event::NotificationStreamOpened {
					// remote,
					// protocol,
					// role,
					// });
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::NotificationStreamClosed {
					remote,
					protocol,
				})) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics
							.notifications_streams_closed_total
							.with_label_values(&[&protocol[..]])
							.inc();
					}
					this.event_streams.send(Event::NotificationStreamClosed {
						remote,
						protocol: protocol.clone(),
					});
					{
						let mut peers_notifications_sinks = this.peers_notifications_sinks.lock();
						let _previous_value = peers_notifications_sinks.remove(&(remote, protocol));
						debug_assert!(_previous_value.is_some());
					}
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::NotificationsReceived {
					remote,
					messages,
				})) => {
					if let Some(metrics) = this.metrics.as_ref() {
						for (protocol, message) in &messages {
							metrics
								.notifications_sizes
								.with_label_values(&["in", protocol])
								.observe(message.len() as f64);
						}
					}
					this.event_streams.send(Event::NotificationsReceived { remote, messages });
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::SyncConnected(remote))) => {
					this.event_streams.send(Event::SyncConnected { remote });
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::SyncDisconnected(remote))) => {
					this.event_streams.send(Event::SyncDisconnected { remote });
				},
				Poll::Ready(SwarmEvent::Behaviour(BehaviourOut::Dht(event, duration))) => {
					if let Some(metrics) = this.metrics.as_ref() {
						let query_type = match event {
							DhtEvent::ValueFound(_) => "value-found",
							DhtEvent::ValueNotFound(_) => "value-not-found",
							DhtEvent::ValuePut(_) => "value-put",
							DhtEvent::ValuePutFailed(_) => "value-put-failed",
						};
						metrics
							.kademlia_query_duration
							.with_label_values(&[query_type])
							.observe(duration.as_secs_f64());
					}

					this.event_streams.send(Event::Dht(event));
				},
				Poll::Ready(SwarmEvent::ConnectionEstablished {
					peer_id,
					endpoint,
					num_established,
					concurrent_dial_errors,
				}) => {
					if let Some(errors) = concurrent_dial_errors {
						debug!(target: "sub-libp2p", "Libp2p => Connected({:?}) with errors: {:?}", peer_id, errors);
					} else {
						debug!(target: "sub-libp2p", "Libp2p => Connected({:?})", peer_id);
					}

					if let Some(metrics) = this.metrics.as_ref() {
						let direction = match endpoint {
							ConnectedPoint::Dialer { .. } => "out",
							ConnectedPoint::Listener { .. } => "in",
						};
						metrics.connections_opened_total.with_label_values(&[direction]).inc();

						if num_established.get() == 1 {
							metrics.distinct_peers_connections_opened_total.inc();
						}
					}
				},
				Poll::Ready(SwarmEvent::ConnectionClosed {
					peer_id,
					cause,
					endpoint,
					num_established,
				}) => {
					debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}, {:?})", peer_id, cause);
					if let Some(metrics) = this.metrics.as_ref() {
						let direction = match endpoint {
							ConnectedPoint::Dialer { .. } => "out",
							ConnectedPoint::Listener { .. } => "in",
						};
						let reason = match cause {
							Some(ConnectionError::IO(_)) => "transport-error",
							Some(ConnectionError::Handler(EitherError::A(EitherError::A(
								EitherError::A(EitherError::B(EitherError::A(
									PingFailure::Timeout,
								))),
							)))) => "ping-timeout",
							Some(ConnectionError::Handler(EitherError::A(EitherError::A(
								EitherError::A(EitherError::A(
									NotifsHandlerError::SyncNotificationsClogged,
								)),
							)))) => "sync-notifications-clogged",
							Some(ConnectionError::Handler(_)) => "protocol-error",
							Some(ConnectionError::KeepAliveTimeout) => "keep-alive-timeout",
							None => "actively-closed",
						};
						metrics
							.connections_closed_total
							.with_label_values(&[direction, reason])
							.inc();

						// `num_established` represents the number of *remaining* connections.
						if num_established == 0 {
							metrics.distinct_peers_connections_closed_total.inc();
						}
					}
				},
				Poll::Ready(SwarmEvent::NewListenAddr { address, .. }) => {
					trace!(target: "sub-libp2p", "Libp2p => NewListenAddr({})", address);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.inc();
					}
				},
				Poll::Ready(SwarmEvent::ExpiredListenAddr { address, .. }) => {
					info!(target: "sub-libp2p", "📪 No longer listening on {}", address);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.dec();
					}
				},
				Poll::Ready(SwarmEvent::OutgoingConnectionError { peer_id, error }) => {
					if let Some(peer_id) = peer_id {
						trace!(
							target: "sub-libp2p",
							"Libp2p => Failed to reach {:?}: {}",
							peer_id, error,
						);

						if this.boot_node_ids.contains(&peer_id) {
							if let DialError::WrongPeerId { obtained, endpoint } = &error {
								if let ConnectedPoint::Dialer { address, role_override: _ } =
									endpoint
								{
									warn!(
										"💔 The bootnode you want to connect to at `{}` provided a different peer ID `{}` than the one you expect `{}`.",
										address,
										obtained,
										peer_id,
									);
								}
							}
						}
					}

					if let Some(metrics) = this.metrics.as_ref() {
						let reason = match error {
							DialError::ConnectionLimit(_) => Some("limit-reached"),
							DialError::InvalidPeerId(_) => Some("invalid-peer-id"),
							DialError::Transport(_) | DialError::ConnectionIo(_) =>
								Some("transport-error"),
							DialError::Banned |
							DialError::LocalPeerId |
							DialError::NoAddresses |
							DialError::DialPeerConditionFalse(_) |
							DialError::WrongPeerId { .. } |
							DialError::Aborted => None, // ignore them
						};
						if let Some(reason) = reason {
							metrics
								.pending_connections_errors_total
								.with_label_values(&[reason])
								.inc();
						}
					}
				},
				Poll::Ready(SwarmEvent::Dialing(peer_id)) => {
					trace!(target: "sub-libp2p", "Libp2p => Dialing({:?})", peer_id)
				},
				Poll::Ready(SwarmEvent::IncomingConnection { local_addr, send_back_addr }) => {
					trace!(target: "sub-libp2p", "Libp2p => IncomingConnection({},{}))",
						local_addr, send_back_addr);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.incoming_connections_total.inc();
					}
				},
				Poll::Ready(SwarmEvent::IncomingConnectionError {
					local_addr,
					send_back_addr,
					error,
				}) => {
					debug!(
						target: "sub-libp2p",
						"Libp2p => IncomingConnectionError({},{}): {}",
						local_addr, send_back_addr, error,
					);
					if let Some(metrics) = this.metrics.as_ref() {
						let reason = match error {
							PendingConnectionError::ConnectionLimit(_) => Some("limit-reached"),
							PendingConnectionError::WrongPeerId { .. } => Some("invalid-peer-id"),
							PendingConnectionError::Transport(_) |
							PendingConnectionError::IO(_) => Some("transport-error"),
							PendingConnectionError::Aborted => None, // ignore it
						};

						if let Some(reason) = reason {
							metrics
								.incoming_connections_errors_total
								.with_label_values(&[reason])
								.inc();
						}
					}
				},
				Poll::Ready(SwarmEvent::BannedPeer { peer_id, endpoint }) => {
					debug!(
						target: "sub-libp2p",
						"Libp2p => BannedPeer({}). Connected via {:?}.",
						peer_id, endpoint,
					);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics
							.incoming_connections_errors_total
							.with_label_values(&["banned"])
							.inc();
					}
				},
				Poll::Ready(SwarmEvent::ListenerClosed { reason, addresses, .. }) => {
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_local_addresses.sub(addresses.len() as u64);
					}
					let addrs =
						addresses.into_iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ");
					match reason {
						Ok(()) => error!(
							target: "sub-libp2p",
							"📪 Libp2p listener ({}) closed gracefully",
							addrs
						),
						Err(e) => error!(
							target: "sub-libp2p",
							"📪 Libp2p listener ({}) closed: {}",
							addrs, e
						),
					}
				},
				Poll::Ready(SwarmEvent::ListenerError { error, .. }) => {
					debug!(target: "sub-libp2p", "Libp2p => ListenerError: {}", error);
					if let Some(metrics) = this.metrics.as_ref() {
						metrics.listeners_errors_total.inc();
					}
				},
			};
		}

		let num_connected_peers =
			this.network_service.behaviour_mut().user_protocol_mut().num_connected_peers();

		// Update the variables shared with the `NetworkService`.
		this.num_connected.store(num_connected_peers, Ordering::Relaxed);
		{
			let external_addresses =
				Swarm::<Behaviour<B, Client>>::external_addresses(&this.network_service)
					.map(|r| &r.addr)
					.cloned()
					.collect();
			*this.external_addresses.lock() = external_addresses;
		}

		let is_major_syncing =
			match this.network_service.behaviour_mut().user_protocol_mut().sync_state().state {
				SyncState::Idle => false,
				SyncState::Downloading => true,
			};

		this.tx_handler_controller.set_gossip_enabled(!is_major_syncing);

		this.is_major_syncing.store(is_major_syncing, Ordering::Relaxed);

		if let Some(metrics) = this.metrics.as_ref() {
			for (proto, buckets) in this.network_service.behaviour_mut().num_entries_per_kbucket() {
				for (lower_ilog2_bucket_bound, num_entries) in buckets {
					metrics
						.kbuckets_num_nodes
						.with_label_values(&[proto.as_ref(), &lower_ilog2_bucket_bound.to_string()])
						.set(num_entries as u64);
				}
			}
			for (proto, num_entries) in this.network_service.behaviour_mut().num_kademlia_records()
			{
				metrics
					.kademlia_records_count
					.with_label_values(&[proto.as_ref()])
					.set(num_entries as u64);
			}
			for (proto, num_entries) in
				this.network_service.behaviour_mut().kademlia_records_total_size()
			{
				metrics
					.kademlia_records_sizes_total
					.with_label_values(&[proto.as_ref()])
					.set(num_entries as u64);
			}
			metrics
				.peerset_num_discovered
				.set(this.network_service.behaviour_mut().user_protocol().num_discovered_peers()
					as u64);
			metrics.pending_connections.set(
				Swarm::network_info(&this.network_service).connection_counters().num_pending()
					as u64,
			);
		}

		Poll::Pending
	}
}

impl<B, H, Client> Unpin for NetworkWorker<B, H, Client>
where
	B: BlockT + 'static,
	H: ExHashT,
	Client: HeaderBackend<B> + 'static,
{
}

// Implementation of `import_queue::Link` trait using the available local variables.
struct NetworkLink<'a, B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + 'static,
{
	protocol: &'a mut Swarm<Behaviour<B, Client>>,
}

impl<'a, B, Client> Link<B> for NetworkLink<'a, B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + 'static,
{
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportStatus<NumberFor<B>>, BlockImportError>, B::Hash)>,
	) {
		self.protocol
			.behaviour_mut()
			.user_protocol_mut()
			.on_blocks_processed(imported, count, results)
	}
	fn justification_imported(
		&mut self,
		who: PeerId,
		hash: &B::Hash,
		number: NumberFor<B>,
		success: bool,
	) {
		self.protocol
			.behaviour_mut()
			.user_protocol_mut()
			.justification_import_result(who, *hash, number, success);
	}
	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		self.protocol
			.behaviour_mut()
			.user_protocol_mut()
			.request_justification(hash, number)
	}
}

fn ensure_addresses_consistent_with_transport<'a>(
	addresses: impl Iterator<Item = &'a Multiaddr>,
	transport: &TransportConfig,
) -> Result<(), Error> {
	if matches!(transport, TransportConfig::MemoryOnly) {
		let addresses: Vec<_> = addresses
			.filter(|x| {
				x.iter().any(|y| !matches!(y, libp2p::core::multiaddr::Protocol::Memory(_)))
			})
			.cloned()
			.collect();

		if !addresses.is_empty() {
			return Err(Error::AddressesForAnotherTransport {
				transport: transport.clone(),
				addresses,
			})
		}
	} else {
		let addresses: Vec<_> = addresses
			.filter(|x| x.iter().any(|y| matches!(y, libp2p::core::multiaddr::Protocol::Memory(_))))
			.cloned()
			.collect();

		if !addresses.is_empty() {
			return Err(Error::AddressesForAnotherTransport {
				transport: transport.clone(),
				addresses,
			})
		}
	}

	Ok(())
}
