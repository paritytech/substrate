// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
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

//! `SyncingEngine` is the actor responsible for syncing Substrate chain
//! to tip and keep the blockchain up to date with network updates.

use crate::{
	service::{self, chain_sync::ToServiceCommand},
	ChainSync, ClientError, SyncingService,
};

use futures::{FutureExt, Stream, StreamExt};
use libp2p::PeerId;
use lru::LruCache;
use prometheus_endpoint::{
	register, Gauge, GaugeVec, MetricSource, Opts, PrometheusError, Registry, SourcedGauge, U64,
};

use codec::{Decode, DecodeAll, Encode};
use futures_timer::Delay;
use sc_client_api::{BlockBackend, HeaderBackend, ProofProvider};
use sc_consensus::import_queue::ImportQueueService;
use sc_network_common::{
	config::{
		NetworkConfiguration, NonDefaultSetConfig, ProtocolId, SyncMode as SyncOperationMode,
	},
	protocol::{event::Event, role::Roles, ProtocolName},
	sync::{
		message::{
			generic::{BlockData, BlockResponse},
			BlockAnnounce, BlockAnnouncesHandshake, BlockState,
		},
		warp::WarpSyncParams,
		BadPeer, ChainSync as ChainSyncT, ExtendedPeerInfo, PollBlockAnnounceValidation, SyncEvent,
		SyncMode,
	},
	utils::LruHashSet,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_blockchain::HeaderMetadata;
use sp_consensus::block_validation::BlockAnnounceValidator;
use sp_runtime::{
	traits::{Block as BlockT, CheckedSub, Header, NumberFor, Zero},
	SaturatedConversion,
};

use std::{
	collections::{HashMap, HashSet},
	num::NonZeroUsize,
	pin::Pin,
	sync::{
		atomic::{AtomicBool, AtomicUsize, Ordering},
		Arc,
	},
	task::Poll,
};

/// Interval at which we perform time based maintenance
const TICK_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(1100);

/// When light node connects to the full node and the full node is behind light node
/// for at least `LIGHT_MAXIMAL_BLOCKS_DIFFERENCE` blocks, we consider it not useful
/// and disconnect to free connection slot.
const LIGHT_MAXIMAL_BLOCKS_DIFFERENCE: u64 = 8192;

/// Maximum number of known block hashes to keep for a peer.
const MAX_KNOWN_BLOCKS: usize = 1024; // ~32kb per peer + LruHashSet overhead

mod rep {
	use sc_peerset::ReputationChange as Rep;
	/// Reputation change when we are a light client and a peer is behind us.
	pub const PEER_BEHIND_US_LIGHT: Rep = Rep::new(-(1 << 8), "Useless for a light peer");
	/// We received a message that failed to decode.
	pub const BAD_MESSAGE: Rep = Rep::new(-(1 << 12), "Bad message");
	/// Peer has different genesis.
	pub const GENESIS_MISMATCH: Rep = Rep::new_fatal("Genesis mismatch");
	/// Peer role does not match (e.g. light peer connecting to another light peer).
	pub const BAD_ROLE: Rep = Rep::new_fatal("Unsupported role");
	/// Peer send us a block announcement that failed at validation.
	pub const BAD_BLOCK_ANNOUNCEMENT: Rep = Rep::new(-(1 << 12), "Bad block announcement");
}

struct Metrics {
	peers: Gauge<U64>,
	queued_blocks: Gauge<U64>,
	fork_targets: Gauge<U64>,
	justifications: GaugeVec<U64>,
}

impl Metrics {
	fn register(r: &Registry, major_syncing: Arc<AtomicBool>) -> Result<Self, PrometheusError> {
		let _ = MajorSyncingGauge::register(r, major_syncing)?;
		Ok(Self {
			peers: {
				let g = Gauge::new("substrate_sync_peers", "Number of peers we sync with")?;
				register(g, r)?
			},
			queued_blocks: {
				let g =
					Gauge::new("substrate_sync_queued_blocks", "Number of blocks in import queue")?;
				register(g, r)?
			},
			fork_targets: {
				let g = Gauge::new("substrate_sync_fork_targets", "Number of fork sync targets")?;
				register(g, r)?
			},
			justifications: {
				let g = GaugeVec::new(
					Opts::new(
						"substrate_sync_extra_justifications",
						"Number of extra justifications requests",
					),
					&["status"],
				)?;
				register(g, r)?
			},
		})
	}
}

/// The "major syncing" metric.
#[derive(Clone)]
pub struct MajorSyncingGauge(Arc<AtomicBool>);

impl MajorSyncingGauge {
	/// Registers the [`MajorSyncGauge`] metric whose value is
	/// obtained from the given `AtomicBool`.
	fn register(registry: &Registry, value: Arc<AtomicBool>) -> Result<(), PrometheusError> {
		prometheus_endpoint::register(
			SourcedGauge::new(
				&Opts::new(
					"substrate_sub_libp2p_is_major_syncing",
					"Whether the node is performing a major sync or not.",
				),
				MajorSyncingGauge(value),
			)?,
			registry,
		)?;

		Ok(())
	}
}

impl MetricSource for MajorSyncingGauge {
	type N = u64;

	fn collect(&self, mut set: impl FnMut(&[&str], Self::N)) {
		set(&[], self.0.load(Ordering::Relaxed) as u64);
	}
}

/// Peer information
#[derive(Debug)]
pub struct Peer<B: BlockT> {
	pub info: ExtendedPeerInfo<B>,
	/// Holds a set of blocks known to this peer.
	pub known_blocks: LruHashSet<B::Hash>,
}

pub struct SyncingEngine<B: BlockT, Client> {
	/// State machine that handles the list of in-progress requests. Only full node peers are
	/// registered.
	chain_sync: ChainSync<B, Client>,

	/// Blockchain client.
	client: Arc<Client>,

	/// Number of peers we're connected to.
	num_connected: Arc<AtomicUsize>,

	/// Are we actively catching up with the chain?
	is_major_syncing: Arc<AtomicBool>,

	/// Network service.
	network_service: service::network::NetworkServiceHandle,

	/// Channel for receiving service commands
	service_rx: TracingUnboundedReceiver<ToServiceCommand<B>>,

	/// Assigned roles.
	roles: Roles,

	/// Genesis hash.
	genesis_hash: B::Hash,

	/// Set of channels for other protocols that have subscribed to syncing events.
	event_streams: Vec<TracingUnboundedSender<SyncEvent>>,

	/// Interval at which we call `tick`.
	tick_timeout: Delay,

	/// All connected peers. Contains both full and light node peers.
	peers: HashMap<PeerId, Peer<B>>,

	/// List of nodes for which we perform additional logging because they are important for the
	/// user.
	important_peers: HashSet<PeerId>,

	/// Actual list of connected no-slot nodes.
	default_peers_set_no_slot_connected_peers: HashSet<PeerId>,

	/// List of nodes that should never occupy peer slots.
	default_peers_set_no_slot_peers: HashSet<PeerId>,

	/// Value that was passed as part of the configuration. Used to cap the number of full
	/// nodes.
	default_peers_set_num_full: usize,

	/// Number of slots to allocate to light nodes.
	default_peers_set_num_light: usize,

	/// A cache for the data that was associated to a block announcement.
	block_announce_data_cache: LruCache<B::Hash, Vec<u8>>,

	/// The `PeerId`'s of all boot nodes.
	boot_node_ids: HashSet<PeerId>,

	/// Protocol name used for block announcements
	block_announce_protocol_name: ProtocolName,

	/// Prometheus metrics.
	metrics: Option<Metrics>,
}

impl<B: BlockT, Client> SyncingEngine<B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B>
		+ BlockBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ ProofProvider<B>
		+ Send
		+ Sync
		+ 'static,
{
	pub fn new(
		roles: Roles,
		client: Arc<Client>,
		metrics_registry: Option<&Registry>,
		network_config: &NetworkConfiguration,
		protocol_id: ProtocolId,
		fork_id: &Option<String>,
		block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,
		warp_sync_params: Option<WarpSyncParams<B>>,
		network_service: service::network::NetworkServiceHandle,
		import_queue: Box<dyn ImportQueueService<B>>,
		block_request_protocol_name: ProtocolName,
		state_request_protocol_name: ProtocolName,
		warp_sync_protocol_name: Option<ProtocolName>,
	) -> Result<(Self, SyncingService<B>, NonDefaultSetConfig), ClientError> {
		let mode = match network_config.sync_mode {
			SyncOperationMode::Full => SyncMode::Full,
			SyncOperationMode::Fast { skip_proofs, storage_chain_mode } =>
				SyncMode::LightState { skip_proofs, storage_chain_mode },
			SyncOperationMode::Warp => SyncMode::Warp,
		};
		let max_parallel_downloads = network_config.max_parallel_downloads;
		let cache_capacity = NonZeroUsize::new(
			(network_config.default_peers_set.in_peers as usize +
				network_config.default_peers_set.out_peers as usize)
				.max(1),
		)
		.expect("cache capacity is not zero");
		let important_peers = {
			let mut imp_p = HashSet::new();
			for reserved in &network_config.default_peers_set.reserved_nodes {
				imp_p.insert(reserved.peer_id);
			}
			for reserved in network_config
				.extra_sets
				.iter()
				.flat_map(|s| s.set_config.reserved_nodes.iter())
			{
				imp_p.insert(reserved.peer_id);
			}
			imp_p.shrink_to_fit();
			imp_p
		};
		let boot_node_ids = {
			let mut list = HashSet::new();
			for node in &network_config.boot_nodes {
				list.insert(node.peer_id);
			}
			list.shrink_to_fit();
			list
		};
		let default_peers_set_no_slot_peers = {
			let mut no_slot_p: HashSet<PeerId> = network_config
				.default_peers_set
				.reserved_nodes
				.iter()
				.map(|reserved| reserved.peer_id)
				.collect();
			no_slot_p.shrink_to_fit();
			no_slot_p
		};
		let default_peers_set_num_full = network_config.default_peers_set_num_full as usize;
		let default_peers_set_num_light = {
			let total = network_config.default_peers_set.out_peers +
				network_config.default_peers_set.in_peers;
			total.saturating_sub(network_config.default_peers_set_num_full) as usize
		};

		let (chain_sync, block_announce_config) = ChainSync::new(
			mode,
			client.clone(),
			protocol_id,
			fork_id,
			roles,
			block_announce_validator,
			max_parallel_downloads,
			warp_sync_params,
			metrics_registry,
			network_service.clone(),
			import_queue,
			block_request_protocol_name,
			state_request_protocol_name,
			warp_sync_protocol_name,
		)?;

		let block_announce_protocol_name = block_announce_config.notifications_protocol.clone();
		let (tx, service_rx) = tracing_unbounded("mpsc_chain_sync", 100_000);
		let num_connected = Arc::new(AtomicUsize::new(0));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let genesis_hash = client
			.block_hash(0u32.into())
			.ok()
			.flatten()
			.expect("Genesis block exists; qed");

		Ok((
			Self {
				roles,
				client,
				chain_sync,
				network_service,
				peers: HashMap::new(),
				block_announce_data_cache: LruCache::new(cache_capacity),
				block_announce_protocol_name,
				num_connected: num_connected.clone(),
				is_major_syncing: is_major_syncing.clone(),
				service_rx,
				genesis_hash,
				important_peers,
				default_peers_set_no_slot_connected_peers: HashSet::new(),
				boot_node_ids,
				default_peers_set_no_slot_peers,
				default_peers_set_num_full,
				default_peers_set_num_light,
				event_streams: Vec::new(),
				tick_timeout: Delay::new(TICK_TIMEOUT),
				metrics: if let Some(r) = metrics_registry {
					match Metrics::register(r, is_major_syncing.clone()) {
						Ok(metrics) => Some(metrics),
						Err(err) => {
							log::error!(target: "sync", "Failed to register metrics {err:?}");
							None
						},
					}
				} else {
					None
				},
			},
			SyncingService::new(tx, num_connected, is_major_syncing),
			block_announce_config,
		))
	}

	/// Report Prometheus metrics.
	pub fn report_metrics(&self) {
		if let Some(metrics) = &self.metrics {
			let n = u64::try_from(self.peers.len()).unwrap_or(std::u64::MAX);
			metrics.peers.set(n);

			let m = self.chain_sync.metrics();

			metrics.fork_targets.set(m.fork_targets.into());
			metrics.queued_blocks.set(m.queued_blocks.into());

			metrics
				.justifications
				.with_label_values(&["pending"])
				.set(m.justifications.pending_requests.into());
			metrics
				.justifications
				.with_label_values(&["active"])
				.set(m.justifications.active_requests.into());
			metrics
				.justifications
				.with_label_values(&["failed"])
				.set(m.justifications.failed_requests.into());
			metrics
				.justifications
				.with_label_values(&["importing"])
				.set(m.justifications.importing_requests.into());
		}
	}

	fn update_peer_info(&mut self, who: &PeerId) {
		if let Some(info) = self.chain_sync.peer_info(who) {
			if let Some(ref mut peer) = self.peers.get_mut(who) {
				peer.info.best_hash = info.best_hash;
				peer.info.best_number = info.best_number;
			}
		}
	}

	/// Process the result of the block announce validation.
	pub fn process_block_announce_validation_result(
		&mut self,
		validation_result: PollBlockAnnounceValidation<B::Header>,
	) {
		let (header, _is_best, who) = match validation_result {
			PollBlockAnnounceValidation::Skip => return,
			PollBlockAnnounceValidation::Nothing { is_best: _, who, announce } => {
				self.update_peer_info(&who);

				if let Some(data) = announce.data {
					if !data.is_empty() {
						self.block_announce_data_cache.put(announce.header.hash(), data);
					}
				}

				return
			},
			PollBlockAnnounceValidation::ImportHeader { announce, is_best, who } => {
				self.update_peer_info(&who);

				if let Some(data) = announce.data {
					if !data.is_empty() {
						self.block_announce_data_cache.put(announce.header.hash(), data);
					}
				}

				(announce.header, is_best, who)
			},
			PollBlockAnnounceValidation::Failure { who, disconnect } => {
				if disconnect {
					self.network_service
						.disconnect_peer(who, self.block_announce_protocol_name.clone());
				}

				self.network_service.report_peer(who, rep::BAD_BLOCK_ANNOUNCEMENT);
				return
			},
		};

		// to import header from announced block let's construct response to request that normally
		// would have been sent over network (but it is not in our case)
		let blocks_to_import = self.chain_sync.on_block_data(
			&who,
			None,
			BlockResponse {
				id: 0,
				blocks: vec![BlockData {
					hash: header.hash(),
					header: Some(header),
					body: None,
					indexed_body: None,
					receipt: None,
					message_queue: None,
					justification: None,
					justifications: None,
				}],
			},
		);

		self.chain_sync.process_block_response_data(blocks_to_import);
	}

	/// Push a block announce validation.
	///
	/// It is required that [`ChainSync::poll_block_announce_validation`] is
	/// called later to check for finished validations. The result of the validation
	/// needs to be passed to [`SyncingEngine::process_block_announce_validation_result`]
	/// to finish the processing.
	///
	/// # Note
	///
	/// This will internally create a future, but this future will not be registered
	/// in the task before being polled once. So, it is required to call
	/// [`ChainSync::poll_block_announce_validation`] to ensure that the future is
	/// registered properly and will wake up the task when being ready.
	pub fn push_block_announce_validation(
		&mut self,
		who: PeerId,
		announce: BlockAnnounce<B::Header>,
	) {
		let hash = announce.header.hash();

		let peer = match self.peers.get_mut(&who) {
			Some(p) => p,
			None => {
				log::error!(target: "sync", "Received block announce from disconnected peer {}", who);
				debug_assert!(false);
				return
			},
		};
		peer.known_blocks.insert(hash);

		if peer.info.roles.is_full() {
			let is_best = match announce.state.unwrap_or(BlockState::Best) {
				BlockState::Best => true,
				BlockState::Normal => false,
			};

			self.chain_sync.push_block_announce_validation(who, hash, announce, is_best);
		}
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&mut self, hash: B::Hash, data: Option<Vec<u8>>) {
		let header = match self.client.header(hash) {
			Ok(Some(header)) => header,
			Ok(None) => {
				log::warn!(target: "sync", "Trying to announce unknown block: {}", hash);
				return
			},
			Err(e) => {
				log::warn!(target: "sync", "Error reading block header {}: {}", hash, e);
				return
			},
		};

		// don't announce genesis block since it will be ignored
		if header.number().is_zero() {
			return
		}

		let is_best = self.client.info().best_hash == hash;
		log::debug!(target: "sync", "Reannouncing block {:?} is_best: {}", hash, is_best);

		let data = data
			.or_else(|| self.block_announce_data_cache.get(&hash).cloned())
			.unwrap_or_default();

		for (who, ref mut peer) in self.peers.iter_mut() {
			let inserted = peer.known_blocks.insert(hash);
			if inserted {
				log::trace!(target: "sync", "Announcing block {:?} to {}", hash, who);
				let message = BlockAnnounce {
					header: header.clone(),
					state: if is_best { Some(BlockState::Best) } else { Some(BlockState::Normal) },
					data: Some(data.clone()),
				};

				self.network_service.write_notification(
					*who,
					self.block_announce_protocol_name.clone(),
					message.encode(),
				);
			}
		}
	}

	/// Inform sync about new best imported block.
	pub fn new_best_block_imported(&mut self, hash: B::Hash, number: NumberFor<B>) {
		log::debug!(target: "sync", "New best block imported {:?}/#{}", hash, number);

		self.chain_sync.update_chain_info(&hash, number);
		self.network_service.set_notification_handshake(
			self.block_announce_protocol_name.clone(),
			BlockAnnouncesHandshake::<B>::build(self.roles, number, hash, self.genesis_hash)
				.encode(),
		)
	}

	pub async fn run(mut self, mut stream: Pin<Box<dyn Stream<Item = Event> + Send>>) {
		loop {
			futures::future::poll_fn(|cx| self.poll(cx, &mut stream)).await;
		}
	}

	pub fn poll(
		&mut self,
		cx: &mut std::task::Context,
		event_stream: &mut Pin<Box<dyn Stream<Item = Event> + Send>>,
	) -> Poll<()> {
		self.num_connected.store(self.peers.len(), Ordering::Relaxed);
		self.is_major_syncing
			.store(self.chain_sync.status().state.is_major_syncing(), Ordering::Relaxed);

		while let Poll::Ready(()) = self.tick_timeout.poll_unpin(cx) {
			self.report_metrics();
			self.tick_timeout.reset(TICK_TIMEOUT);
		}

		while let Poll::Ready(Some(event)) = event_stream.poll_next_unpin(cx) {
			match event {
				Event::NotificationStreamOpened {
					remote, protocol, received_handshake, ..
				} => {
					if protocol != self.block_announce_protocol_name {
						continue
					}

					match <BlockAnnouncesHandshake<B> as DecodeAll>::decode_all(
						&mut &received_handshake[..],
					) {
						Ok(handshake) => {
							if self.on_sync_peer_connected(remote, handshake).is_err() {
								log::debug!(
									target: "sync",
									"Failed to register peer {remote:?}: {received_handshake:?}",
								);
							}
						},
						Err(err) => {
							log::debug!(
								target: "sync",
								"Couldn't decode handshake sent by {}: {:?}: {}",
								remote,
								received_handshake,
								err,
							);
							self.network_service.report_peer(remote, rep::BAD_MESSAGE);
						},
					}
				},
				Event::NotificationStreamClosed { remote, protocol } => {
					if protocol != self.block_announce_protocol_name {
						continue
					}

					if self.on_sync_peer_disconnected(remote).is_err() {
						log::trace!(
							target: "sync",
							"Disconnected peer which had earlier been refused by on_sync_peer_connected {}",
							remote
						);
					}
				},
				Event::NotificationsReceived { remote, messages } => {
					for (protocol, message) in messages {
						if protocol != self.block_announce_protocol_name {
							continue
						}

						if self.peers.contains_key(&remote) {
							if let Ok(announce) = BlockAnnounce::decode(&mut message.as_ref()) {
								self.push_block_announce_validation(remote, announce);

								// Make sure that the newly added block announce validation future
								// was polled once to be registered in the task.
								if let Poll::Ready(res) =
									self.chain_sync.poll_block_announce_validation(cx)
								{
									self.process_block_announce_validation_result(res)
								}
							} else {
								log::warn!(target: "sub-libp2p", "Failed to decode block announce");
							}
						} else {
							log::trace!(
								target: "sync",
								"Received sync for peer earlier refused by sync layer: {}",
								remote
							);
						}
					}
				},
				_ => {},
			}
		}

		while let Poll::Ready(Some(event)) = self.service_rx.poll_next_unpin(cx) {
			match event {
				ToServiceCommand::SetSyncForkRequest(peers, hash, number) => {
					self.chain_sync.set_sync_fork_request(peers, &hash, number);
				},
				ToServiceCommand::EventStream(tx) => self.event_streams.push(tx),
				ToServiceCommand::RequestJustification(hash, number) =>
					self.chain_sync.request_justification(&hash, number),
				ToServiceCommand::ClearJustificationRequests =>
					self.chain_sync.clear_justification_requests(),
				ToServiceCommand::BlocksProcessed(imported, count, results) => {
					for result in self.chain_sync.on_blocks_processed(imported, count, results) {
						match result {
							Ok((id, req)) => self.chain_sync.send_block_request(id, req),
							Err(BadPeer(id, repu)) => {
								self.network_service
									.disconnect_peer(id, self.block_announce_protocol_name.clone());
								self.network_service.report_peer(id, repu)
							},
						}
					}
				},
				ToServiceCommand::JustificationImported(peer, hash, number, success) => {
					self.chain_sync.on_justification_import(hash, number, success);
					if !success {
						log::info!(target: "sync", "💔 Invalid justification provided by {} for #{}", peer, hash);
						self.network_service
							.disconnect_peer(peer, self.block_announce_protocol_name.clone());
						self.network_service.report_peer(
							peer,
							sc_peerset::ReputationChange::new_fatal("Invalid justification"),
						);
					}
				},
				ToServiceCommand::AnnounceBlock(hash, data) => self.announce_block(hash, data),
				ToServiceCommand::NewBestBlockImported(hash, number) =>
					self.new_best_block_imported(hash, number),
				ToServiceCommand::Status(tx) => {
					let _ = tx.send(self.chain_sync.status());
				},
				ToServiceCommand::NumActivePeers(tx) => {
					let _ = tx.send(self.chain_sync.num_active_peers());
				},
				ToServiceCommand::SyncState(tx) => {
					let _ = tx.send(self.chain_sync.status());
				},
				ToServiceCommand::BestSeenBlock(tx) => {
					let _ = tx.send(self.chain_sync.status().best_seen_block);
				},
				ToServiceCommand::NumSyncPeers(tx) => {
					let _ = tx.send(self.chain_sync.status().num_peers);
				},
				ToServiceCommand::NumQueuedBlocks(tx) => {
					let _ = tx.send(self.chain_sync.status().queued_blocks);
				},
				ToServiceCommand::NumDownloadedBlocks(tx) => {
					let _ = tx.send(self.chain_sync.num_downloaded_blocks());
				},
				ToServiceCommand::NumSyncRequests(tx) => {
					let _ = tx.send(self.chain_sync.num_sync_requests());
				},
				ToServiceCommand::PeersInfo(tx) => {
					let peers_info =
						self.peers.iter().map(|(id, peer)| (*id, peer.info.clone())).collect();
					let _ = tx.send(peers_info);
				},
				ToServiceCommand::OnBlockFinalized(hash, header) =>
					self.chain_sync.on_block_finalized(&hash, *header.number()),
			}
		}

		while let Poll::Ready(result) = self.chain_sync.poll(cx) {
			self.process_block_announce_validation_result(result);
		}

		Poll::Pending
	}

	/// Called by peer when it is disconnecting.
	///
	/// Returns a result if the handshake of this peer was indeed accepted.
	pub fn on_sync_peer_disconnected(&mut self, peer: PeerId) -> Result<(), ()> {
		if self.important_peers.contains(&peer) {
			log::warn!(target: "sync", "Reserved peer {} disconnected", peer);
		} else {
			log::debug!(target: "sync", "{} disconnected", peer);
		}

		if self.peers.remove(&peer).is_some() {
			self.chain_sync.peer_disconnected(&peer);
			self.default_peers_set_no_slot_connected_peers.remove(&peer);
			self.event_streams
				.retain(|stream| stream.unbounded_send(SyncEvent::PeerDisconnected(peer)).is_ok());
			Ok(())
		} else {
			Err(())
		}
	}

	/// Called on the first connection between two peers on the default set, after their exchange
	/// of handshake.
	///
	/// Returns `Ok` if the handshake is accepted and the peer added to the list of peers we sync
	/// from.
	pub fn on_sync_peer_connected(
		&mut self,
		who: PeerId,
		status: BlockAnnouncesHandshake<B>,
	) -> Result<(), ()> {
		log::trace!(target: "sync", "New peer {} {:?}", who, status);

		if self.peers.contains_key(&who) {
			log::error!(target: "sync", "Called on_sync_peer_connected with already connected peer {}", who);
			debug_assert!(false);
			return Err(())
		}

		if status.genesis_hash != self.genesis_hash {
			self.network_service.report_peer(who, rep::GENESIS_MISMATCH);
			self.network_service
				.disconnect_peer(who, self.block_announce_protocol_name.clone());

			if self.important_peers.contains(&who) {
				log::error!(
					target: "sync",
					"Reserved peer id `{}` is on a different chain (our genesis: {} theirs: {})",
					who,
					self.genesis_hash,
					status.genesis_hash,
				);
			} else if self.boot_node_ids.contains(&who) {
				log::error!(
					target: "sync",
					"Bootnode with peer id `{}` is on a different chain (our genesis: {} theirs: {})",
					who,
					self.genesis_hash,
					status.genesis_hash,
				);
			} else {
				log::debug!(
					target: "sync",
					"Peer is on different chain (our genesis: {} theirs: {})",
					self.genesis_hash, status.genesis_hash
				);
			}

			return Err(())
		}

		if self.roles.is_light() {
			// we're not interested in light peers
			if status.roles.is_light() {
				log::debug!(target: "sync", "Peer {} is unable to serve light requests", who);
				self.network_service.report_peer(who, rep::BAD_ROLE);
				self.network_service
					.disconnect_peer(who, self.block_announce_protocol_name.clone());
				return Err(())
			}

			// we don't interested in peers that are far behind us
			let self_best_block = self.client.info().best_number;
			let blocks_difference = self_best_block
				.checked_sub(&status.best_number)
				.unwrap_or_else(Zero::zero)
				.saturated_into::<u64>();
			if blocks_difference > LIGHT_MAXIMAL_BLOCKS_DIFFERENCE {
				log::debug!(target: "sync", "Peer {} is far behind us and will unable to serve light requests", who);
				self.network_service.report_peer(who, rep::PEER_BEHIND_US_LIGHT);
				self.network_service
					.disconnect_peer(who, self.block_announce_protocol_name.clone());
				return Err(())
			}
		}

		let no_slot_peer = self.default_peers_set_no_slot_peers.contains(&who);
		let this_peer_reserved_slot: usize = if no_slot_peer { 1 } else { 0 };

		if status.roles.is_full() &&
			self.chain_sync.num_peers() >=
				self.default_peers_set_num_full +
					self.default_peers_set_no_slot_connected_peers.len() +
					this_peer_reserved_slot
		{
			log::debug!(target: "sync", "Too many full nodes, rejecting {}", who);
			self.network_service
				.disconnect_peer(who, self.block_announce_protocol_name.clone());
			return Err(())
		}

		if status.roles.is_light() &&
			(self.peers.len() - self.chain_sync.num_peers()) >= self.default_peers_set_num_light
		{
			// Make sure that not all slots are occupied by light clients.
			log::debug!(target: "sync", "Too many light nodes, rejecting {}", who);
			self.network_service
				.disconnect_peer(who, self.block_announce_protocol_name.clone());
			return Err(())
		}

		let peer = Peer {
			info: ExtendedPeerInfo {
				roles: status.roles,
				best_hash: status.best_hash,
				best_number: status.best_number,
			},
			known_blocks: LruHashSet::new(
				NonZeroUsize::new(MAX_KNOWN_BLOCKS).expect("Constant is nonzero"),
			),
		};

		let req = if peer.info.roles.is_full() {
			match self.chain_sync.new_peer(who, peer.info.best_hash, peer.info.best_number) {
				Ok(req) => req,
				Err(BadPeer(id, repu)) => {
					self.network_service
						.disconnect_peer(id, self.block_announce_protocol_name.clone());
					self.network_service.report_peer(id, repu);
					return Err(())
				},
			}
		} else {
			None
		};

		log::debug!(target: "sync", "Connected {}", who);

		self.peers.insert(who, peer);
		if no_slot_peer {
			self.default_peers_set_no_slot_connected_peers.insert(who);
		}

		if let Some(req) = req {
			self.chain_sync.send_block_request(who, req);
		}

		self.event_streams
			.retain(|stream| stream.unbounded_send(SyncEvent::PeerConnected(who)).is_ok());

		Ok(())
	}
}
