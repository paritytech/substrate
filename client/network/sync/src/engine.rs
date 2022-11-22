// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{service, ChainSync, ChainSyncInterfaceHandle, ClientError};

use libp2p::PeerId;
use lru::LruCache;
use prometheus_endpoint::{register, Gauge, GaugeVec, Opts, PrometheusError, Registry, U64};

use sc_client_api::{BlockBackend, HeaderBackend, ProofProvider};
use sc_consensus::import_queue::ImportQueueService;
use sc_network_common::{
	config::{NonDefaultSetConfig, ProtocolId},
	protocol::{role::Roles, ProtocolName},
	sync::{
		message::{
			generic::{BlockData, BlockResponse},
			BlockAnnounce, BlockState,
		},
		warp::WarpSyncProvider,
		ChainSync as ChainSyncT, ExtendedPeerInfo, PollBlockAnnounceValidation, SyncMode,
	},
	utils::LruHashSet,
};
use sp_blockchain::HeaderMetadata;
use sp_consensus::block_validation::BlockAnnounceValidator;
use sp_runtime::traits::{Block as BlockT, Header};

use std::{collections::HashMap, num::NonZeroUsize, sync::Arc, task::Poll};

mod rep {
	use sc_peerset::ReputationChange as Rep;
	// /// Reputation change when we are a light client and a peer is behind us.
	// pub const PEER_BEHIND_US_LIGHT: Rep = Rep::new(-(1 << 8), "Useless for a light peer");
	// /// We received a message that failed to decode.
	// pub const BAD_MESSAGE: Rep = Rep::new(-(1 << 12), "Bad message");
	// /// Peer has different genesis.
	// pub const GENESIS_MISMATCH: Rep = Rep::new_fatal("Genesis mismatch");
	// /// Peer role does not match (e.g. light peer connecting to another light peer).
	// pub const BAD_ROLE: Rep = Rep::new_fatal("Unsupported role");
	/// Peer send us a block announcement that failed at validation.
	pub const BAD_BLOCK_ANNOUNCEMENT: Rep = Rep::new(-(1 << 12), "Bad block announcement");
}

struct Metrics {
	_peers: Gauge<U64>,
	queued_blocks: Gauge<U64>,
	fork_targets: Gauge<U64>,
	justifications: GaugeVec<U64>,
}

impl Metrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			_peers: {
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

/// Peer information
#[derive(Debug)]
pub struct Peer<B: BlockT> {
	pub info: ExtendedPeerInfo<B>,
	/// Holds a set of blocks known to this peer.
	pub known_blocks: LruHashSet<B::Hash>,
}

// TODO(aaro): reorder these properly and remove stuff that is not needed
pub struct SyncingEngine<B: BlockT, Client> {
	/// State machine that handles the list of in-progress requests. Only full node peers are
	/// registered.
	pub chain_sync: Box<dyn ChainSyncT<B>>,

	/// Blockchain client.
	_client: Arc<Client>,

	/// Network service.
	network_service: service::network::NetworkServiceHandle,

	// /// Interval at which we call `tick`.
	// tick_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Assigned roles.
	_roles: Roles,
	/// All connected peers. Contains both full and light node peers.
	pub peers: HashMap<PeerId, Peer<B>>,

	/// A cache for the data that was associated to a block announcement.
	pub block_announce_data_cache: LruCache<B::Hash, Vec<u8>>,

	/// Protocol name used for block announcements
	block_announce_protocol_name: ProtocolName,
	// /// List of nodes for which we perform additional logging because they are important for the
	// /// user.
	// important_peers: HashSet<PeerId>,
	// /// List of nodes that should never occupy peer slots.
	// default_peers_set_no_slot_peers: HashSet<PeerId>,
	// /// Actual list of connected no-slot nodes.
	// default_peers_set_no_slot_connected_peers: HashSet<PeerId>,
	// /// Value that was passed as part of the configuration. Used to cap the number of full
	// nodes. default_peers_set_num_full: usize,
	// /// Number of slots to allocate to light nodes.
	// default_peers_set_num_light: usize,
	// /// Used to report reputation changes.
	// peerset_handle: sc_peerset::PeersetHandle,
	// /// Handles opening the unique substream and sending and receiving raw messages.
	// behaviour: Notifications,
	// /// List of notifications protocols that have been registered.
	// notification_protocols: Vec<ProtocolName>,
	// /// If we receive a new "substream open" event that contains an invalid handshake, we ask
	// the /// inner layer to force-close the substream. Force-closing the substream will generate
	// a /// "substream closed" event. This is a problem: since we can't propagate the "substream
	// open" /// event to the outer layers, we also shouldn't propagate this "substream closed"
	// event. To /// solve this, an entry is added to this map whenever an invalid handshake is
	// received. /// Entries are removed when the corresponding "substream closed" is later
	// received. bad_handshake_substreams: HashSet<(PeerId, sc_peerset::SetId)>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
	// /// The `PeerId`'s of all boot nodes.
	// boot_node_ids: HashSet<PeerId>,
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
	// TODO(aaro): clean up these parameters
	pub fn new(
		roles: Roles,
		client: Arc<Client>,
		metrics_registry: Option<&Registry>,
		mode: SyncMode,
		protocol_id: ProtocolId,
		fork_id: &Option<String>,
		block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,
		max_parallel_downloads: u32,
		warp_sync_provider: Option<Arc<dyn WarpSyncProvider<B>>>,
		network_service: service::network::NetworkServiceHandle,
		import_queue: Box<dyn ImportQueueService<B>>,
		block_request_protocol_name: ProtocolName,
		state_request_protocol_name: ProtocolName,
		warp_sync_protocol_name: Option<ProtocolName>,
		cache_capacity: NonZeroUsize,
	) -> Result<(Self, ChainSyncInterfaceHandle<B>, NonDefaultSetConfig), ClientError> {
		let (chain_sync, chain_sync_service, block_announce_config) = ChainSync::new(
			mode,
			client.clone(),
			protocol_id,
			fork_id,
			roles,
			block_announce_validator,
			max_parallel_downloads,
			warp_sync_provider,
			metrics_registry,
			network_service.clone(),
			import_queue,
			block_request_protocol_name,
			state_request_protocol_name,
			warp_sync_protocol_name,
		)?;

		let block_announce_protocol_name = block_announce_config.notifications_protocol.clone();
		Ok((
			Self {
				_roles: roles,
				_client: client,
				chain_sync: Box::new(chain_sync),
				network_service,
				peers: HashMap::new(),
				block_announce_data_cache: LruCache::new(cache_capacity),
				block_announce_protocol_name,
				metrics: if let Some(r) = metrics_registry {
					match Metrics::register(r) {
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
			chain_sync_service,
			block_announce_config,
		))
	}

	/// Report Prometheus metrics.
	pub fn report_metrics(&self) {
		if let Some(metrics) = &self.metrics {
			// TODO(aaro): fix
			// let n = u64::try_from(self.peers.len()).unwrap_or(std::u64::MAX);
			// metrics.peers.set(n);

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

	// TODO: emit peernewbest event?
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
	/// needs to be passed to [`Protocol::process_block_announce_validation_result`]
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

		let is_best = match announce.state.unwrap_or(BlockState::Best) {
			BlockState::Best => true,
			BlockState::Normal => false,
		};

		if peer.info.roles.is_full() {
			self.chain_sync.push_block_announce_validation(who, hash, announce, is_best);
		}
	}

	pub fn poll(&mut self, cx: &mut std::task::Context) {
		while let Poll::Ready(result) = self.chain_sync.poll(cx) {
			self.process_block_announce_validation_result(result);
		}
	}
}
