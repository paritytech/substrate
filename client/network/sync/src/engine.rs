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

use prometheus_endpoint::{register, Gauge, GaugeVec, Opts, PrometheusError, Registry, U64};

use sc_client_api::{BlockBackend, HeaderBackend, ProofProvider};
use sc_consensus::import_queue::ImportQueueService;
use sc_network_common::{
	config::{NonDefaultSetConfig, ProtocolId},
	protocol::{role::Roles, ProtocolName},
	sync::{warp::WarpSyncProvider, ChainSync as ChainSyncT, SyncMode},
};
use sp_blockchain::HeaderMetadata;
use sp_consensus::block_validation::BlockAnnounceValidator;
use sp_runtime::traits::Block as BlockT;

use std::sync::Arc;

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

// TODO(aaro): reorder these properly and remove stuff that is not needed
pub struct SyncingEngine<B: BlockT, Client> {
	/// State machine that handles the list of in-progress requests. Only full node peers are
	/// registered.
	pub chain_sync: Box<dyn ChainSyncT<B>>,

	/// Blockchain client.
	_client: Arc<Client>,

	/// Network service.
	_network_service: service::network::NetworkServiceHandle,

	// /// Interval at which we call `tick`.
	// tick_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Assigned roles.
	_roles: Roles,
	// /// All connected peers. Contains both full and light node peers.
	// peers: HashMap<PeerId, Peer<B>>,
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
	// /// A cache for the data that was associated to a block announcement.
	// block_announce_data_cache: LruCache<B::Hash, Vec<u8>>,
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

		Ok((
			Self {
				_roles: roles,
				_client: client,
				chain_sync: Box::new(chain_sync),
				_network_service: network_service,
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
}
