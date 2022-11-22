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

use prometheus_endpoint::{register, Gauge, GaugeVec, Opts, PrometheusError, Registry, U64};

use sc_network_common::{protocol::role::Roles, sync::ChainSync};
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

pub struct SyncingEngine<B: BlockT, Client> {
	// /// Interval at which we call `tick`.
	// tick_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	// /// Pending list of messages to return from `poll` as a priority.
	// pending_messages: VecDeque<CustomMessageOutcome<B>>,
	/// Assigned roles.
	_roles: Roles,
	/// State machine that handles the list of in-progress requests. Only full node peers are
	/// registered.
	pub chain_sync: Box<dyn ChainSync<B>>,
	// /// All connected peers. Contains both full and light node peers.
	// peers: HashMap<PeerId, Peer<B>>,
	_client: Arc<Client>,
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

impl<B: BlockT, Client> SyncingEngine<B, Client> {
	pub fn new(
		roles: Roles,
		client: Arc<Client>,
		chain_sync: Box<dyn ChainSync<B>>,
		metrics_registry: Option<&Registry>,
	) -> Self {
		Self {
			_roles: roles,
			_client: client,
			chain_sync,
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
		}
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
