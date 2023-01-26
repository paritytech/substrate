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

use crate::config;

use bytes::Bytes;
use codec::{Decode, DecodeAll, Encode};
use futures::prelude::*;
use libp2p::{
	core::connection::ConnectionId,
	swarm::{
		behaviour::FromSwarm, ConnectionHandler, IntoConnectionHandler, NetworkBehaviour,
		NetworkBehaviourAction, PollParameters,
	},
	Multiaddr, PeerId,
};
use log::{debug, error, log, trace, warn, Level};
use lru::LruCache;
use message::{generic::Message as GenericMessage, Message};
use notifications::{Notifications, NotificationsOut};
use prometheus_endpoint::{register, Gauge, GaugeVec, Opts, PrometheusError, Registry, U64};
use sc_client_api::HeaderBackend;
use sc_network_common::{
	config::NonReservedPeerMode,
	error,
	protocol::{role::Roles, ProtocolName},
	sync::{
		message::{BlockAnnounce, BlockAnnouncesHandshake, BlockData, BlockResponse, BlockState},
		BadPeer, ChainSync, PollBlockAnnounceValidation, SyncStatus,
	},
	utils::{interval, LruHashSet},
};
use sp_arithmetic::traits::SaturatedConversion;
use sp_runtime::traits::{Block as BlockT, CheckedSub, Header as HeaderT, NumberFor, Zero};
use std::{
	collections::{HashMap, HashSet, VecDeque},
	iter,
	num::NonZeroUsize,
	pin::Pin,
	sync::Arc,
	task::Poll,
	time,
};

mod notifications;

pub mod message;

pub use notifications::{NotificationsSink, NotifsHandlerError, Ready};

/// Interval at which we perform time based maintenance
const TICK_TIMEOUT: time::Duration = time::Duration::from_millis(1100);

/// Maximum number of known block hashes to keep for a peer.
const MAX_KNOWN_BLOCKS: usize = 1024; // ~32kb per peer + LruHashSet overhead

/// Maximum size used for notifications in the block announce and transaction protocols.
// Must be equal to `max(MAX_BLOCK_ANNOUNCE_SIZE, MAX_TRANSACTIONS_SIZE)`.
pub(crate) const BLOCK_ANNOUNCES_TRANSACTIONS_SUBSTREAM_SIZE: u64 = 16 * 1024 * 1024;

/// Identifier of the peerset for the block announces protocol.
const HARDCODED_PEERSETS_SYNC: sc_peerset::SetId = sc_peerset::SetId::from(0);
/// Number of hardcoded peersets (the constants right above). Any set whose identifier is equal or
/// superior to this value corresponds to a user-defined protocol.
const NUM_HARDCODED_PEERSETS: usize = 1;

/// When light node connects to the full node and the full node is behind light node
/// for at least `LIGHT_MAXIMAL_BLOCKS_DIFFERENCE` blocks, we consider it not useful
/// and disconnect to free connection slot.
const LIGHT_MAXIMAL_BLOCKS_DIFFERENCE: u64 = 8192;

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
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
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

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, Client> {
	/// Interval at which we call `tick`.
	tick_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Pending list of messages to return from `poll` as a priority.
	pending_messages: VecDeque<CustomMessageOutcome<B>>,
	/// Assigned roles.
	roles: Roles,
	genesis_hash: B::Hash,
	/// State machine that handles the list of in-progress requests. Only full node peers are
	/// registered.
	chain_sync: Box<dyn ChainSync<B>>,
	// All connected peers. Contains both full and light node peers.
	peers: HashMap<PeerId, Peer<B>>,
	chain: Arc<Client>,
	/// List of nodes for which we perform additional logging because they are important for the
	/// user.
	important_peers: HashSet<PeerId>,
	/// List of nodes that should never occupy peer slots.
	default_peers_set_no_slot_peers: HashSet<PeerId>,
	/// Actual list of connected no-slot nodes.
	default_peers_set_no_slot_connected_peers: HashSet<PeerId>,
	/// Value that was passed as part of the configuration. Used to cap the number of full nodes.
	default_peers_set_num_full: usize,
	/// Number of slots to allocate to light nodes.
	default_peers_set_num_light: usize,
	/// Used to report reputation changes.
	peerset_handle: sc_peerset::PeersetHandle,
	/// Handles opening the unique substream and sending and receiving raw messages.
	behaviour: Notifications,
	/// List of notifications protocols that have been registered.
	notification_protocols: Vec<ProtocolName>,
	/// If we receive a new "substream open" event that contains an invalid handshake, we ask the
	/// inner layer to force-close the substream. Force-closing the substream will generate a
	/// "substream closed" event. This is a problem: since we can't propagate the "substream open"
	/// event to the outer layers, we also shouldn't propagate this "substream closed" event. To
	/// solve this, an entry is added to this map whenever an invalid handshake is received.
	/// Entries are removed when the corresponding "substream closed" is later received.
	bad_handshake_substreams: HashSet<(PeerId, sc_peerset::SetId)>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
	/// The `PeerId`'s of all boot nodes.
	boot_node_ids: HashSet<PeerId>,
	/// A cache for the data that was associated to a block announcement.
	block_announce_data_cache: LruCache<B::Hash, Vec<u8>>,
}

/// Peer information
#[derive(Debug)]
struct Peer<B: BlockT> {
	info: PeerInfo<B>,
	/// Holds a set of blocks known to this peer.
	known_blocks: LruHashSet<B::Hash>,
}

/// Info about a peer's known state.
#[derive(Clone, Debug)]
pub struct PeerInfo<B: BlockT> {
	/// Roles
	pub roles: Roles,
	/// Peer best block hash
	pub best_hash: B::Hash,
	/// Peer best block number
	pub best_number: <B::Header as HeaderT>::Number,
}

impl<B, Client> Protocol<B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + 'static,
{
	/// Create a new instance.
	pub fn new(
		roles: Roles,
		chain: Arc<Client>,
		network_config: &config::NetworkConfiguration,
		metrics_registry: Option<&Registry>,
		chain_sync: Box<dyn ChainSync<B>>,
		block_announces_protocol: sc_network_common::config::NonDefaultSetConfig,
	) -> error::Result<(Self, sc_peerset::PeersetHandle, Vec<(PeerId, Multiaddr)>)> {
		let info = chain.info();

		let boot_node_ids = {
			let mut list = HashSet::new();
			for node in &network_config.boot_nodes {
				list.insert(node.peer_id);
			}
			list.shrink_to_fit();
			list
		};

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

		let mut known_addresses = Vec::new();

		let (peerset, peerset_handle) = {
			let mut sets =
				Vec::with_capacity(NUM_HARDCODED_PEERSETS + network_config.extra_sets.len());

			let mut default_sets_reserved = HashSet::new();
			for reserved in network_config.default_peers_set.reserved_nodes.iter() {
				default_sets_reserved.insert(reserved.peer_id);

				if !reserved.multiaddr.is_empty() {
					known_addresses.push((reserved.peer_id, reserved.multiaddr.clone()));
				}
			}

			let mut bootnodes = Vec::with_capacity(network_config.boot_nodes.len());
			for bootnode in network_config.boot_nodes.iter() {
				bootnodes.push(bootnode.peer_id);
			}

			// Set number 0 is used for block announces.
			sets.push(sc_peerset::SetConfig {
				in_peers: network_config.default_peers_set.in_peers,
				out_peers: network_config.default_peers_set.out_peers,
				bootnodes,
				reserved_nodes: default_sets_reserved.clone(),
				reserved_only: network_config.default_peers_set.non_reserved_mode ==
					NonReservedPeerMode::Deny,
			});

			for set_cfg in &network_config.extra_sets {
				let mut reserved_nodes = HashSet::new();
				for reserved in set_cfg.set_config.reserved_nodes.iter() {
					reserved_nodes.insert(reserved.peer_id);
					known_addresses.push((reserved.peer_id, reserved.multiaddr.clone()));
				}

				let reserved_only =
					set_cfg.set_config.non_reserved_mode == NonReservedPeerMode::Deny;

				sets.push(sc_peerset::SetConfig {
					in_peers: set_cfg.set_config.in_peers,
					out_peers: set_cfg.set_config.out_peers,
					bootnodes: Vec::new(),
					reserved_nodes,
					reserved_only,
				});
			}

			sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig { sets })
		};

		let behaviour = {
			Notifications::new(
				peerset,
				// NOTE: Block announcement protocol is still very much hardcoded into `Protocol`.
				// 	This protocol must be the first notification protocol given to
				// `Notifications`
				iter::once(notifications::ProtocolConfig {
					name: block_announces_protocol.notifications_protocol.clone(),
					fallback_names: block_announces_protocol.fallback_names.clone(),
					handshake: block_announces_protocol.handshake.as_ref().unwrap().to_vec(),
					max_notification_size: block_announces_protocol.max_notification_size,
				})
				.chain(network_config.extra_sets.iter().map(|s| notifications::ProtocolConfig {
					name: s.notifications_protocol.clone(),
					fallback_names: s.fallback_names.clone(),
					handshake: s.handshake.as_ref().map_or(roles.encode(), |h| (*h).to_vec()),
					max_notification_size: s.max_notification_size,
				})),
			)
		};

		let cache_capacity = NonZeroUsize::new(
			(network_config.default_peers_set.in_peers as usize +
				network_config.default_peers_set.out_peers as usize)
				.max(1),
		)
		.expect("cache capacity is not zero");
		let block_announce_data_cache = LruCache::new(cache_capacity);

		let protocol = Self {
			tick_timeout: Box::pin(interval(TICK_TIMEOUT)),
			pending_messages: VecDeque::new(),
			roles,
			peers: HashMap::new(),
			chain,
			genesis_hash: info.genesis_hash,
			chain_sync,
			important_peers,
			default_peers_set_no_slot_peers,
			default_peers_set_no_slot_connected_peers: HashSet::new(),
			default_peers_set_num_full: network_config.default_peers_set_num_full as usize,
			default_peers_set_num_light: {
				let total = network_config.default_peers_set.out_peers +
					network_config.default_peers_set.in_peers;
				total.saturating_sub(network_config.default_peers_set_num_full) as usize
			},
			peerset_handle: peerset_handle.clone(),
			behaviour,
			notification_protocols: iter::once(block_announces_protocol.notifications_protocol)
				.chain(network_config.extra_sets.iter().map(|s| s.notifications_protocol.clone()))
				.collect(),
			bad_handshake_substreams: Default::default(),
			metrics: if let Some(r) = metrics_registry {
				Some(Metrics::register(r)?)
			} else {
				None
			},
			boot_node_ids,
			block_announce_data_cache,
		};

		Ok((protocol, peerset_handle, known_addresses))
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.open_peers()
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.behaviour.num_discovered_peers()
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId, protocol_name: ProtocolName) {
		if let Some(position) = self.notification_protocols.iter().position(|p| *p == protocol_name)
		{
			self.behaviour.disconnect_peer(peer_id, sc_peerset::SetId::from(position));
		} else {
			warn!(target: "sub-libp2p", "disconnect_peer() with invalid protocol name")
		}
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.behaviour.peerset_debug_info()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.peers.len()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.chain_sync.num_active_peers()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncStatus<B> {
		self.chain_sync.status()
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.chain_sync.status().best_seen_block
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.chain_sync.status().num_peers
	}

	/// Number of blocks in the import queue.
	pub fn num_queued_blocks(&self) -> u32 {
		self.chain_sync.status().queued_blocks
	}

	/// Number of downloaded blocks.
	pub fn num_downloaded_blocks(&self) -> usize {
		self.chain_sync.num_downloaded_blocks()
	}

	/// Number of active sync requests.
	pub fn num_sync_requests(&self) -> usize {
		self.chain_sync.num_sync_requests()
	}

	/// Inform sync about new best imported block.
	pub fn new_best_block_imported(&mut self, hash: B::Hash, number: NumberFor<B>) {
		debug!(target: "sync", "New best block imported {:?}/#{}", hash, number);

		self.chain_sync.update_chain_info(&hash, number);

		self.behaviour.set_notif_protocol_handshake(
			HARDCODED_PEERSETS_SYNC,
			BlockAnnouncesHandshake::<B>::build(self.roles, number, hash, self.genesis_hash)
				.encode(),
		);
	}

	fn update_peer_info(&mut self, who: &PeerId) {
		if let Some(info) = self.chain_sync.peer_info(who) {
			if let Some(ref mut peer) = self.peers.get_mut(who) {
				peer.info.best_hash = info.best_hash;
				peer.info.best_number = info.best_number;
			}
		}
	}

	/// Returns information about all the peers we are connected to after the handshake message.
	pub fn peers_info(&self) -> impl Iterator<Item = (&PeerId, &PeerInfo<B>)> {
		self.peers.iter().map(|(id, peer)| (id, &peer.info))
	}

	/// Called by peer when it is disconnecting.
	///
	/// Returns a result if the handshake of this peer was indeed accepted.
	pub fn on_sync_peer_disconnected(&mut self, peer: PeerId) -> Result<(), ()> {
		if self.important_peers.contains(&peer) {
			warn!(target: "sync", "Reserved peer {} disconnected", peer);
		} else {
			debug!(target: "sync", "{} disconnected", peer);
		}

		if let Some(_peer_data) = self.peers.remove(&peer) {
			self.chain_sync.peer_disconnected(&peer);
			self.default_peers_set_no_slot_connected_peers.remove(&peer);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Adjusts the reputation of a node.
	pub fn report_peer(&self, who: PeerId, reputation: sc_peerset::ReputationChange) {
		self.peerset_handle.report_peer(who, reputation)
	}

	/// Perform time based maintenance.
	///
	/// > **Note**: This method normally doesn't have to be called except for testing purposes.
	pub fn tick(&mut self) {
		self.report_metrics()
	}

	/// Called on the first connection between two peers on the default set, after their exchange
	/// of handshake.
	///
	/// Returns `Ok` if the handshake is accepted and the peer added to the list of peers we sync
	/// from.
	fn on_sync_peer_connected(
		&mut self,
		who: PeerId,
		status: BlockAnnouncesHandshake<B>,
	) -> Result<(), ()> {
		trace!(target: "sync", "New peer {} {:?}", who, status);

		if self.peers.contains_key(&who) {
			error!(target: "sync", "Called on_sync_peer_connected with already connected peer {}", who);
			debug_assert!(false);
			return Err(())
		}

		if status.genesis_hash != self.genesis_hash {
			log!(
				target: "sync",
				if self.important_peers.contains(&who) { Level::Warn } else { Level::Debug },
				"Peer is on different chain (our genesis: {} theirs: {})",
				self.genesis_hash, status.genesis_hash
			);
			self.peerset_handle.report_peer(who, rep::GENESIS_MISMATCH);
			self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);

			if self.boot_node_ids.contains(&who) {
				error!(
					target: "sync",
					"Bootnode with peer id `{}` is on a different chain (our genesis: {} theirs: {})",
					who,
					self.genesis_hash,
					status.genesis_hash,
				);
			}

			return Err(())
		}

		if self.roles.is_light() {
			// we're not interested in light peers
			if status.roles.is_light() {
				debug!(target: "sync", "Peer {} is unable to serve light requests", who);
				self.peerset_handle.report_peer(who, rep::BAD_ROLE);
				self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);
				return Err(())
			}

			// we don't interested in peers that are far behind us
			let self_best_block = self.chain.info().best_number;
			let blocks_difference = self_best_block
				.checked_sub(&status.best_number)
				.unwrap_or_else(Zero::zero)
				.saturated_into::<u64>();
			if blocks_difference > LIGHT_MAXIMAL_BLOCKS_DIFFERENCE {
				debug!(target: "sync", "Peer {} is far behind us and will unable to serve light requests", who);
				self.peerset_handle.report_peer(who, rep::PEER_BEHIND_US_LIGHT);
				self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);
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
			debug!(target: "sync", "Too many full nodes, rejecting {}", who);
			self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);
			return Err(())
		}

		if status.roles.is_light() &&
			(self.peers.len() - self.chain_sync.num_peers()) >= self.default_peers_set_num_light
		{
			// Make sure that not all slots are occupied by light clients.
			debug!(target: "sync", "Too many light nodes, rejecting {}", who);
			self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);
			return Err(())
		}

		let peer = Peer {
			info: PeerInfo {
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
					self.behaviour.disconnect_peer(&id, HARDCODED_PEERSETS_SYNC);
					self.peerset_handle.report_peer(id, repu);
					return Err(())
				},
			}
		} else {
			None
		};

		debug!(target: "sync", "Connected {}", who);

		self.peers.insert(who, peer);
		if no_slot_peer {
			self.default_peers_set_no_slot_connected_peers.insert(who);
		}
		self.pending_messages
			.push_back(CustomMessageOutcome::PeerNewBest(who, status.best_number));

		if let Some(req) = req {
			self.chain_sync.send_block_request(who, req);
		}

		Ok(())
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&mut self, hash: B::Hash, data: Option<Vec<u8>>) {
		let header = match self.chain.header(hash) {
			Ok(Some(header)) => header,
			Ok(None) => {
				warn!("Trying to announce unknown block: {}", hash);
				return
			},
			Err(e) => {
				warn!("Error reading block header {}: {}", hash, e);
				return
			},
		};

		// don't announce genesis block since it will be ignored
		if header.number().is_zero() {
			return
		}

		let is_best = self.chain.info().best_hash == hash;
		debug!(target: "sync", "Reannouncing block {:?} is_best: {}", hash, is_best);

		let data = data
			.or_else(|| self.block_announce_data_cache.get(&hash).cloned())
			.unwrap_or_default();

		for (who, ref mut peer) in self.peers.iter_mut() {
			let inserted = peer.known_blocks.insert(hash);
			if inserted {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, who);
				let message = BlockAnnounce {
					header: header.clone(),
					state: if is_best { Some(BlockState::Best) } else { Some(BlockState::Normal) },
					data: Some(data.clone()),
				};

				self.behaviour
					.write_notification(who, HARDCODED_PEERSETS_SYNC, message.encode());
			}
		}
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
	fn push_block_announce_validation(&mut self, who: PeerId, announce: BlockAnnounce<B::Header>) {
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

	/// Process the result of the block announce validation.
	fn process_block_announce_validation_result(
		&mut self,
		validation_result: PollBlockAnnounceValidation<B::Header>,
	) -> CustomMessageOutcome<B> {
		let (header, is_best, who) = match validation_result {
			PollBlockAnnounceValidation::Skip => return CustomMessageOutcome::None,
			PollBlockAnnounceValidation::Nothing { is_best, who, announce } => {
				self.update_peer_info(&who);

				if let Some(data) = announce.data {
					if !data.is_empty() {
						self.block_announce_data_cache.put(announce.header.hash(), data);
					}
				}

				// `on_block_announce` returns `OnBlockAnnounce::ImportHeader`
				// when we have all data required to import the block
				// in the BlockAnnounce message. This is only when:
				// 1) we're on light client;
				// AND
				// 2) parent block is already imported and not pruned.
				if is_best {
					return CustomMessageOutcome::PeerNewBest(who, *announce.header.number())
				} else {
					return CustomMessageOutcome::None
				}
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
					self.behaviour.disconnect_peer(&who, HARDCODED_PEERSETS_SYNC);
				}

				self.report_peer(who, rep::BAD_BLOCK_ANNOUNCEMENT);
				return CustomMessageOutcome::None
			},
		};

		let number = *header.number();

		// to import header from announced block let's construct response to request that normally
		// would have been sent over network (but it is not in our case)
		let blocks_to_import = self.chain_sync.on_block_data(
			&who,
			None,
			BlockResponse::<B> {
				id: 0,
				blocks: vec![BlockData::<B> {
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

		if is_best {
			self.pending_messages.push_back(CustomMessageOutcome::PeerNewBest(who, number));
		}

		CustomMessageOutcome::None
	}

	/// Call this when a block has been finalized. The sync layer may have some additional
	/// requesting to perform.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: &B::Header) {
		self.chain_sync.on_block_finalized(&hash, *header.number())
	}

	/// Set whether the syncing peers set is in reserved-only mode.
	pub fn set_reserved_only(&self, reserved_only: bool) {
		self.peerset_handle.set_reserved_only(HARDCODED_PEERSETS_SYNC, reserved_only);
	}

	/// Removes a `PeerId` from the list of reserved peers for syncing purposes.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.remove_reserved_peer(HARDCODED_PEERSETS_SYNC, peer);
	}

	/// Returns the list of reserved peers.
	pub fn reserved_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.reserved_peers(HARDCODED_PEERSETS_SYNC)
	}

	/// Adds a `PeerId` to the list of reserved peers for syncing purposes.
	pub fn add_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.add_reserved_peer(HARDCODED_PEERSETS_SYNC, peer);
	}

	/// Sets the list of reserved peers for syncing purposes.
	pub fn set_reserved_peers(&self, peers: HashSet<PeerId>) {
		self.peerset_handle.set_reserved_peers(HARDCODED_PEERSETS_SYNC, peers);
	}

	/// Sets the list of reserved peers for the given protocol/peerset.
	pub fn set_reserved_peerset_peers(&self, protocol: ProtocolName, peers: HashSet<PeerId>) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.set_reserved_peers(sc_peerset::SetId::from(index), peers);
		} else {
			error!(
				target: "sub-libp2p",
				"set_reserved_peerset_peers with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_set_reserved_peer(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_reserved_peer(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"remove_set_reserved_peer with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Adds a `PeerId` to the list of reserved peers.
	pub fn add_set_reserved_peer(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_reserved_peer(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"add_set_reserved_peer with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Notify the protocol that we have learned about the existence of nodes on the default set.
	///
	/// Can be called multiple times with the same `PeerId`s.
	pub fn add_default_set_discovered_nodes(&mut self, peer_ids: impl Iterator<Item = PeerId>) {
		for peer_id in peer_ids {
			self.peerset_handle.add_to_peers_set(HARDCODED_PEERSETS_SYNC, peer_id);
		}
	}

	/// Add a peer to a peers set.
	pub fn add_to_peers_set(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_to_peers_set(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"add_to_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Remove a peer from a peers set.
	pub fn remove_from_peers_set(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_from_peers_set(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"remove_from_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}

	fn report_metrics(&self) {
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
}

/// Outcome of an incoming custom message.
#[derive(Debug)]
#[must_use]
pub enum CustomMessageOutcome<B: BlockT> {
	/// Notification protocols have been opened with a remote.
	NotificationStreamOpened {
		remote: PeerId,
		protocol: ProtocolName,
		/// See [`crate::Event::NotificationStreamOpened::negotiated_fallback`].
		negotiated_fallback: Option<ProtocolName>,
		roles: Roles,
		notifications_sink: NotificationsSink,
	},
	/// The [`NotificationsSink`] of some notification protocols need an update.
	NotificationStreamReplaced {
		remote: PeerId,
		protocol: ProtocolName,
		notifications_sink: NotificationsSink,
	},
	/// Notification protocols have been closed with a remote.
	NotificationStreamClosed {
		remote: PeerId,
		protocol: ProtocolName,
	},
	/// Messages have been received on one or more notifications protocols.
	NotificationsReceived {
		remote: PeerId,
		messages: Vec<(ProtocolName, Bytes)>,
	},
	/// Peer has a reported a new head of chain.
	PeerNewBest(PeerId, NumberFor<B>),
	/// Now connected to a new peer for syncing purposes.
	SyncConnected(PeerId),
	/// No longer connected to a peer for syncing purposes.
	SyncDisconnected(PeerId),
	None,
}

impl<B, Client> NetworkBehaviour for Protocol<B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + 'static,
{
	type ConnectionHandler = <Notifications as NetworkBehaviour>::ConnectionHandler;
	type OutEvent = CustomMessageOutcome<B>;

	fn new_handler(&mut self) -> Self::ConnectionHandler {
		self.behaviour.new_handler()
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		// Only `Discovery::addresses_of_peer` must be returning addresses to ensure that we
		// don't return unwanted addresses.
		Vec::new()
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		self.behaviour.on_swarm_event(event);
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: <<Self::ConnectionHandler as IntoConnectionHandler>::Handler as
		ConnectionHandler>::OutEvent,
	) {
		self.behaviour.on_connection_handler_event(peer_id, connection_id, event);
	}

	fn poll(
		&mut self,
		cx: &mut std::task::Context,
		params: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ConnectionHandler>> {
		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message))
		}

		// Advance the state of `ChainSync`
		//
		// Process any received requests received from `NetworkService` and
		// check if there is any block announcement validation finished.
		while let Poll::Ready(result) = self.chain_sync.poll(cx) {
			match self.process_block_announce_validation_result(result) {
				CustomMessageOutcome::None => {},
				outcome => self.pending_messages.push_back(outcome),
			}
		}

		while let Poll::Ready(Some(())) = self.tick_timeout.poll_next_unpin(cx) {
			self.tick();
		}

		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message))
		}

		let event = match self.behaviour.poll(cx, params) {
			Poll::Pending => return Poll::Pending,
			Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev)) => ev,
			Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }) =>
				return Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }),
			Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }) =>
				return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
					peer_id,
					handler,
					event,
				}),
			Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }) =>
				return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }),
			Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }) =>
				return Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }),
		};

		let outcome = match event {
			NotificationsOut::CustomProtocolOpen {
				peer_id,
				set_id,
				received_handshake,
				notifications_sink,
				negotiated_fallback,
			} => {
				// Set number 0 is hardcoded the default set of peers we sync from.
				if set_id == HARDCODED_PEERSETS_SYNC {
					// `received_handshake` can be either a `Status` message if received from the
					// legacy substream ,or a `BlockAnnouncesHandshake` if received from the block
					// announces substream.
					match <Message<B> as DecodeAll>::decode_all(&mut &received_handshake[..]) {
						Ok(GenericMessage::Status(handshake)) => {
							let handshake = BlockAnnouncesHandshake {
								roles: handshake.roles,
								best_number: handshake.best_number,
								best_hash: handshake.best_hash,
								genesis_hash: handshake.genesis_hash,
							};

							if self.on_sync_peer_connected(peer_id, handshake).is_ok() {
								CustomMessageOutcome::SyncConnected(peer_id)
							} else {
								CustomMessageOutcome::None
							}
						},
						Ok(msg) => {
							debug!(
								target: "sync",
								"Expected Status message from {}, but got {:?}",
								peer_id,
								msg,
							);
							self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						},
						Err(err) => {
							match <BlockAnnouncesHandshake<B> as DecodeAll>::decode_all(
								&mut &received_handshake[..],
							) {
								Ok(handshake) => {
									if self.on_sync_peer_connected(peer_id, handshake).is_ok() {
										CustomMessageOutcome::SyncConnected(peer_id)
									} else {
										CustomMessageOutcome::None
									}
								},
								Err(err2) => {
									debug!(
										target: "sync",
										"Couldn't decode handshake sent by {}: {:?}: {} & {}",
										peer_id,
										received_handshake,
										err,
										err2,
									);
									self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
									CustomMessageOutcome::None
								},
							}
						},
					}
				} else {
					match (
						Roles::decode_all(&mut &received_handshake[..]),
						self.peers.get(&peer_id),
					) {
						(Ok(roles), _) => CustomMessageOutcome::NotificationStreamOpened {
							remote: peer_id,
							protocol: self.notification_protocols[usize::from(set_id)].clone(),
							negotiated_fallback,
							roles,
							notifications_sink,
						},
						(Err(_), Some(peer)) if received_handshake.is_empty() => {
							// As a convenience, we allow opening substreams for "external"
							// notification protocols with an empty handshake. This fetches the
							// roles from the locally-known roles.
							// TODO: remove this after https://github.com/paritytech/substrate/issues/5685
							CustomMessageOutcome::NotificationStreamOpened {
								remote: peer_id,
								protocol: self.notification_protocols[usize::from(set_id)].clone(),
								negotiated_fallback,
								roles: peer.info.roles,
								notifications_sink,
							}
						},
						(Err(err), _) => {
							debug!(target: "sync", "Failed to parse remote handshake: {}", err);
							self.bad_handshake_substreams.insert((peer_id, set_id));
							self.behaviour.disconnect_peer(&peer_id, set_id);
							self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						},
					}
				}
			},
			NotificationsOut::CustomProtocolReplaced { peer_id, notifications_sink, set_id } =>
				if set_id == HARDCODED_PEERSETS_SYNC ||
					self.bad_handshake_substreams.contains(&(peer_id, set_id))
				{
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamReplaced {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id)].clone(),
						notifications_sink,
					}
				},
			NotificationsOut::CustomProtocolClosed { peer_id, set_id } => {
				// Set number 0 is hardcoded the default set of peers we sync from.
				if set_id == HARDCODED_PEERSETS_SYNC {
					if self.on_sync_peer_disconnected(peer_id).is_ok() {
						CustomMessageOutcome::SyncDisconnected(peer_id)
					} else {
						log::trace!(
							target: "sync",
							"Disconnected peer which had earlier been refused by on_sync_peer_connected {}",
							peer_id
						);
						CustomMessageOutcome::None
					}
				} else if self.bad_handshake_substreams.remove(&(peer_id, set_id)) {
					// The substream that has just been closed had been opened with a bad
					// handshake. The outer layers have never received an opening event about this
					// substream, and consequently shouldn't receive a closing event either.
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamClosed {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id)].clone(),
					}
				}
			},
			NotificationsOut::Notification { peer_id, set_id, message } => match set_id {
				HARDCODED_PEERSETS_SYNC if self.peers.contains_key(&peer_id) => {
					if let Ok(announce) = BlockAnnounce::decode(&mut message.as_ref()) {
						self.push_block_announce_validation(peer_id, announce);

						// Make sure that the newly added block announce validation future was
						// polled once to be registered in the task.
						if let Poll::Ready(res) = self.chain_sync.poll_block_announce_validation(cx)
						{
							self.process_block_announce_validation_result(res)
						} else {
							CustomMessageOutcome::None
						}
					} else {
						warn!(target: "sub-libp2p", "Failed to decode block announce");
						CustomMessageOutcome::None
					}
				},
				HARDCODED_PEERSETS_SYNC => {
					trace!(
						target: "sync",
						"Received sync for peer earlier refused by sync layer: {}",
						peer_id
					);
					CustomMessageOutcome::None
				},
				_ if self.bad_handshake_substreams.contains(&(peer_id, set_id)) =>
					CustomMessageOutcome::None,
				_ => {
					let protocol_name = self.notification_protocols[usize::from(set_id)].clone();
					CustomMessageOutcome::NotificationsReceived {
						remote: peer_id,
						messages: vec![(protocol_name, message.freeze())],
					}
				},
			},
		};

		if !matches!(outcome, CustomMessageOutcome::<B>::None) {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(outcome))
		}

		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message))
		}

		// This block can only be reached if an event was pulled from the behaviour and that
		// resulted in `CustomMessageOutcome::None`. Since there might be another pending
		// message from the behaviour, the task is scheduled again.
		cx.waker().wake_by_ref();
		Poll::Pending
	}
}
