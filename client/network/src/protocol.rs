// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::{
	ExHashT,
	chain::Client,
	config::{self, ProtocolId, TransactionPool, TransactionImportFuture, TransactionImport},
	error,
	utils::{interval, LruHashSet},
};

use bytes::{Bytes, BytesMut};
use futures::{prelude::*, stream::FuturesUnordered};
use generic_proto::{GenericProto, GenericProtoOut};
use libp2p::{Multiaddr, PeerId};
use libp2p::core::{ConnectedPoint, connection::{ConnectionId, ListenerId}};
use libp2p::swarm::{ProtocolsHandler, IntoProtocolsHandler};
use libp2p::swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use sp_consensus::{
	BlockOrigin,
	block_validation::BlockAnnounceValidator,
	import_queue::{BlockImportResult, BlockImportError, IncomingBlock, Origin}
};
use codec::{Decode, DecodeAll, Encode};
use sp_runtime::{generic::BlockId, Justification};
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, CheckedSub
};
use sp_arithmetic::traits::SaturatedConversion;
use message::{BlockAnnounce, Message};
use message::generic::{Message as GenericMessage, Roles};
use prometheus_endpoint::{
	Registry, Gauge, Counter, GaugeVec,
	PrometheusError, Opts, register, U64
};
use sync::{ChainSync, SyncState};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet, VecDeque, hash_map::Entry};
use std::sync::Arc;
use std::fmt::Write;
use std::{io, iter, num::NonZeroUsize, pin::Pin, task::Poll, time};
use log::{log, Level, trace, debug, warn, error};
use wasm_timer::Instant;

mod generic_proto;

pub mod message;
pub mod event;
pub mod sync;

pub use generic_proto::{NotificationsSink, Ready, NotifsHandlerError};

const REQUEST_TIMEOUT_SEC: u64 = 40;
/// Interval at which we perform time based maintenance
const TICK_TIMEOUT: time::Duration = time::Duration::from_millis(1100);
/// Interval at which we propagate transactions;
const PROPAGATE_TIMEOUT: time::Duration = time::Duration::from_millis(2900);

/// Maximim number of known block hashes to keep for a peer.
const MAX_KNOWN_BLOCKS: usize = 1024; // ~32kb per peer + LruHashSet overhead
/// Maximim number of known transaction hashes to keep for a peer.
///
/// This should be approx. 2 blocks full of transactions for the network to function properly.
const MAX_KNOWN_TRANSACTIONS: usize = 10240; // ~300kb per peer + overhead.

/// Maximim number of transaction validation request we keep at any moment.
const MAX_PENDING_TRANSACTIONS: usize = 8192;

/// Current protocol version.
pub(crate) const CURRENT_VERSION: u32 = 6;
/// Lowest version we support
pub(crate) const MIN_VERSION: u32 = 3;

/// When light node connects to the full node and the full node is behind light node
/// for at least `LIGHT_MAXIMAL_BLOCKS_DIFFERENCE` blocks, we consider it not useful
/// and disconnect to free connection slot.
const LIGHT_MAXIMAL_BLOCKS_DIFFERENCE: u64 = 8192;

mod rep {
	use sc_peerset::ReputationChange as Rep;
	/// Reputation change when a peer doesn't respond in time to our messages.
	pub const TIMEOUT: Rep = Rep::new(-(1 << 10), "Request timeout");
	/// Reputation change when we are a light client and a peer is behind us.
	pub const PEER_BEHIND_US_LIGHT: Rep = Rep::new(-(1 << 8), "Useless for a light peer");
	/// Reputation change when a peer sends us any transaction.
	///
	/// This forces node to verify it, thus the negative value here. Once transaction is verified,
	/// reputation change should be refunded with `ANY_TRANSACTION_REFUND`
	pub const ANY_TRANSACTION: Rep = Rep::new(-(1 << 4), "Any transaction");
	/// Reputation change when a peer sends us any transaction that is not invalid.
	pub const ANY_TRANSACTION_REFUND: Rep = Rep::new(1 << 4, "Any transaction (refund)");
	/// Reputation change when a peer sends us an transaction that we didn't know about.
	pub const GOOD_TRANSACTION: Rep = Rep::new(1 << 7, "Good transaction");
	/// Reputation change when a peer sends us a bad transaction.
	pub const BAD_TRANSACTION: Rep = Rep::new(-(1 << 12), "Bad transaction");
	/// We received a message that failed to decode.
	pub const BAD_MESSAGE: Rep = Rep::new(-(1 << 12), "Bad message");
	/// We received an unexpected response.
	pub const UNEXPECTED_RESPONSE: Rep = Rep::new_fatal("Unexpected response packet");
	/// We received an unexpected transaction packet.
	pub const UNEXPECTED_TRANSACTIONS: Rep = Rep::new_fatal("Unexpected transactions packet");
	/// Peer has different genesis.
	pub const GENESIS_MISMATCH: Rep = Rep::new_fatal("Genesis mismatch");
	/// Peer is on unsupported protocol version.
	pub const BAD_PROTOCOL: Rep = Rep::new_fatal("Unsupported protocol");
	/// Peer role does not match (e.g. light peer connecting to another light peer).
	pub const BAD_ROLE: Rep = Rep::new_fatal("Unsupported role");
	/// Peer send us a block announcement that failed at validation.
	pub const BAD_BLOCK_ANNOUNCEMENT: Rep = Rep::new(-(1 << 12), "Bad block announcement");
}

struct Metrics {
	obsolete_requests: Gauge<U64>,
	peers: Gauge<U64>,
	queued_blocks: Gauge<U64>,
	fork_targets: Gauge<U64>,
	justifications: GaugeVec<U64>,
	propagated_transactions: Counter<U64>,
}

impl Metrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(Metrics {
			obsolete_requests: {
				let g = Gauge::new("sync_obsolete_requests", "Number of obsolete requests")?;
				register(g, r)?
			},
			peers: {
				let g = Gauge::new("sync_peers", "Number of peers we sync with")?;
				register(g, r)?
			},
			queued_blocks: {
				let g = Gauge::new("sync_queued_blocks", "Number of blocks in import queue")?;
				register(g, r)?
			},
			fork_targets: {
				let g = Gauge::new("sync_fork_targets", "Number of fork sync targets")?;
				register(g, r)?
			},
			justifications: {
				let g = GaugeVec::new(
					Opts::new(
						"sync_extra_justifications",
						"Number of extra justifications requests"
					),
					&["status"],
				)?;
				register(g, r)?
			},
			propagated_transactions: register(Counter::new(
				"sync_propagated_transactions",
				"Number of transactions propagated to at least one peer",
			)?, r)?,
		})
	}
}

#[pin_project::pin_project]
struct PendingTransaction<H> {
	#[pin]
	validation: TransactionImportFuture,
	tx_hash: H,
}

impl<H: ExHashT> Future for PendingTransaction<H> {
	type Output = (H, TransactionImport);

	fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
		let mut this = self.project();

		if let Poll::Ready(import_result) = Pin::new(&mut this.validation).poll_unpin(cx) {
			return Poll::Ready((this.tx_hash.clone(), import_result));
		}

		Poll::Pending
	}
}

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, H: ExHashT> {
	/// Interval at which we call `tick`.
	tick_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Interval at which we call `propagate_transactions`.
	propagate_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Pending list of messages to return from `poll` as a priority.
	pending_messages: VecDeque<CustomMessageOutcome<B>>,
	/// Pending transactions verification tasks.
	pending_transactions: FuturesUnordered<PendingTransaction<H>>,
	/// As multiple peers can send us the same transaction, we group
	/// these peers using the transaction hash while the transaction is
	/// imported. This prevents that we import the same transaction
	/// multiple times concurrently.
	pending_transactions_peers: HashMap<H, Vec<PeerId>>,
	config: ProtocolConfig,
	genesis_hash: B::Hash,
	sync: ChainSync<B>,
	context_data: ContextData<B, H>,
	/// List of nodes for which we perform additional logging because they are important for the
	/// user.
	important_peers: HashSet<PeerId>,
	/// Used to report reputation changes.
	peerset_handle: sc_peerset::PeersetHandle,
	transaction_pool: Arc<dyn TransactionPool<H, B>>,
	/// Handles opening the unique substream and sending and receiving raw messages.
	behaviour: GenericProto,
	/// List of notifications protocols that have been registered.
	notification_protocols: Vec<Cow<'static, str>>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
	/// The `PeerId`'s of all boot nodes.
	boot_node_ids: HashSet<PeerId>,
}

#[derive(Default)]
struct PacketStats {
	bytes_in: u64,
	bytes_out: u64,
	count_in: u64,
	count_out: u64,
}

/// Peer information
#[derive(Debug, Clone)]
struct Peer<B: BlockT, H: ExHashT> {
	info: PeerInfo<B>,
	/// Current block request, if any.
	block_request: Option<(Instant, message::BlockRequest<B>)>,
	/// Requests we are no longer interested in.
	obsolete_requests: HashMap<message::RequestId, Instant>,
	/// Holds a set of transactions known to this peer.
	known_transactions: LruHashSet<H>,
	/// Holds a set of blocks known to this peer.
	known_blocks: LruHashSet<B::Hash>,
	/// Request counter,
	next_request_id: message::RequestId,
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

/// Data necessary to create a context.
struct ContextData<B: BlockT, H: ExHashT> {
	// All connected peers
	peers: HashMap<PeerId, Peer<B, H>>,
	stats: HashMap<&'static str, PacketStats>,
	pub chain: Arc<dyn Client<B>>,
}

/// Configuration for the Substrate-specific part of the networking layer.
#[derive(Clone)]
pub struct ProtocolConfig {
	/// Assigned roles.
	pub roles: Roles,
	/// Maximum number of peers to ask the same blocks in parallel.
	pub max_parallel_downloads: u32,
}

impl Default for ProtocolConfig {
	fn default() -> ProtocolConfig {
		ProtocolConfig {
			roles: Roles::FULL,
			max_parallel_downloads: 5,
		}
	}
}

/// Handshake sent when we open a block announces substream.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
struct BlockAnnouncesHandshake<B: BlockT> {
	/// Roles of the node.
	roles: Roles,
	/// Best block number.
	best_number: NumberFor<B>,
	/// Best block hash.
	best_hash: B::Hash,
	/// Genesis block hash.
	genesis_hash: B::Hash,
}

impl<B: BlockT> BlockAnnouncesHandshake<B> {
	fn build(
		protocol_config: &ProtocolConfig,
		best_number: NumberFor<B>,
		best_hash: B::Hash,
		genesis_hash: B::Hash,
	) -> Self {
		BlockAnnouncesHandshake {
			genesis_hash,
			roles: protocol_config.roles,
			best_number,
			best_hash,
		}
	}
}

/// Builds a SCALE-encoded "Status" message to send as handshake for the legacy protocol.
fn build_status_message<B: BlockT>(
	protocol_config: &ProtocolConfig,
	best_number: NumberFor<B>,
	best_hash: B::Hash,
	genesis_hash: B::Hash,
) -> Vec<u8> {
	let status = message::generic::Status {
		version: CURRENT_VERSION,
		min_supported_version: MIN_VERSION,
		genesis_hash,
		roles: protocol_config.roles.into(),
		best_number,
		best_hash,
		chain_status: Vec::new(), // TODO: find a way to make this backwards-compatible
	};

	Message::<B>::Status(status).encode()
}

impl<B: BlockT, H: ExHashT> Protocol<B, H> {
	/// Create a new instance.
	pub fn new(
		config: ProtocolConfig,
		chain: Arc<dyn Client<B>>,
		transaction_pool: Arc<dyn TransactionPool<H, B>>,
		protocol_id: ProtocolId,
		config_role: &config::Role,
		network_config: &config::NetworkConfiguration,
		block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,
		metrics_registry: Option<&Registry>,
	) -> error::Result<(Protocol<B, H>, sc_peerset::PeersetHandle, Vec<(PeerId, Multiaddr)>)> {
		let info = chain.info();
		let sync = ChainSync::new(
			config.roles,
			chain.clone(),
			&info,
			block_announce_validator,
			config.max_parallel_downloads,
		);

		let boot_node_ids = {
			let mut list = HashSet::new();
			for node in &network_config.boot_nodes {
				list.insert(node.peer_id.clone());
			}
			list.shrink_to_fit();
			list
		};

		let important_peers = {
			let mut imp_p = HashSet::new();
			for reserved in &network_config.default_peers_set.reserved_nodes {
				imp_p.insert(reserved.peer_id.clone());
			}
			for reserved in network_config.extra_sets.iter().flat_map(|s| s.set_config.reserved_nodes.iter()) {
				imp_p.insert(reserved.peer_id.clone());
			}
			imp_p.shrink_to_fit();
			imp_p
		};

		let mut known_addresses = Vec::new();

		let (peerset, peerset_handle) = {
			let mut sets = Vec::with_capacity(2 + network_config.extra_sets.len());

			let mut default_sets_reserved = HashSet::new();
			match config_role {
				config::Role::Sentry { validators } => {
					for validator in validators {
						default_sets_reserved.insert(validator.peer_id.clone());
						known_addresses.push((validator.peer_id.clone(), validator.multiaddr.clone()));
					}
				}
				config::Role::Authority { sentry_nodes } => {
					for sentry_node in sentry_nodes {
						default_sets_reserved.insert(sentry_node.peer_id.clone());
						known_addresses.push((sentry_node.peer_id.clone(), sentry_node.multiaddr.clone()));
					}
				}
				_ => {}
			};
			for reserved in network_config.default_peers_set.reserved_nodes.iter() {
				default_sets_reserved.insert(reserved.peer_id.clone());
				known_addresses.push((reserved.peer_id.clone(), reserved.multiaddr.clone()));
			}

			let mut bootnodes = Vec::with_capacity(network_config.boot_nodes.len());
			for bootnode in network_config.boot_nodes.iter() {
				bootnodes.push(bootnode.peer_id.clone());
				known_addresses.push((bootnode.peer_id.clone(), bootnode.multiaddr.clone()));
			}

			// Set number 0 is used for block announces.
			sets.push(sc_peerset::SetConfig {
				in_peers: network_config.default_peers_set.in_peers,
				out_peers: network_config.default_peers_set.out_peers,
				bootnodes,
				reserved_nodes: default_sets_reserved.clone(),
				reserved_only: network_config.default_peers_set.non_reserved_mode
					== config::NonReservedPeerMode::Deny,
			});

			// Set number 1 is used for transactions.
			// The `reserved_nodes` of this set are later kept in sync with the peers we connect
			// to through set 0.
			sets.push(sc_peerset::SetConfig {
				in_peers: network_config.default_peers_set.in_peers,
				out_peers: network_config.default_peers_set.out_peers,
				bootnodes: Vec::new(),
				reserved_nodes: default_sets_reserved,
				reserved_only: network_config.default_peers_set.non_reserved_mode
					== config::NonReservedPeerMode::Deny,
			});

			for set_cfg in &network_config.extra_sets {
				let mut reserved_nodes = HashSet::new();
				for reserved in set_cfg.set_config.reserved_nodes.iter() {
					reserved_nodes.insert(reserved.peer_id.clone());
					known_addresses.push((reserved.peer_id.clone(), reserved.multiaddr.clone()));
				}

				let reserved_only =
					set_cfg.set_config.non_reserved_mode == config::NonReservedPeerMode::Deny;

				sets.push(sc_peerset::SetConfig {
					in_peers: set_cfg.set_config.in_peers,
					out_peers: set_cfg.set_config.out_peers,
					bootnodes: Vec::new(),
					reserved_nodes,
					reserved_only,
				});
			}

			sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig {
				sets,
			})
		};

		let transactions_protocol: Cow<'static, str> = Cow::from({
			let mut proto = String::new();
			proto.push_str("/");
			proto.push_str(protocol_id.as_ref());
			proto.push_str("/transactions/1");
			proto
		});

		let block_announces_protocol: Cow<'static, str> = Cow::from({
			let mut proto = String::new();
			proto.push_str("/");
			proto.push_str(protocol_id.as_ref());
			proto.push_str("/block-announces/1");
			proto
		});

		let behaviour = {
			let versions = &((MIN_VERSION as u8)..=(CURRENT_VERSION as u8)).collect::<Vec<u8>>();
			let handshake_message = Roles::from(config_role).encode();

			let best_number = info.best_number;
			let best_hash = info.best_hash;
			let genesis_hash = info.genesis_hash;

			let block_announces_handshake = BlockAnnouncesHandshake::<B>::build(
				&config,
				best_number,
				best_hash,
				genesis_hash,
			).encode();
			GenericProto::new(
				protocol_id.clone(),
				versions,
				build_status_message::<B>(&config, best_number, best_hash, genesis_hash),
				peerset,
				iter::once((block_announces_protocol, block_announces_handshake))
					.chain(iter::once((transactions_protocol, vec![])))
					.chain(network_config.extra_sets.iter()
						.map(|s| (s.notifications_protocol.clone(), handshake_message.clone()))
					),
			)
		};

		let protocol = Protocol {
			tick_timeout: Box::pin(interval(TICK_TIMEOUT)),
			propagate_timeout: Box::pin(interval(PROPAGATE_TIMEOUT)),
			pending_messages: VecDeque::new(),
			pending_transactions: FuturesUnordered::new(),
			pending_transactions_peers: HashMap::new(),
			config,
			context_data: ContextData {
				peers: HashMap::new(),
				stats: HashMap::new(),
				chain,
			},
			genesis_hash: info.genesis_hash,
			sync,
			important_peers,
			transaction_pool,
			peerset_handle: peerset_handle.clone(),
			behaviour,
			notification_protocols:
				network_config.extra_sets.iter().map(|s| s.notifications_protocol.clone()).collect(),
			metrics: if let Some(r) = metrics_registry {
				Some(Metrics::register(r)?)
			} else {
				None
			},
			boot_node_ids,
		};

		Ok((protocol, peerset_handle, known_addresses))
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.open_peers()
	}

	/// Returns the list of all the peers that the peerset currently requests us to be connected
	/// to on the default set.
	pub fn requested_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.requested_peers(sc_peerset::SetId::from(0))
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.behaviour.num_discovered_peers()
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId, protocol_name: &str) {
		if let Some(position) = self.notification_protocols.iter().position(|p| *p == protocol_name) {
			self.behaviour.disconnect_peer(peer_id, sc_peerset::SetId::from(position + 2));
		} else {
			log::warn!(target: "sub-libp2p", "disconnect_peer() with invalid protocol name")
		}
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.behaviour.peerset_debug_info()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.context_data.peers.values().count()
	}

	/// Returns the number of peers we're connected to and that are being queried.
	pub fn num_active_peers(&self) -> usize {
		self.context_data
			.peers
			.values()
			.filter(|p| p.block_request.is_some())
			.count()
	}

	/// Current global sync state.
	pub fn sync_state(&self) -> SyncState {
		self.sync.status().state
	}

	/// Target sync block number.
	pub fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.sync.status().best_seen_block
	}

	/// Number of peers participating in syncing.
	pub fn num_sync_peers(&self) -> u32 {
		self.sync.status().num_peers
	}

	/// Number of blocks in the import queue.
	pub fn num_queued_blocks(&self) -> u32 {
		self.sync.status().queued_blocks
	}

	/// Number of downloaded blocks.
	pub fn num_downloaded_blocks(&self) -> usize {
		self.sync.num_downloaded_blocks()
	}

	/// Number of active sync requests.
	pub fn num_sync_requests(&self) -> usize {
		self.sync.num_sync_requests()
	}

	/// Inform sync about new best imported block.
	pub fn new_best_block_imported(&mut self, hash: B::Hash, number: NumberFor<B>) {
		trace!(target: "sync", "New best block imported {:?}/#{}", hash, number);

		self.sync.update_chain_info(&hash, number);

		self.behaviour.set_legacy_handshake_message(
			build_status_message::<B>(&self.config, number, hash, self.genesis_hash),
		);
		self.behaviour.set_notif_protocol_handshake(
			sc_peerset::SetId::from(0),
			BlockAnnouncesHandshake::<B>::build(
				&self.config,
				number,
				hash,
				self.genesis_hash,
			).encode()
		);
	}

	fn update_peer_info(&mut self, who: &PeerId) {
		if let Some(info) = self.sync.peer_info(who) {
			if let Some(ref mut peer) = self.context_data.peers.get_mut(who) {
				peer.info.best_hash = info.best_hash;
				peer.info.best_number = info.best_number;
			}
		}
	}

	/// Returns information about all the peers we are connected to after the handshake message.
	pub fn peers_info(&self) -> impl Iterator<Item = (&PeerId, &PeerInfo<B>)> {
		self.context_data.peers.iter().map(|(id, peer)| (id, &peer.info))
	}

	fn on_custom_message(
		&mut self,
		who: PeerId,
		data: BytesMut,
	) -> CustomMessageOutcome<B> {
		let message = match <Message<B> as Decode>::decode(&mut &data[..]) {
			Ok(message) => message,
			Err(err) => {
				debug!(
					target: "sync",
					"Couldn't decode packet sent by {}: {:?}: {}",
					who,
					data,
					err.what(),
				);
				self.peerset_handle.report_peer(who, rep::BAD_MESSAGE);
				return CustomMessageOutcome::None;
			}
		};

		let mut stats = self.context_data.stats.entry(message.id()).or_default();
		stats.bytes_in += data.len() as u64;
		stats.count_in += 1;

		match message {
			GenericMessage::Status(_) =>
				debug!(target: "sub-libp2p", "Received unexpected Status"),
			GenericMessage::BlockAnnounce(announce) =>
				self.push_block_announce_validation(who.clone(), announce),
			GenericMessage::Transactions(m) =>
				self.on_transactions(who, m),
			GenericMessage::BlockResponse(_) =>
				warn!(target: "sub-libp2p", "Received unexpected BlockResponse"),
			GenericMessage::RemoteCallResponse(_) =>
				warn!(target: "sub-libp2p", "Received unexpected RemoteCallResponse"),
			GenericMessage::RemoteReadResponse(_) =>
				warn!(target: "sub-libp2p", "Received unexpected RemoteReadResponse"),
			GenericMessage::RemoteHeaderResponse(_) =>
				warn!(target: "sub-libp2p", "Received unexpected RemoteHeaderResponse"),
			GenericMessage::RemoteChangesResponse(_) =>
				warn!(target: "sub-libp2p", "Received unexpected RemoteChangesResponse"),
			GenericMessage::BlockRequest(_) |
			GenericMessage::RemoteReadChildRequest(_) |
			GenericMessage::RemoteCallRequest(_) |
			GenericMessage::RemoteReadRequest(_) |
			GenericMessage::RemoteHeaderRequest(_) |
			GenericMessage::RemoteChangesRequest(_) |
			GenericMessage::Consensus(_) |
			GenericMessage::ConsensusBatch(_) => {
				debug!(
					target: "sub-libp2p",
					"Received no longer supported legacy request from {:?}",
					who
				);
				self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));
				self.peerset_handle.report_peer(who, rep::BAD_PROTOCOL);
			},
		}

		CustomMessageOutcome::None
	}

	fn update_peer_request(&mut self, who: &PeerId, request: &mut message::BlockRequest<B>) {
		update_peer_request::<B, H>(&mut self.context_data.peers, who, request)
	}

	/// Called by peer when it is disconnecting.
	///
	/// Returns a result if the handshake of this peer was indeed accepted.
	pub fn on_sync_peer_disconnected(&mut self, peer: PeerId) -> Result<(), ()> {
		if self.important_peers.contains(&peer) {
			warn!(target: "sync", "Reserved peer {} disconnected", peer);
		} else {
			trace!(target: "sync", "{} disconnected", peer);
		}

		if let Some(_peer_data) = self.context_data.peers.remove(&peer) {
			self.sync.peer_disconnected(&peer);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Adjusts the reputation of a node.
	pub fn report_peer(&self, who: PeerId, reputation: sc_peerset::ReputationChange) {
		self.peerset_handle.report_peer(who, reputation)
	}

	/// Must be called in response to a [`CustomMessageOutcome::BlockRequest`] being emitted.
	/// Must contain the same `PeerId` and request that have been emitted.
	pub fn on_block_response(
		&mut self,
		peer: PeerId,
		response: message::BlockResponse<B>,
	) -> CustomMessageOutcome<B> {
		let request = if let Some(ref mut p) = self.context_data.peers.get_mut(&peer) {
			if p.obsolete_requests.remove(&response.id).is_some() {
				trace!(target: "sync", "Ignoring obsolete block response packet from {} ({})", peer, response.id);
				return CustomMessageOutcome::None;
			}
			// Clear the request. If the response is invalid peer will be disconnected anyway.
			match p.block_request.take() {
				Some((_, request)) if request.id == response.id => request,
				Some(_) =>  {
					trace!(target: "sync", "Ignoring obsolete block response packet from {} ({})", peer, response.id);
					return CustomMessageOutcome::None;
				}
				None => {
					trace!(target: "sync", "Unexpected response packet from unknown peer {}", peer);
					self.behaviour.disconnect_peer(&peer, sc_peerset::SetId::from(0));
					self.peerset_handle.report_peer(peer, rep::UNEXPECTED_RESPONSE);
					return CustomMessageOutcome::None;
				}
			}
		} else {
			trace!(target: "sync", "Unexpected response packet from unknown peer {}", peer);
			self.behaviour.disconnect_peer(&peer, sc_peerset::SetId::from(0));
			self.peerset_handle.report_peer(peer, rep::UNEXPECTED_RESPONSE);
			return CustomMessageOutcome::None;
		};

		let blocks_range = || match (
			response.blocks.first().and_then(|b| b.header.as_ref().map(|h| h.number())),
			response.blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number())),
		) {
			(Some(first), Some(last)) if first != last => format!(" ({}..{})", first, last),
			(Some(first), Some(_)) => format!(" ({})", first),
			_ => Default::default(),
		};
		trace!(target: "sync", "BlockResponse {} from {} with {} blocks {}",
			response.id,
			peer,
			response.blocks.len(),
			blocks_range(),
		);

		if request.fields == message::BlockAttributes::JUSTIFICATION {
			match self.sync.on_block_justification(peer, response) {
				Ok(sync::OnBlockJustification::Nothing) => CustomMessageOutcome::None,
				Ok(sync::OnBlockJustification::Import { peer, hash, number, justification }) =>
					CustomMessageOutcome::JustificationImport(peer, hash, number, justification),
				Err(sync::BadPeer(id, repu)) => {
					self.behaviour.disconnect_peer(&id, sc_peerset::SetId::from(0));
					self.peerset_handle.report_peer(id, repu);
					CustomMessageOutcome::None
				}
			}
		} else {
			match self.sync.on_block_data(&peer, Some(request), response) {
				Ok(sync::OnBlockData::Import(origin, blocks)) =>
					CustomMessageOutcome::BlockImport(origin, blocks),
				Ok(sync::OnBlockData::Request(peer, mut req)) => {
					self.update_peer_request(&peer, &mut req);
					CustomMessageOutcome::BlockRequest {
						target: peer,
						request: req,
					}
				}
				Err(sync::BadPeer(id, repu)) => {
					self.behaviour.disconnect_peer(&id, sc_peerset::SetId::from(0));
					self.peerset_handle.report_peer(id, repu);
					CustomMessageOutcome::None
				}
			}
		}
	}

	/// Must be called in response to a [`CustomMessageOutcome::BlockRequest`] if it has failed.
	pub fn on_block_request_failed(
		&mut self,
		peer: &PeerId,
	) {
		self.peerset_handle.report_peer(peer.clone(), rep::TIMEOUT);
		self.behaviour.disconnect_peer(peer, sc_peerset::SetId::from(0));
	}

	/// Perform time based maintenance.
	///
	/// > **Note**: This method normally doesn't have to be called except for testing purposes.
	pub fn tick(&mut self) {
		self.maintain_peers();
		self.report_metrics()
	}

	fn maintain_peers(&mut self) {
		let tick = Instant::now();
		let mut aborting = Vec::new();
		{
			for (who, peer) in self.context_data.peers.iter() {
				if peer.block_request.as_ref().map_or(false, |(t, _)| (tick - *t).as_secs() > REQUEST_TIMEOUT_SEC) {
					log!(
						target: "sync",
						if self.important_peers.contains(who) { Level::Warn } else { Level::Trace },
						"Request timeout {}", who
					);
					aborting.push(who.clone());
				} else if peer.obsolete_requests.values().any(|t| (tick - *t).as_secs() > REQUEST_TIMEOUT_SEC) {
					log!(
						target: "sync",
						if self.important_peers.contains(who) { Level::Warn } else { Level::Trace },
						"Obsolete timeout {}", who
					);
					aborting.push(who.clone());
				}
			}
		}

		for p in aborting {
			self.behaviour.disconnect_peer(&p, sc_peerset::SetId::from(0));
			self.peerset_handle.report_peer(p, rep::TIMEOUT);
		}
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

		if self.context_data.peers.contains_key(&who) {
			debug!(target: "sync", "Ignoring duplicate status packet from {}", who);
			return Err(());
		}
		if status.genesis_hash != self.genesis_hash {
			log!(
				target: "sync",
				if self.important_peers.contains(&who) { Level::Warn } else { Level::Trace },
				"Peer is on different chain (our genesis: {} theirs: {})",
				self.genesis_hash, status.genesis_hash
			);
			self.peerset_handle.report_peer(who.clone(), rep::GENESIS_MISMATCH);
			self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));

			if self.boot_node_ids.contains(&who) {
				error!(
					target: "sync",
					"Bootnode with peer id `{}` is on a different chain (our genesis: {} theirs: {})",
					who,
					self.genesis_hash,
					status.genesis_hash,
				);
			}

			return Err(());
		}

		if self.config.roles.is_light() {
			// we're not interested in light peers
			if status.roles.is_light() {
				debug!(target: "sync", "Peer {} is unable to serve light requests", who);
				self.peerset_handle.report_peer(who.clone(), rep::BAD_ROLE);
				self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));
				return Err(());
			}

			// we don't interested in peers that are far behind us
			let self_best_block = self
				.context_data
				.chain
				.info()
				.best_number;
			let blocks_difference = self_best_block
				.checked_sub(&status.best_number)
				.unwrap_or_else(Zero::zero)
				.saturated_into::<u64>();
			if blocks_difference > LIGHT_MAXIMAL_BLOCKS_DIFFERENCE {
				debug!(target: "sync", "Peer {} is far behind us and will unable to serve light requests", who);
				self.peerset_handle.report_peer(who.clone(), rep::PEER_BEHIND_US_LIGHT);
				self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));
				return Err(());
			}
		}

		let peer = Peer {
			info: PeerInfo {
				roles: status.roles,
				best_hash: status.best_hash,
				best_number: status.best_number
			},
			block_request: None,
			known_transactions: LruHashSet::new(NonZeroUsize::new(MAX_KNOWN_TRANSACTIONS)
				.expect("Constant is nonzero")),
			known_blocks: LruHashSet::new(NonZeroUsize::new(MAX_KNOWN_BLOCKS)
				.expect("Constant is nonzero")),
			next_request_id: 0,
			obsolete_requests: HashMap::new(),
		};
		self.context_data.peers.insert(who.clone(), peer);

		debug!(target: "sync", "Connected {}", who);

		let info = self.context_data.peers.get(&who).expect("We just inserted above; QED").info.clone();
		self.pending_messages.push_back(CustomMessageOutcome::PeerNewBest(who.clone(), status.best_number));
		if info.roles.is_full() {
			match self.sync.new_peer(who.clone(), info.best_hash, info.best_number) {
				Ok(None) => (),
				Ok(Some(mut req)) => {
					self.update_peer_request(&who, &mut req);
					self.pending_messages.push_back(CustomMessageOutcome::BlockRequest {
						target: who.clone(),
						request: req,
					});
				},
				Err(sync::BadPeer(id, repu)) => {
					self.behaviour.disconnect_peer(&id, sc_peerset::SetId::from(0));
					self.peerset_handle.report_peer(id, repu);
					return Err(())
				}
			}
		}

		Ok(())
	}

	/// Called when peer sends us new transactions
	fn on_transactions(
		&mut self,
		who: PeerId,
		transactions: message::Transactions<B::Extrinsic>,
	) {
		// sending transaction to light node is considered a bad behavior
		if !self.config.roles.is_full() {
			trace!(target: "sync", "Peer {} is trying to send transactions to the light node", who);
			self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(1));
			self.peerset_handle.report_peer(who, rep::UNEXPECTED_TRANSACTIONS);
			return;
		}

		// Accept transactions only when fully synced
		if self.sync.status().state != SyncState::Idle {
			trace!(target: "sync", "{} Ignoring transactions while syncing", who);
			return;
		}

		trace!(target: "sync", "Received {} transactions from {}", transactions.len(), who);
		if let Some(ref mut peer) = self.context_data.peers.get_mut(&who) {
			for t in transactions {
				if self.pending_transactions.len() > MAX_PENDING_TRANSACTIONS {
					debug!(
						target: "sync",
						"Ignoring any further transactions that exceed `MAX_PENDING_TRANSACTIONS`({}) limit",
						MAX_PENDING_TRANSACTIONS,
					);
					break;
				}

				let hash = self.transaction_pool.hash_of(&t);
				peer.known_transactions.insert(hash.clone());

				self.peerset_handle.report_peer(who.clone(), rep::ANY_TRANSACTION);

				match self.pending_transactions_peers.entry(hash.clone()) {
					Entry::Vacant(entry) => {
						self.pending_transactions.push(PendingTransaction {
							validation: self.transaction_pool.import(t),
							tx_hash: hash,
						});
						entry.insert(vec![who.clone()]);
					},
					Entry::Occupied(mut entry) => {
						entry.get_mut().push(who.clone());
					}
				}
			}
		}
	}

	fn on_handle_transaction_import(&mut self, who: PeerId, import: TransactionImport) {
		match import {
			TransactionImport::KnownGood => self.peerset_handle.report_peer(who, rep::ANY_TRANSACTION_REFUND),
			TransactionImport::NewGood => self.peerset_handle.report_peer(who, rep::GOOD_TRANSACTION),
			TransactionImport::Bad => self.peerset_handle.report_peer(who, rep::BAD_TRANSACTION),
			TransactionImport::None => {},
		}
	}

	/// Propagate one transaction.
	pub fn propagate_transaction(
		&mut self,
		hash: &H,
	) {
		debug!(target: "sync", "Propagating transaction [{:?}]", hash);
		// Accept transactions only when fully synced
		if self.sync.status().state != SyncState::Idle {
			return;
		}
		if let Some(transaction) = self.transaction_pool.transaction(hash) {
			let propagated_to = self.do_propagate_transactions(&[(hash.clone(), transaction)]);
			self.transaction_pool.on_broadcasted(propagated_to);
		}
	}

	fn do_propagate_transactions(
		&mut self,
		transactions: &[(H, B::Extrinsic)],
	) -> HashMap<H, Vec<String>> {
		let mut propagated_to = HashMap::<_, Vec<_>>::new();
		let mut propagated_transactions = 0;

		for (who, peer) in self.context_data.peers.iter_mut() {
			// never send transactions to the light node
			if !peer.info.roles.is_full() {
				continue;
			}

			if !self.behaviour.is_open(who, sc_peerset::SetId::from(1)) {
				continue;
			}

			let (hashes, to_send): (Vec<_>, Vec<_>) = transactions
				.iter()
				.filter(|&(ref hash, _)| peer.known_transactions.insert(hash.clone()))
				.cloned()
				.unzip();

			propagated_transactions += hashes.len();

			if !to_send.is_empty() {
				for hash in hashes {
					propagated_to
						.entry(hash)
						.or_default()
						.push(who.to_base58());
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), who);
				self.behaviour.write_notification(
					who,
					sc_peerset::SetId::from(1),
					to_send.encode()
				);
			}
		}

		if let Some(ref metrics) = self.metrics {
			metrics.propagated_transactions.inc_by(propagated_transactions as _)
		}

		propagated_to
	}

	/// Call when we must propagate ready transactions to peers.
	pub fn propagate_transactions(&mut self) {
		debug!(target: "sync", "Propagating transactions");
		// Accept transactions only when fully synced
		if self.sync.status().state != SyncState::Idle {
			return;
		}
		let transactions = self.transaction_pool.transactions();
		let propagated_to = self.do_propagate_transactions(&transactions);
		self.transaction_pool.on_broadcasted(propagated_to);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&mut self, hash: B::Hash, data: Vec<u8>) {
		let header = match self.context_data.chain.header(BlockId::Hash(hash)) {
			Ok(Some(header)) => header,
			Ok(None) => {
				warn!("Trying to announce unknown block: {}", hash);
				return;
			}
			Err(e) => {
				warn!("Error reading block header {}: {:?}", hash, e);
				return;
			}
		};

		// don't announce genesis block since it will be ignored
		if header.number().is_zero() {
			return;
		}

		let is_best = self.context_data.chain.info().best_hash == hash;
		debug!(target: "sync", "Reannouncing block {:?} is_best: {}", hash, is_best);

		for (who, ref mut peer) in self.context_data.peers.iter_mut() {
			let inserted = peer.known_blocks.insert(hash);
			if inserted {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, who);
				let message = message::BlockAnnounce {
					header: header.clone(),
					state: if is_best {
						Some(message::BlockState::Best)
					} else {
						Some(message::BlockState::Normal)
					},
					data: Some(data.clone()),
				};

				self.behaviour.write_notification(
					who,
					sc_peerset::SetId::from(0),
					message.encode()
				);
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
	fn push_block_announce_validation(
		&mut self,
		who: PeerId,
		announce: BlockAnnounce<B::Header>,
	) {
		let hash = announce.header.hash();

		if let Some(ref mut peer) = self.context_data.peers.get_mut(&who) {
			peer.known_blocks.insert(hash.clone());
		}

		let is_best = match announce.state.unwrap_or(message::BlockState::Best) {
			message::BlockState::Best => true,
			message::BlockState::Normal => false,
		};

		self.sync.push_block_announce_validation(who, hash, announce, is_best);
	}

	/// Process the result of the block announce validation.
	fn process_block_announce_validation_result(
		&mut self,
		validation_result: sync::PollBlockAnnounceValidation<B::Header>,
	) -> CustomMessageOutcome<B> {
		let (header, is_best, who) = match validation_result {
			sync::PollBlockAnnounceValidation::Nothing { is_best, who, header } => {
				self.update_peer_info(&who);

				// `on_block_announce` returns `OnBlockAnnounce::ImportHeader`
				// when we have all data required to import the block
				// in the BlockAnnounce message. This is only when:
				// 1) we're on light client;
				// AND
				// 2) parent block is already imported and not pruned.
				if is_best {
					return CustomMessageOutcome::PeerNewBest(who, *header.number())
				} else {
					return CustomMessageOutcome::None
				}
			}
			sync::PollBlockAnnounceValidation::ImportHeader { header, is_best, who } => {
				self.update_peer_info(&who);
				(header, is_best, who)
			}
			sync::PollBlockAnnounceValidation::Failure { who, disconnect } => {
				if disconnect {
					self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));
				}

				self.report_peer(who, rep::BAD_BLOCK_ANNOUNCEMENT);
				return CustomMessageOutcome::None
			}
		};

		let number = *header.number();

		// to import header from announced block let's construct response to request that normally
		// would have been sent over network (but it is not in our case)
		let blocks_to_import = self.sync.on_block_data(
			&who,
			None,
			message::generic::BlockResponse {
				id: 0,
				blocks: vec![
					message::generic::BlockData {
						hash: header.hash(),
						header: Some(header),
						body: None,
						receipt: None,
						message_queue: None,
						justification: None,
					},
				],
			},
		);

		if is_best {
			self.pending_messages.push_back(
				CustomMessageOutcome::PeerNewBest(who, number),
			);
		}

		match blocks_to_import {
			Ok(sync::OnBlockData::Import(origin, blocks)) => {
				CustomMessageOutcome::BlockImport(origin, blocks)
			},
			Ok(sync::OnBlockData::Request(peer, mut req)) => {
				self.update_peer_request(&peer, &mut req);
				CustomMessageOutcome::BlockRequest {
					target: peer,
					request: req,
				}
			}
			Err(sync::BadPeer(id, repu)) => {
				self.behaviour.disconnect_peer(&id, sc_peerset::SetId::from(0));
				self.peerset_handle.report_peer(id, repu);
				CustomMessageOutcome::None
			}
		}
	}

	/// Call this when a block has been finalized. The sync layer may have some additional
	/// requesting to perform.
	pub fn on_block_finalized(&mut self, hash: B::Hash, header: &B::Header) {
		self.sync.on_block_finalized(&hash, *header.number())
	}

	/// Request a justification for the given block.
	///
	/// Uses `protocol` to queue a new justification request and tries to dispatch all pending
	/// requests.
	pub fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		self.sync.request_justification(&hash, number)
	}

	/// Request syncing for the given block from given set of peers.
	/// Uses `protocol` to queue a new block download request and tries to dispatch all pending
	/// requests.
	pub fn set_sync_fork_request(&mut self, peers: Vec<PeerId>, hash: &B::Hash, number: NumberFor<B>) {
		self.sync.set_sync_fork_request(peers, hash, number)
	}

	/// A batch of blocks have been processed, with or without errors.
	/// Call this when a batch of blocks have been processed by the importqueue, with or without
	/// errors.
	pub fn on_blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>
	) {
		let results = self.sync.on_blocks_processed(
			imported,
			count,
			results,
		);
		for result in results {
			match result {
				Ok((id, mut req)) => {
					update_peer_request(&mut self.context_data.peers, &id, &mut req);
					self.pending_messages.push_back(CustomMessageOutcome::BlockRequest {
						target: id,
						request: req,
					});
				}
				Err(sync::BadPeer(id, repu)) => {
					self.behaviour.disconnect_peer(&id, sc_peerset::SetId::from(0));
					self.peerset_handle.report_peer(id, repu)
				}
			}
		}
	}

	/// Call this when a justification has been processed by the import queue, with or without
	/// errors.
	pub fn justification_import_result(&mut self, who: PeerId, hash: B::Hash, number: NumberFor<B>, success: bool) {
		self.sync.on_justification_import(hash, number, success);
		if !success {
			log::info!("💔 Invalid justification provided by {} for #{}", who, hash);
			self.behaviour.disconnect_peer(&who, sc_peerset::SetId::from(0));
			self.peerset_handle.report_peer(
				who,
				sc_peerset::ReputationChange::new_fatal("Invalid justification")
			);
		}
	}

	/// Set whether the syncing peers set is in reserved-only mode.
	pub fn set_reserved_only(&self, reserved_only: bool) {
		self.peerset_handle.set_reserved_only(sc_peerset::SetId::from(0), reserved_only);
		self.peerset_handle.set_reserved_only(sc_peerset::SetId::from(1), reserved_only);
	}

	/// Removes a `PeerId` from the list of reserved peers for syncing purposes.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.remove_reserved_peer(sc_peerset::SetId::from(0), peer.clone());
		self.peerset_handle.remove_reserved_peer(sc_peerset::SetId::from(1), peer);
	}

	/// Adds a `PeerId` to the list of reserved peers for syncing purposes.
	pub fn add_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.add_reserved_peer(sc_peerset::SetId::from(0), peer.clone());
		self.peerset_handle.add_reserved_peer(sc_peerset::SetId::from(1), peer);
	}

	/// Sets the list of reserved peers for syncing purposes.
	pub fn set_reserved_peers(&self, peers: HashSet<PeerId>) {
		self.peerset_handle.set_reserved_peers(sc_peerset::SetId::from(0), peers.clone());
		self.peerset_handle.set_reserved_peers(sc_peerset::SetId::from(1), peers);
	}

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_set_reserved_peer(&self, protocol: Cow<'static, str>, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_reserved_peer(sc_peerset::SetId::from(index + 2), peer);
		} else {
			log::error!(
				target: "sub-libp2p",
				"remove_set_reserved_peer with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Adds a `PeerId` to the list of reserved peers.
	pub fn add_set_reserved_peer(&self, protocol: Cow<'static, str>, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_reserved_peer(sc_peerset::SetId::from(index + 2), peer);
		} else {
			log::error!(
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
			self.peerset_handle.add_to_peers_set(sc_peerset::SetId::from(0), peer_id);
		}
	}

	/// Add a peer to a peers set.
	pub fn add_to_peers_set(&self, protocol: Cow<'static, str>, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_to_peers_set(sc_peerset::SetId::from(index + 2), peer);
		} else {
			log::error!(
				target: "sub-libp2p",
				"add_to_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Remove a peer from a peers set.
	pub fn remove_from_peers_set(&self, protocol: Cow<'static, str>, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_from_peers_set(sc_peerset::SetId::from(index + 2), peer);
		} else {
			log::error!(
				target: "sub-libp2p",
				"remove_from_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}

	fn format_stats(&self) -> String {
		let mut out = String::new();
		for (id, stats) in &self.context_data.stats {
			let _ = writeln!(
				&mut out,
				"{}: In: {} bytes ({}), Out: {} bytes ({})",
				id,
				stats.bytes_in,
				stats.count_in,
				stats.bytes_out,
				stats.count_out,
			);
		}
		out
	}

	fn report_metrics(&self) {
		use std::convert::TryInto;

		if let Some(metrics) = &self.metrics {
			let mut obsolete_requests: u64 = 0;
			for peer in self.context_data.peers.values() {
				let n = peer.obsolete_requests.len().try_into().unwrap_or(std::u64::MAX);
				obsolete_requests = obsolete_requests.saturating_add(n);
			}
			metrics.obsolete_requests.set(obsolete_requests);

			let n = self.context_data.peers.len().try_into().unwrap_or(std::u64::MAX);
			metrics.peers.set(n);

			let m = self.sync.metrics();

			metrics.fork_targets.set(m.fork_targets.into());
			metrics.queued_blocks.set(m.queued_blocks.into());

			metrics.justifications.with_label_values(&["pending"])
				.set(m.justifications.pending_requests.into());
			metrics.justifications.with_label_values(&["active"])
				.set(m.justifications.active_requests.into());
			metrics.justifications.with_label_values(&["failed"])
				.set(m.justifications.failed_requests.into());
			metrics.justifications.with_label_values(&["importing"])
				.set(m.justifications.importing_requests.into());
		}
	}
}

/// Outcome of an incoming custom message.
#[derive(Debug)]
#[must_use]
pub enum CustomMessageOutcome<B: BlockT> {
	BlockImport(BlockOrigin, Vec<IncomingBlock<B>>),
	JustificationImport(Origin, B::Hash, NumberFor<B>, Justification),
	/// Notification protocols have been opened with a remote.
	NotificationStreamOpened {
		remote: PeerId,
		protocol: Cow<'static, str>,
		roles: Roles,
		notifications_sink: NotificationsSink
	},
	/// The [`NotificationsSink`] of some notification protocols need an update.
	NotificationStreamReplaced {
		remote: PeerId,
		protocol: Cow<'static, str>,
		notifications_sink: NotificationsSink,
	},
	/// Notification protocols have been closed with a remote.
	NotificationStreamClosed { remote: PeerId, protocol: Cow<'static, str> },
	/// Messages have been received on one or more notifications protocols.
	NotificationsReceived { remote: PeerId, messages: Vec<(Cow<'static, str>, Bytes)> },
	/// A new block request must be emitted.
	/// You must later call either [`Protocol::on_block_response`] or
	/// [`Protocol::on_block_request_failed`].
	/// Each peer can only have one active request. If a request already exists for this peer, it
	/// must be silently discarded.
	/// It is the responsibility of the handler to ensure that a timeout exists.
	BlockRequest { target: PeerId, request: message::BlockRequest<B> },
	/// Peer has a reported a new head of chain.
	PeerNewBest(PeerId, NumberFor<B>),
	/// Now connected to a new peer for syncing purposes.
	SyncConnected(PeerId),
	/// No longer connected to a peer for syncing purposes.
	SyncDisconnected(PeerId),
	None,
}

fn update_peer_request<B: BlockT, H: ExHashT>(
	peers: &mut HashMap<PeerId, Peer<B, H>>,
	who: &PeerId,
	request: &mut message::BlockRequest<B>,
) {
	if let Some(ref mut peer) = peers.get_mut(who) {
		request.id = peer.next_request_id;
		peer.next_request_id += 1;
		if let Some((timestamp, request)) = peer.block_request.take() {
			trace!(target: "sync", "Request {} for {} is now obsolete.", request.id, who);
			peer.obsolete_requests.insert(request.id, timestamp);
		}
		peer.block_request = Some((Instant::now(), request.clone()));
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviour for Protocol<B, H> {
	type ProtocolsHandler = <GenericProto as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = CustomMessageOutcome<B>;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		self.behaviour.new_handler()
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		self.behaviour.addresses_of_peer(peer_id)
	}

	fn inject_connection_established(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		self.behaviour.inject_connection_established(peer_id, conn, endpoint)
	}

	fn inject_connection_closed(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		self.behaviour.inject_connection_closed(peer_id, conn, endpoint)
	}

	fn inject_connected(&mut self, peer_id: &PeerId) {
		self.behaviour.inject_connected(peer_id)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId) {
		self.behaviour.inject_disconnected(peer_id)
	}

	fn inject_event(
		&mut self,
		peer_id: PeerId,
		connection: ConnectionId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent,
	) {
		self.behaviour.inject_event(peer_id, connection, event)
	}

	fn poll(
		&mut self,
		cx: &mut std::task::Context,
		params: &mut impl PollParameters,
	) -> Poll<
		NetworkBehaviourAction<
			<<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::InEvent,
			Self::OutEvent
		>
	> {
		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message));
		}

		while let Poll::Ready(Some(())) = self.tick_timeout.poll_next_unpin(cx) {
			self.tick();
		}

		while let Poll::Ready(Some(())) = self.propagate_timeout.poll_next_unpin(cx) {
			self.propagate_transactions();
		}

		for (id, mut r) in self.sync.block_requests() {
			update_peer_request(&mut self.context_data.peers, &id, &mut r);
			let event = CustomMessageOutcome::BlockRequest {
				target: id.clone(),
				request: r,
			};
			self.pending_messages.push_back(event);
		}
		for (id, mut r) in self.sync.justification_requests() {
			update_peer_request(&mut self.context_data.peers, &id, &mut r);
			let event = CustomMessageOutcome::BlockRequest {
				target: id,
				request: r,
			};
			self.pending_messages.push_back(event);
		}
		if let Poll::Ready(Some((tx_hash, result))) = self.pending_transactions.poll_next_unpin(cx) {
			if let Some(peers) = self.pending_transactions_peers.remove(&tx_hash) {
				peers.into_iter().for_each(|p| self.on_handle_transaction_import(p, result));
			} else {
				warn!(target: "sub-libp2p", "Inconsistent state, no peers for pending transaction!");
			}
		}

		// Check if there is any block announcement validation finished.
		while let Poll::Ready(result) = self.sync.poll_block_announce_validation(cx) {
			match self.process_block_announce_validation_result(result) {
				CustomMessageOutcome::None => {},
				outcome => self.pending_messages.push_back(outcome),
			}
		}

		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message));
		}

		let event = match self.behaviour.poll(cx, params) {
			Poll::Pending => return Poll::Pending,
			Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev)) => ev,
			Poll::Ready(NetworkBehaviourAction::DialAddress { address }) =>
				return Poll::Ready(NetworkBehaviourAction::DialAddress { address }),
			Poll::Ready(NetworkBehaviourAction::DialPeer { peer_id, condition }) =>
				return Poll::Ready(NetworkBehaviourAction::DialPeer { peer_id, condition }),
			Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }) =>
				return Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }),
			Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }) =>
				return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }),
		};

		let outcome = match event {
			GenericProtoOut::CustomProtocolOpen { peer_id, set_id, received_handshake, notifications_sink, .. } => {
				// Set number 0 is hardcoded the default set of peers we sync from.
				if set_id == sc_peerset::SetId::from(0) {
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

							if self.on_sync_peer_connected(peer_id.clone(), handshake).is_ok() {
								// Set 1 is kept in sync with the connected peers of set 0.
								self.peerset_handle.add_to_peers_set(
									sc_peerset::SetId::from(1),
									peer_id.clone()
								);
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
						}
						Err(err) => {
							match <BlockAnnouncesHandshake<B> as DecodeAll>::decode_all(&mut &received_handshake[..]) {
								Ok(handshake) => {
									if self.on_sync_peer_connected(peer_id.clone(), handshake).is_ok() {
										// Set 1 is kept in sync with the connected peers of set 0.
										self.peerset_handle.add_to_peers_set(
											sc_peerset::SetId::from(1),
											peer_id.clone()
										);
										CustomMessageOutcome::SyncConnected(peer_id)
									} else {
										CustomMessageOutcome::None
									}
								}
								Err(err2) => {
									debug!(
										target: "sync",
										"Couldn't decode handshake sent by {}: {:?}: {} & {}",
										peer_id,
										received_handshake,
										err.what(),
										err2,
									);
									self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
									CustomMessageOutcome::None
								}
							}
						}
					}

				} else if set_id == sc_peerset::SetId::from(1) {
					// Nothing to do.
					CustomMessageOutcome::None
				} else {
					match message::Roles::decode_all(&received_handshake[..]) {
						Ok(roles) =>
							CustomMessageOutcome::NotificationStreamOpened {
								remote: peer_id,
								protocol: self.notification_protocols[usize::from(set_id) - 2].clone(),
								roles,
								notifications_sink,
							},
						Err(err) => {
							debug!(target: "sync", "Failed to parse remote handshake: {}", err);
							self.behaviour.disconnect_peer(&peer_id, set_id);
							self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						}
					}
				}
			}
			GenericProtoOut::CustomProtocolReplaced { peer_id, notifications_sink, set_id } => {
				if set_id == sc_peerset::SetId::from(0) || set_id == sc_peerset::SetId::from(1) {
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamReplaced {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id) - 2].clone(),
						notifications_sink,
					}
				}
			},
			GenericProtoOut::CustomProtocolClosed { peer_id, set_id } => {
				// Set number 0 is hardcoded the default set of peers we sync from.
				if set_id == sc_peerset::SetId::from(0) {
					if self.on_sync_peer_disconnected(peer_id.clone()).is_ok() {
						// Set 1 is kept in sync with the connected peers of set 0.
						self.peerset_handle.remove_reserved_peer(
							sc_peerset::SetId::from(1),
							peer_id.clone()
						);
						CustomMessageOutcome::SyncDisconnected(peer_id)
					} else {
						log::debug!(
							target: "sync",
							"Disconnected peer which had earlier been refused by on_sync_peer_connected {}",
							peer_id
						);
						CustomMessageOutcome::None
					}
				} else if set_id == sc_peerset::SetId::from(1) {
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamClosed {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id) - 2].clone(),
					}
				}
			},
			GenericProtoOut::LegacyMessage { peer_id, message } =>
				self.on_custom_message(peer_id, message),
			GenericProtoOut::Notification { peer_id, set_id, message } =>
				match usize::from(set_id) {
					0 => {
						if let Ok(announce) = message::BlockAnnounce::decode(&mut message.as_ref()) {
							self.push_block_announce_validation(peer_id, announce);

							// Make sure that the newly added block announce validation future was
							// polled once to be registered in the task.
							if let Poll::Ready(res) = self.sync.poll_block_announce_validation(cx) {
								self.process_block_announce_validation_result(res)
							} else {
								CustomMessageOutcome::None
							}
						} else {
							warn!(target: "sub-libp2p", "Failed to decode block announce");
							CustomMessageOutcome::None
						}
					}
					1 => {
						if let Ok(m) = message::Transactions::decode(&mut message.as_ref()) {
							self.on_transactions(peer_id, m);
						} else {
							warn!(target: "sub-libp2p", "Failed to decode transactions list");
						}
						CustomMessageOutcome::None
					}
					_ => {
						let protocol_name = self.notification_protocols[usize::from(set_id) - 2].clone();
						CustomMessageOutcome::NotificationsReceived {
							remote: peer_id,
							messages: vec![(protocol_name, message.freeze())],
						}
					}
				}
		};

		if let CustomMessageOutcome::None = outcome {
			Poll::Pending
		} else {
			Poll::Ready(NetworkBehaviourAction::GenerateEvent(outcome))
		}
	}

	fn inject_addr_reach_failure(
		&mut self,
		peer_id: Option<&PeerId>,
		addr: &Multiaddr,
		error: &dyn std::error::Error
	) {
		self.behaviour.inject_addr_reach_failure(peer_id, addr, error)
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.behaviour.inject_dial_failure(peer_id)
	}

	fn inject_new_listen_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_new_listen_addr(addr)
	}

	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_expired_listen_addr(addr)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.behaviour.inject_new_external_addr(addr)
	}

	fn inject_listener_error(&mut self, id: ListenerId, err: &(dyn std::error::Error + 'static)) {
		self.behaviour.inject_listener_error(id, err);
	}

	fn inject_listener_closed(&mut self, id: ListenerId, reason: Result<(), &io::Error>) {
		self.behaviour.inject_listener_closed(id, reason);
	}
}

impl<B: BlockT, H: ExHashT> Drop for Protocol<B, H> {
	fn drop(&mut self) {
		debug!(target: "sync", "Network stats:\n{}", self.format_stats());
	}
}
