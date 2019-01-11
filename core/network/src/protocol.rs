// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::collections::{HashMap, HashSet, BTreeMap};
use std::{mem, cmp};
use std::sync::Arc;
use std::time;
use parking_lot::RwLock;
use rustc_hex::ToHex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor, As, Zero};
use runtime_primitives::generic::BlockId;
use network_libp2p::{NodeIndex, Severity};
use codec::{Encode, Decode};
use consensus::import_queue::ImportQueue;
use message::{self, Message};
use message::generic::Message as GenericMessage;
use consensus_gossip::ConsensusGossip;
use specialization::NetworkSpecialization;
use sync::{ChainSync, Status as SyncStatus, SyncState};
use service::{TransactionPool, ExHashT};
use config::{ProtocolConfig, Roles};
use chain::Client;
use client::light::fetcher::ChangesProof;
use on_demand::OnDemandService;
use io::SyncIo;
use error;

const REQUEST_TIMEOUT_SEC: u64 = 40;

/// Current protocol version.
pub (crate) const CURRENT_VERSION: u32 = 1;

// Maximum allowed entries in `BlockResponse`
const MAX_BLOCK_DATA_RESPONSE: u32 = 128;
/// When light node connects to the full node and the full node is behind light node
/// for at least `LIGHT_MAXIMAL_BLOCKS_DIFFERENCE` blocks, we consider it unuseful
/// and disconnect to free connection slot.
const LIGHT_MAXIMAL_BLOCKS_DIFFERENCE: u64 = 8192;

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	config: ProtocolConfig,
	on_demand: Option<Arc<OnDemandService<B>>>,
	genesis_hash: B::Hash,
	sync: Arc<RwLock<ChainSync<B>>>,
	specialization: RwLock<S>,
	consensus_gossip: RwLock<ConsensusGossip<B>>,
	context_data: ContextData<B, H>,
	// Connected peers pending Status message.
	handshaking_peers: RwLock<HashMap<NodeIndex, time::Instant>>,
	transaction_pool: Arc<TransactionPool<H, B>>,
}
/// Syncing status and statistics
#[derive(Clone)]
pub struct ProtocolStatus<B: BlockT> {
	/// Sync status.
	pub sync: SyncStatus<B>,
	/// Total number of connected peers
	pub num_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
}

/// Peer information
struct Peer<B: BlockT, H: ExHashT> {
	/// Protocol version
	protocol_version: u32,
	/// Roles
	roles: Roles,
	/// Peer best block hash
	best_hash: B::Hash,
	/// Peer best block number
	best_number: <B::Header as HeaderT>::Number,
	/// Pending block request if any
	block_request: Option<message::BlockRequest<B>>,
	/// Pending block request timestamp
	block_request_timestamp: Option<time::Instant>,
	/// Pending block justification request if any
	block_justification_request: Option<message::BlockJustificationRequest<B>>,
	/// Pending block justification request timestamp
	block_justification_request_timestamp: Option<time::Instant>,
	/// Holds a set of transactions known to this peer.
	known_extrinsics: HashSet<H>,
	/// Holds a set of blocks known to this peer.
	known_blocks: HashSet<B::Hash>,
	/// Request counter,
	next_request_id: message::RequestId,
}

/// Info about a peer's known state.
#[derive(Debug)]
pub struct PeerInfo<B: BlockT> {
	/// Roles
	pub roles: Roles,
	/// Protocol version
	pub protocol_version: u32,
	/// Peer best block hash
	pub best_hash: B::Hash,
	/// Peer best block number
	pub best_number: <B::Header as HeaderT>::Number,
}

/// Context for a network-specific handler.
pub trait Context<B: BlockT> {
	/// Get a reference to the client.
	fn client(&self) -> &::chain::Client<B>;

	/// Point out that a peer has been malign or irresponsible or appeared lazy.
	fn report_peer(&mut self, who: NodeIndex, reason: Severity);

	/// Get peer info.
	fn peer_info(&self, peer: NodeIndex) -> Option<PeerInfo<B>>;

	/// Send a message to a peer.
	fn send_message(&mut self, who: NodeIndex, data: ::message::Message<B>);
}

/// Protocol context.
pub(crate) struct ProtocolContext<'a, B: 'a + BlockT, H: 'a + ExHashT> {
	io: &'a mut SyncIo,
	context_data: &'a ContextData<B, H>,
}

impl<'a, B: BlockT + 'a, H: 'a + ExHashT> ProtocolContext<'a, B, H> {
	pub(crate) fn new(context_data: &'a ContextData<B, H>, io: &'a mut SyncIo) -> Self {
		ProtocolContext {
			io,
			context_data,
		}
	}

	/// Send a message to a peer.
	pub fn send_message(&mut self, who: NodeIndex, message: Message<B>) {
		send_message(&self.context_data.peers, self.io, who, message)
	}

	/// Point out that a peer has been malign or irresponsible or appeared lazy.
	pub fn report_peer(&mut self, who: NodeIndex, reason: Severity) {
		self.io.report_peer(who, reason);
	}

	/// Get peer info.
	pub fn peer_info(&self, peer: NodeIndex) -> Option<PeerInfo<B>> {
		self.context_data.peers.read().get(&peer).map(|p| {
			PeerInfo {
				roles: p.roles,
				protocol_version: p.protocol_version,
				best_hash: p.best_hash,
				best_number: p.best_number,
			}
		})
	}
}

impl<'a, B: BlockT + 'a, H: ExHashT + 'a> Context<B> for ProtocolContext<'a, B, H> {
	fn send_message(&mut self, who: NodeIndex, message: Message<B>) {
		ProtocolContext::send_message(self, who, message);
	}

	fn report_peer(&mut self, who: NodeIndex, reason: Severity) {
		ProtocolContext::report_peer(self, who, reason);
	}

	fn peer_info(&self, who: NodeIndex) -> Option<PeerInfo<B>> {
		ProtocolContext::peer_info(self, who)
	}

	fn client(&self) -> &Client<B> {
		&*self.context_data.chain
	}
}

/// Data necessary to create a context.
pub(crate) struct ContextData<B: BlockT, H: ExHashT> {
	// All connected peers
	peers: RwLock<HashMap<NodeIndex, Peer<B, H>>>,
	pub chain: Arc<Client<B>>,
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Protocol<B, S, H> {
	/// Create a new instance.
	pub fn new<I: 'static + ImportQueue<B>>(
		config: ProtocolConfig,
		chain: Arc<Client<B>>,
		import_queue: Arc<I>,
		on_demand: Option<Arc<OnDemandService<B>>>,
		transaction_pool: Arc<TransactionPool<H, B>>,
		specialization: S,
	) -> error::Result<Self>
		where I: ImportQueue<B>
	{
		let info = chain.info()?;
		let sync = ChainSync::new(config.roles, &info, import_queue);
		let protocol = Protocol {
			config: config,
			context_data: ContextData {
				peers: RwLock::new(HashMap::new()),
				chain,
			},
			on_demand,
			genesis_hash: info.chain.genesis_hash,
			sync: Arc::new(RwLock::new(sync)),
			specialization: RwLock::new(specialization),
			consensus_gossip: RwLock::new(ConsensusGossip::new()),
			handshaking_peers: RwLock::new(HashMap::new()),
			transaction_pool: transaction_pool,
		};
		Ok(protocol)
	}

	pub(crate) fn context_data(&self) -> &ContextData<B, H> {
		&self.context_data
	}

	pub(crate) fn sync(&self) -> &Arc<RwLock<ChainSync<B>>> {
		&self.sync
	}

	pub(crate) fn consensus_gossip<'a>(&'a self) -> &'a RwLock<ConsensusGossip<B>> {
		&self.consensus_gossip
	}

	/// Returns protocol status
	pub fn status(&self) -> ProtocolStatus<B> {
		let sync = self.sync.read();
		let peers = self.context_data.peers.read();
		ProtocolStatus {
			sync: sync.status(),
			num_peers: peers.values().count(),
			num_active_peers: peers.values().filter(|p| p.block_request.is_some()).count(),
		}
	}

	pub fn peers(&self) -> Vec<(NodeIndex, PeerInfo<B>)> {
		self.context_data.peers.read().iter().map(|(idx, p)| {
			(
				*idx,
				PeerInfo {
					roles: p.roles,
					protocol_version: p.protocol_version,
					best_hash: p.best_hash,
					best_number: p.best_number,
				}
			)
		}).collect()
	}

	pub fn handle_packet(&self, io: &mut SyncIo, who: NodeIndex, mut data: &[u8]) {
		let message: Message<B> = match Decode::decode(&mut data) {
			Some(m) => m,
			None => {
				trace!(target: "sync", "Invalid packet from {}", who);
				io.report_peer(who, Severity::Bad("Peer sent us a packet with invalid format"));
				return;
			}
		};

		fn validate_response<B: BlockT, H: ExHashT, R, F, G>(
			io: &mut SyncIo,
			who: NodeIndex,
			context: &ContextData<B, H>,
			response_id: message::RequestId,
			request_visitor: F,
			request_id: G,
		) -> Option<R>
		where F: Fn(&mut Peer<B, H>) -> (&mut Option<time::Instant>, &mut Option<R>),
			  G: Fn(&R) -> message::RequestId,
		{
			let request = {
				let mut peers = context.peers.write();
				if let Some(ref mut peer) = peers.get_mut(&who) {
					let (timestamp, request) = request_visitor(peer);

					*timestamp = None;
					match mem::replace(request, None) {
						Some(r) => r,
						None => {
							io.report_peer(who, Severity::Bad("Unexpected response packet received from peer"));
							return None;
						}
					}
				} else {
					io.report_peer(who, Severity::Bad("Unexpected packet received from peer"));
					return None;
				}
			};

			let request_id = request_id(&request);
			if request_id != response_id {
				trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} got {})", who, request_id, response_id);
				return None;
			}

			Some(request)
		}

		match message {
			GenericMessage::Status(s) => self.on_status_message(io, who, s),
			GenericMessage::BlockRequest(r) => self.on_block_request(io, who, r),
			GenericMessage::BlockResponse(r) => {
				if let Some(request) = validate_response(
					io,
					who,
					&self.context_data,
					r.id,
					|peer| (&mut peer.block_request_timestamp, &mut peer.block_request),
					|block_request| block_request.id,
				) {
					self.on_block_response(io, who, request, r);
				}
			},
			GenericMessage::BlockAnnounce(announce) => self.on_block_announce(io, who, announce),
			GenericMessage::BlockJustificationRequest(r) => self.on_block_justification_request(io, who, r),
			GenericMessage::BlockJustificationResponse(r) => {
				if let Some(request) = validate_response(
					io,
					who,
					&self.context_data,
					r.id,
					|peer| (&mut peer.block_justification_request_timestamp, &mut peer.block_justification_request),
					|block_justification_request| block_justification_request.id,
				) {
					self.on_block_justification_response(io, who, request, r);
				}
			},
			GenericMessage::Transactions(m) => self.on_extrinsics(io, who, m),
			GenericMessage::RemoteCallRequest(request) => self.on_remote_call_request(io, who, request),
			GenericMessage::RemoteCallResponse(response) => self.on_remote_call_response(io, who, response),
			GenericMessage::RemoteReadRequest(request) => self.on_remote_read_request(io, who, request),
			GenericMessage::RemoteReadResponse(response) => self.on_remote_read_response(io, who, response),
			GenericMessage::RemoteHeaderRequest(request) => self.on_remote_header_request(io, who, request),
			GenericMessage::RemoteHeaderResponse(response) => self.on_remote_header_response(io, who, response),
			GenericMessage::RemoteChangesRequest(request) => self.on_remote_changes_request(io, who, request),
			GenericMessage::RemoteChangesResponse(response) => self.on_remote_changes_response(io, who, response),
			GenericMessage::Consensus(topic, msg, broadcast) => {
				self.consensus_gossip.write().on_incoming(&mut ProtocolContext::new(&self.context_data, io), who, topic, msg, broadcast);
			},
			other => self.specialization.write().on_message(&mut ProtocolContext::new(&self.context_data, io), who, &mut Some(other)),
		}
	}

	pub fn send_message(&self, io: &mut SyncIo, who: NodeIndex, message: Message<B>) {
		send_message::<B, H>(&self.context_data.peers, io, who, message)
	}

	pub fn gossip_consensus_message(&self, io: &mut SyncIo, topic: B::Hash, message: Vec<u8>, broadcast: bool) {
		let gossip = self.consensus_gossip();
		self.with_spec(io, move |_s, context|{
			gossip.write().multicast(context, topic, message, broadcast);
		});
	}

	/// Called when a new peer is connected
	pub fn on_peer_connected(&self, io: &mut SyncIo, who: NodeIndex) {
		trace!(target: "sync", "Connected {}: {}", who, io.peer_debug_info(who));
		self.handshaking_peers.write().insert(who, time::Instant::now());
		self.send_status(io, who);
	}

	/// Called by peer when it is disconnecting
	pub fn on_peer_disconnected(&self, io: &mut SyncIo, peer: NodeIndex) {
		trace!(target: "sync", "Disconnecting {}: {}", peer, io.peer_debug_info(peer));

		// lock all the the peer lists so that add/remove peer events are in order
		let mut sync = self.sync.write();
		let mut spec = self.specialization.write();

		let removed = {
			let mut peers = self.context_data.peers.write();
			let mut handshaking_peers = self.handshaking_peers.write();
			handshaking_peers.remove(&peer);
			peers.remove(&peer).is_some()
		};
		if removed {
			let mut context = ProtocolContext::new(&self.context_data, io);
			self.consensus_gossip.write().peer_disconnected(&mut context, peer);
			sync.peer_disconnected(&mut context, peer);
			spec.on_disconnect(&mut context, peer);
			self.on_demand.as_ref().map(|s| s.on_disconnect(peer));
		}
	}

	fn on_block_request(&self, io: &mut SyncIo, peer: NodeIndex, request: message::BlockRequest<B>) {
		trace!(target: "sync", "BlockRequest {} from {}: from {:?} to {:?} max {:?}", request.id, peer, request.from, request.to, request.max);
		let mut blocks = Vec::new();
		let mut id = match request.from {
			message::FromBlock::Hash(h) => BlockId::Hash(h),
			message::FromBlock::Number(n) => BlockId::Number(n),
		};
		let max = cmp::min(request.max.unwrap_or(u32::max_value()), MAX_BLOCK_DATA_RESPONSE) as usize;
		// TODO: receipts, etc.
		let get_header = request.fields.contains(message::BlockAttributes::HEADER);
		let get_body = request.fields.contains(message::BlockAttributes::BODY);
		let get_justification = request.fields.contains(message::BlockAttributes::JUSTIFICATION);
		while let Some(header) = self.context_data.chain.header(&id).unwrap_or(None) {
			if blocks.len() >= max {
				break;
			}
			let number = header.number().clone();
			let hash = header.hash();
			let justification = if get_justification { self.context_data.chain.justification(&BlockId::Hash(hash)).unwrap_or(None) } else { None };
			let block_data = message::generic::BlockData {
				hash: hash,
				header: if get_header { Some(header) } else { None },
				body: if get_body { self.context_data.chain.body(&BlockId::Hash(hash)).unwrap_or(None) } else { None },
				receipt: None,
				message_queue: None,
				justification,
			};
			blocks.push(block_data);
			match request.direction {
				message::Direction::Ascending => id = BlockId::Number(number + As::sa(1)),
				message::Direction::Descending => {
					if number == As::sa(0) {
						break;
					}
					id = BlockId::Number(number - As::sa(1))
				}
			}
		}
		let response = message::generic::BlockResponse {
			id: request.id,
			blocks: blocks,
		};
		trace!(target: "sync", "Sending BlockResponse with {} blocks", response.blocks.len());
		self.send_message(io, peer, GenericMessage::BlockResponse(response))
	}

	fn on_block_response(&self, io: &mut SyncIo, peer: NodeIndex, request: message::BlockRequest<B>, response: message::BlockResponse<B>) {
		// TODO: validate response
		let blocks_range = match (
				response.blocks.first().and_then(|b| b.header.as_ref().map(|h| h.number())),
				response.blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number())),
			) {
				(Some(first), Some(last)) if first != last => format!(" ({}..{})", first, last),
				(Some(first), Some(_)) => format!(" ({})", first),
				_ => Default::default(),
			};
		trace!(target: "sync", "BlockResponse {} from {} with {} blocks{}",
			response.id, peer, response.blocks.len(), blocks_range);

		// import_queue.import_blocks also acquires sync.write();
		// Break the cycle by doing these separately from the outside;
		let new_blocks = {
			let mut sync = self.sync.write();
			sync.on_block_data(&mut ProtocolContext::new(&self.context_data, io), peer, request, response)
		};

		if let Some((origin, new_blocks)) = new_blocks {
			let import_queue = self.sync.read().import_queue();
			import_queue.import_blocks(origin, new_blocks);
		}
	}

	fn on_block_justification_request(&self, io: &mut SyncIo, peer: NodeIndex, request: message::BlockJustificationRequest<B>) {
		trace!(target: "sync", "BlockJustificationRequest {} from {}: for {:?}", request.id, peer, request.block);
		let justification = self.context_data.chain.justification(&BlockId::Hash(request.block)).unwrap_or(None);
		let response = message::BlockJustificationResponse {
			id: request.id,
			justification,
		};
		trace!(target: "sync", "Sending BlockJustificationResponse {} for {:?}", request.id, request.block);
		self.send_message(io, peer, GenericMessage::BlockJustificationResponse(response))
	}

	fn on_block_justification_response(
		&self,
		io: &mut SyncIo,
		peer: NodeIndex,
		request: message::BlockJustificationRequest<B>,
		response: message::BlockJustificationResponse,
	) {
		let mut sync = self.sync.write();
		sync.on_block_justification_data(
			&mut ProtocolContext::new(&self.context_data, io),
			peer,
			request,
			response,
		);
	}

	/// Perform time based maintenance.
	pub fn tick(&self, io: &mut SyncIo) {
		self.consensus_gossip.write().collect_garbage(|_| true);
		self.maintain_peers(io);
		self.on_demand.as_ref().map(|s| s.maintain_peers(io));
	}

	fn maintain_peers(&self, io: &mut SyncIo) {
		let tick = time::Instant::now();
		let mut aborting = Vec::new();
		{
			let peers = self.context_data.peers.read();
			let handshaking_peers = self.handshaking_peers.read();
			for (who, timestamp) in peers.iter()
				.filter_map(|(id, peer)| peer.block_request_timestamp.as_ref().map(|r| (id, r)))
				.chain(handshaking_peers.iter()) {
				if (tick - *timestamp).as_secs() > REQUEST_TIMEOUT_SEC {
					trace!(target: "sync", "Timeout {}", who);
					aborting.push(*who);
				}
			}
		}

		self.specialization.write().maintain_peers(&mut ProtocolContext::new(&self.context_data, io));
		for p in aborting {
			io.report_peer(p, Severity::Timeout);
		}
	}

	#[allow(dead_code)]
	pub fn peer_info(&self, peer: NodeIndex) -> Option<PeerInfo<B>> {
		self.context_data.peers.read().get(&peer).map(|p| {
			PeerInfo {
				roles: p.roles,
				protocol_version: p.protocol_version,
				best_hash: p.best_hash,
				best_number: p.best_number,
			}
		})
	}

	/// Called by peer to report status
	fn on_status_message(&self, io: &mut SyncIo, who: NodeIndex, status: message::Status<B>) {
		trace!(target: "sync", "New peer {} {:?}", who, status);

		{
			let mut peers = self.context_data.peers.write();
			let mut handshaking_peers = self.handshaking_peers.write();
			if peers.contains_key(&who) {
				debug!(target: "sync", "Unexpected status packet from {}:{}", who, io.peer_debug_info(who));
				return;
			}
			if status.genesis_hash != self.genesis_hash {
				io.report_peer(who, Severity::Bad(&format!("Peer is on different chain (our genesis: {} theirs: {})", self.genesis_hash, status.genesis_hash)));
				return;
			}
			if status.version != CURRENT_VERSION {
				io.report_peer(who, Severity::Bad(&format!("Peer using unsupported protocol version {}", status.version)));
				return;
			}
			if self.config.roles & Roles::LIGHT == Roles::LIGHT {
				let self_best_block = self.context_data.chain.info().ok()
					.and_then(|info| info.best_queued_number)
					.unwrap_or_else(|| Zero::zero());
				let blocks_difference = self_best_block.as_().checked_sub(status.best_number.as_()).unwrap_or(0);
				if blocks_difference > LIGHT_MAXIMAL_BLOCKS_DIFFERENCE {
					io.report_peer(who, Severity::Useless("Peer is far behind us and will unable to serve light requests"));
					return;
				}
			}

			let peer = Peer {
				protocol_version: status.version,
				roles: status.roles,
				best_hash: status.best_hash,
				best_number: status.best_number,
				block_request: None,
				block_request_timestamp: None,
				block_justification_request: None,
				block_justification_request_timestamp: None,
				known_extrinsics: HashSet::new(),
				known_blocks: HashSet::new(),
				next_request_id: 0,
			};
			peers.insert(who.clone(), peer);
			handshaking_peers.remove(&who);
			debug!(target: "sync", "Connected {} {}", who, io.peer_debug_info(who));
		}

		let mut context = ProtocolContext::new(&self.context_data, io);
		self.on_demand.as_ref().map(|s| s.on_connect(who, status.roles, status.best_number));
		self.sync.write().new_peer(&mut context, who);
		self.consensus_gossip.write().new_peer(&mut context, who, status.roles);
		self.specialization.write().on_connect(&mut context, who, status);
	}

	/// Called when peer sends us new extrinsics
	fn on_extrinsics(&self, _io: &mut SyncIo, who: NodeIndex, extrinsics: message::Transactions<B::Extrinsic>) {
		// Accept extrinsics only when fully synced
		if self.sync.read().status().state != SyncState::Idle {
			trace!(target: "sync", "{} Ignoring extrinsics while syncing", who);
			return;
		}
		trace!(target: "sync", "Received {} extrinsics from {}", extrinsics.len(), who);
		let mut peers = self.context_data.peers.write();
		if let Some(ref mut peer) = peers.get_mut(&who) {
			for t in extrinsics {
				if let Some(hash) = self.transaction_pool.import(&t) {
					peer.known_extrinsics.insert(hash);
				} else {
					trace!(target: "sync", "Extrinsic rejected");
				}
			}
		}
	}

	/// Called when we propagate ready extrinsics to peers.
	pub fn propagate_extrinsics(&self, io: &mut SyncIo) {
		debug!(target: "sync", "Propagating extrinsics");

		// Accept transactions only when fully synced
		if self.sync.read().status().state != SyncState::Idle {
			return;
		}

		let extrinsics = self.transaction_pool.transactions();

		let mut propagated_to = HashMap::new();
		let mut peers = self.context_data.peers.write();
		for (who, ref mut peer) in peers.iter_mut() {
			let (hashes, to_send): (Vec<_>, Vec<_>) = extrinsics
				.iter()
				.filter(|&(ref hash, _)| peer.known_extrinsics.insert(hash.clone()))
				.cloned()
				.unzip();

			if !to_send.is_empty() {
				let node_id = io.peer_id(*who).map(|id| id.to_base58());
				if let Some(id) = node_id {
					for hash in hashes {
						propagated_to.entry(hash).or_insert_with(Vec::new).push(id.clone());
					}
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), who);
				self.send_message(io, *who, GenericMessage::Transactions(to_send));
			}
		}
		self.transaction_pool.on_broadcasted(propagated_to);
	}

	/// Send Status message
	fn send_status(&self, io: &mut SyncIo, who: NodeIndex) {
		if let Ok(info) = self.context_data.chain.info() {
			let status = message::generic::Status {
				version: CURRENT_VERSION,
				genesis_hash: info.chain.genesis_hash,
				roles: self.config.roles.into(),
				best_number: info.chain.best_number,
				best_hash: info.chain.best_hash,
				chain_status: self.specialization.read().status(),
			};
			self.send_message(io, who, GenericMessage::Status(status))
		}
	}

	pub fn abort(&self) {
		let mut sync = self.sync.write();
		let mut spec = self.specialization.write();
		let mut peers = self.context_data.peers.write();
		let mut handshaking_peers = self.handshaking_peers.write();
		let mut consensus_gossip = self.consensus_gossip.write();
		sync.clear();
		spec.on_abort();
		peers.clear();
		handshaking_peers.clear();
		consensus_gossip.abort();
	}

	pub fn stop(&self) {
		// stop processing import requests first (without holding a sync lock)
		let import_queue = self.sync.read().import_queue();
		import_queue.stop();

		// and then clear all the sync data
		self.abort();
	}

	pub fn on_block_announce(&self, io: &mut SyncIo, who: NodeIndex, announce: message::BlockAnnounce<B::Header>) {
		let header = announce.header;
		let hash = header.hash();
		{
			let mut peers = self.context_data.peers.write();
			if let Some(ref mut peer) = peers.get_mut(&who) {
				peer.known_blocks.insert(hash.clone());
			}
		}
		self.on_demand.as_ref().map(|s| s.on_block_announce(who, *header.number()));
		self.sync.write().on_block_announce(&mut ProtocolContext::new(&self.context_data, io), who, hash, &header);
	}

	pub fn on_block_imported(&self, io: &mut SyncIo, hash: B::Hash, header: &B::Header) {
		self.sync.write().update_chain_info(&header);
		self.specialization.write().on_block_imported(
			&mut ProtocolContext::new(&self.context_data, io),
			hash.clone(),
			header
		);

		// blocks are not announced by light clients
		if self.config.roles & Roles::LIGHT == Roles::LIGHT {
			return;
		}

		// send out block announcements
		let mut peers = self.context_data.peers.write();

		for (who, ref mut peer) in peers.iter_mut() {
			if peer.known_blocks.insert(hash.clone()) {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, who);
				self.send_message(io, *who, GenericMessage::BlockAnnounce(message::BlockAnnounce {
					header: header.clone()
				}));
			}
		}
	}

	pub fn on_block_finalized(&self, _io: &mut SyncIo, hash: B::Hash, header: &B::Header) {
		self.sync.write().block_finalized(&hash, *header.number());
	}

	fn on_remote_call_request(&self, io: &mut SyncIo, who: NodeIndex, request: message::RemoteCallRequest<B::Hash>) {
		trace!(target: "sync", "Remote call request {} from {} ({} at {})", request.id, who, request.method, request.block);
		let proof = match self.context_data.chain.execution_proof(&request.block, &request.method, &request.data) {
			Ok((_, proof)) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote call request {} from {} ({} at {}) failed with: {}",
					request.id, who, request.method, request.block, error);
				Default::default()
			},
		};

		self.send_message(io, who, GenericMessage::RemoteCallResponse(message::RemoteCallResponse {
			id: request.id, proof,
		}));
	}

	fn on_remote_call_response(&self, io: &mut SyncIo, who: NodeIndex, response: message::RemoteCallResponse) {
		trace!(target: "sync", "Remote call response {} from {}", response.id, who);
		self.on_demand.as_ref().map(|s| s.on_remote_call_response(io, who, response));
	}

	fn on_remote_read_request(&self, io: &mut SyncIo, who: NodeIndex, request: message::RemoteReadRequest<B::Hash>) {
		trace!(target: "sync", "Remote read request {} from {} ({} at {})",
			request.id, who, request.key.to_hex(), request.block);
		let proof = match self.context_data.chain.read_proof(&request.block, &request.key) {
			Ok(proof) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote read request {} from {} ({} at {}) failed with: {}",
					request.id, who, request.key.to_hex(), request.block, error);
				Default::default()
			},
		};
		self.send_message(io, who, GenericMessage::RemoteReadResponse(message::RemoteReadResponse {
			id: request.id, proof,
		}));
	}
	fn on_remote_read_response(&self, io: &mut SyncIo, who: NodeIndex, response: message::RemoteReadResponse) {
		trace!(target: "sync", "Remote read response {} from {}", response.id, who);
		self.on_demand.as_ref().map(|s| s.on_remote_read_response(io, who, response));
	}

	fn on_remote_header_request(&self, io: &mut SyncIo, who: NodeIndex, request: message::RemoteHeaderRequest<NumberFor<B>>) {
		trace!(target: "sync", "Remote header proof request {} from {} ({})",
			request.id, who, request.block);
		let (header, proof) = match self.context_data.chain.header_proof(request.block) {
			Ok((header, proof)) => (Some(header), proof),
			Err(error) => {
				trace!(target: "sync", "Remote header proof request {} from {} ({}) failed with: {}",
					request.id, who, request.block, error);
				(Default::default(), Default::default())
			},
		};
 		self.send_message(io, who, GenericMessage::RemoteHeaderResponse(message::RemoteHeaderResponse {
			id: request.id, header, proof,
		}));
	}

 	fn on_remote_header_response(&self, io: &mut SyncIo, who: NodeIndex, response: message::RemoteHeaderResponse<B::Header>) {
		trace!(target: "sync", "Remote header proof response {} from {}", response.id, who);
		self.on_demand.as_ref().map(|s| s.on_remote_header_response(io, who, response));
	}

	fn on_remote_changes_request(&self, io: &mut SyncIo, who: NodeIndex, request: message::RemoteChangesRequest<B::Hash>) {
		trace!(target: "sync", "Remote changes proof request {} from {} for key {} ({}..{})",
			request.id, who, request.key.to_hex(), request.first, request.last);
		let proof = match self.context_data.chain.key_changes_proof(request.first, request.last, request.min, request.max, &request.key) {
			Ok(proof) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote changes proof request {} from {} for key {} ({}..{}) failed with: {}",
					request.id, who, request.key.to_hex(), request.first, request.last, error);
				ChangesProof::<B::Header> {
					max_block: Zero::zero(),
					proof: vec![],
					roots: BTreeMap::new(),
					roots_proof: vec![],
				}
			},
		};
 		self.send_message(io, who, GenericMessage::RemoteChangesResponse(message::RemoteChangesResponse {
			id: request.id,
			max: proof.max_block,
			proof: proof.proof,
			roots: proof.roots.into_iter().collect(),
			roots_proof: proof.roots_proof,
		}));
	}

 	fn on_remote_changes_response(&self, io: &mut SyncIo, who: NodeIndex, response: message::RemoteChangesResponse<NumberFor<B>, B::Hash>) {
		trace!(target: "sync", "Remote changes proof response {} from {} (max={})",
			response.id, who, response.max);
		self.on_demand.as_ref().map(|s| s.on_remote_changes_response(io, who, response));
	}


	/// Execute a closure with access to a network context and specialization.
	pub fn with_spec<F, U>(&self, io: &mut SyncIo, f: F) -> U
		where F: FnOnce(&mut S, &mut Context<B>) -> U
	{
		f(&mut* self.specialization.write(), &mut ProtocolContext::new(&self.context_data, io))
	}
}

fn send_message<B: BlockT, H: ExHashT>(peers: &RwLock<HashMap<NodeIndex, Peer<B, H>>>, io: &mut SyncIo, who: NodeIndex, mut message: Message<B>) {
	match message {
		GenericMessage::BlockRequest(ref mut r) => {
			let mut peers = peers.write();
			if let Some(ref mut peer) = peers.get_mut(&who) {
				r.id = peer.next_request_id;
				peer.next_request_id = peer.next_request_id + 1;
				peer.block_request = Some(r.clone());
				peer.block_request_timestamp = Some(time::Instant::now());
			}
		},
		GenericMessage::BlockJustificationRequest(ref mut r) => {
			let mut peers = peers.write();
			if let Some(ref mut peer) = peers.get_mut(&who) {
				r.id = peer.next_request_id;
				peer.next_request_id = peer.next_request_id + 1;
				peer.block_justification_request = Some(r.clone());
				peer.block_justification_request_timestamp = Some(time::Instant::now());
			}
		},
		_ => (),
	}
	io.send(who, message.encode());
}

/// Construct a simple protocol that is composed of several sub protocols.
/// Each "sub protocol" needs to implement `Specialization` and needs to provide a `new()` function.
/// For more fine grained implementations, this macro is not usable.
///
/// # Example
///
/// ```nocompile
/// construct_simple_protocol! {
///     pub struct MyProtocol where Block = MyBlock {
///         consensus_gossip: ConsensusGossip<MyBlock>,
///         other_protocol: MyCoolStuff,
///     }
/// }
/// ```
///
/// You can also provide an optional parameter after `where Block = MyBlock`, so it looks like
/// `where Block = MyBlock, Status = consensus_gossip`. This will instruct the implementation to
/// use the `status()` function from the `ConsensusGossip` protocol. By default, `status()` returns
/// an empty vector.
#[macro_export]
macro_rules! construct_simple_protocol {
	(
		$( #[ $attr:meta ] )*
		pub struct $protocol:ident where
			Block = $block:ident
			$( , Status = $status_protocol_name:ident )*
		{
			$( $sub_protocol_name:ident : $sub_protocol:ident $( <$protocol_block:ty> )*, )*
		}
	) => {
		$( #[$attr] )*
		pub struct $protocol {
			$( $sub_protocol_name: $sub_protocol $( <$protocol_block> )*, )*
		}

		impl $protocol {
			/// Instantiate a node protocol handler.
			pub fn new() -> Self {
				Self {
					$( $sub_protocol_name: $sub_protocol::new(), )*
				}
			}
		}

		impl $crate::specialization::NetworkSpecialization<$block> for $protocol {
			fn status(&self) -> Vec<u8> {
				$(
					let status = self.$status_protocol_name.status();

					if !status.is_empty() {
						return status;
					}
				)*

				Vec::new()
			}

			fn on_connect(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::NodeIndex,
				_status: $crate::StatusMessage<$block>
			) {
				$( self.$sub_protocol_name.on_connect(_ctx, _who, _status); )*
			}

			fn on_disconnect(&mut self, _ctx: &mut $crate::Context<$block>, _who: $crate::NodeIndex) {
				$( self.$sub_protocol_name.on_disconnect(_ctx, _who); )*
			}

			fn on_message(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::NodeIndex,
				_message: &mut Option<$crate::message::Message<$block>>
			) {
				$( self.$sub_protocol_name.on_message(_ctx, _who, _message); )*
			}

			fn on_abort(&mut self) {
				$( self.$sub_protocol_name.on_abort(); )*
			}

			fn maintain_peers(&mut self, _ctx: &mut $crate::Context<$block>) {
				$( self.$sub_protocol_name.maintain_peers(_ctx); )*
			}

			fn on_block_imported(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_hash: <$block as $crate::BlockT>::Hash,
				_header: &<$block as $crate::BlockT>::Header
			) {
				$( self.$sub_protocol_name.on_block_imported(_ctx, _hash, _header); )*
			}
		}
	}
}
