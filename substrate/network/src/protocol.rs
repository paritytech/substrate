// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use std::collections::{HashMap, HashSet};
use std::{mem, cmp};
use std::sync::Arc;
use std::time;
use parking_lot::RwLock;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash, HashFor, As};
use runtime_primitives::generic::BlockId;
use network_libp2p::{NodeIndex, Severity};
use codec::{Encode, Decode};

use message::{self, Message};
use message::generic::Message as GenericMessage;
use specialization::Specialization;
use sync::{ChainSync, Status as SyncStatus, SyncState};
use service::{Roles, TransactionPool};
use import_queue::ImportQueue;
use config::ProtocolConfig;
use chain::Client;
use on_demand::OnDemandService;
use io::SyncIo;
use error;

const REQUEST_TIMEOUT_SEC: u64 = 40;

/// Current protocol version.
pub (crate) const CURRENT_VERSION: u32 = 1;
/// Current packet count.
pub (crate) const CURRENT_PACKET_COUNT: u8 = 1;

// Maximum allowed entries in `BlockResponse`
const MAX_BLOCK_DATA_RESPONSE: u32 = 128;

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, S: Specialization<B>> {
	config: ProtocolConfig,
	on_demand: Option<Arc<OnDemandService<B>>>,
	genesis_hash: B::Hash,
	sync: Arc<RwLock<ChainSync<B>>>,
	specialization: RwLock<S>,
	context_data: ContextData<B>,
	// Connected peers pending Status message.
	handshaking_peers: RwLock<HashMap<NodeIndex, time::Instant>>,
	transaction_pool: Arc<TransactionPool<B>>,
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
struct Peer<B: BlockT> {
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
	/// Request timestamp
	request_timestamp: Option<time::Instant>,
	/// Holds a set of transactions known to this peer.
	known_extrinsics: HashSet<B::Hash>,
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
pub(crate) struct ProtocolContext<'a, B: 'a + BlockT> {
	io: &'a mut SyncIo,
	context_data: &'a ContextData<B>,
}

impl<'a, B: BlockT + 'a> ProtocolContext<'a, B> {
	pub(crate) fn new(context_data: &'a ContextData<B>, io: &'a mut SyncIo) -> Self {
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

impl<'a, B: BlockT + 'a> Context<B> for ProtocolContext<'a, B> {
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
pub(crate) struct ContextData<B: BlockT> {
	// All connected peers
	peers: RwLock<HashMap<NodeIndex, Peer<B>>>,
	chain: Arc<Client<B>>,
}

impl<B: BlockT, S: Specialization<B>> Protocol<B, S> {
	/// Create a new instance.
	pub fn new(
		config: ProtocolConfig,
		chain: Arc<Client<B>>,
		import_queue: Arc<ImportQueue<B>>,
		on_demand: Option<Arc<OnDemandService<B>>>,
		transaction_pool: Arc<TransactionPool<B>>,
		specialization: S,
	) -> error::Result<Self>  {
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
			handshaking_peers: RwLock::new(HashMap::new()),
			transaction_pool: transaction_pool,
		};
		Ok(protocol)
	}

	pub(crate) fn context_data(&self) -> &ContextData<B> {
		&self.context_data
	}

	pub(crate) fn sync(&self) -> &Arc<RwLock<ChainSync<B>>> {
		&self.sync
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

	pub fn handle_packet(&self, io: &mut SyncIo, who: NodeIndex, mut data: &[u8]) {
		let message: Message<B> = match Decode::decode(&mut data) {
			Some(m) => m,
			None => {
				trace!(target: "sync", "Invalid packet from {}", who);
				io.report_peer(who, Severity::Bad("Peer sent us a packet with invalid format"));
				return;
			}
		};

		match message {
			GenericMessage::Status(s) => self.on_status_message(io, who, s),
			GenericMessage::BlockRequest(r) => self.on_block_request(io, who, r),
			GenericMessage::BlockResponse(r) => {
				let request = {
					let mut peers = self.context_data.peers.write();
					if let Some(ref mut peer) = peers.get_mut(&who) {
						peer.request_timestamp = None;
						match mem::replace(&mut peer.block_request, None) {
							Some(r) => r,
							None => {
								io.report_peer(who, Severity::Bad("Unexpected response packet received from peer"));
								return;
							}
						}
					} else {
						io.report_peer(who, Severity::Bad("Unexpected packet received from peer"));
						return;
					}
				};
				if request.id != r.id {
					trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} got {})", who, request.id, r.id);
					return;
				}
				self.on_block_response(io, who, request, r);
			},
			GenericMessage::BlockAnnounce(announce) => self.on_block_announce(io, who, announce),
			GenericMessage::Transactions(m) => self.on_extrinsics(io, who, m),
			GenericMessage::RemoteCallRequest(request) => self.on_remote_call_request(io, who, request),
			GenericMessage::RemoteCallResponse(response) => self.on_remote_call_response(io, who, response),
			other => self.specialization.write().on_message(&mut ProtocolContext::new(&self.context_data, io), who, other),
		}
	}

	pub fn send_message(&self, io: &mut SyncIo, who: NodeIndex, message: Message<B>) {
		send_message::<B>(&self.context_data.peers, io, who, message)
	}

	/// Called when a new peer is connected
	pub fn on_peer_connected(&self, io: &mut SyncIo, who: NodeIndex) {
		trace!(target: "sync", "Connected {}: {}", who, io.peer_info(who));
		self.handshaking_peers.write().insert(who, time::Instant::now());
		self.send_status(io, who);
	}

	/// Called by peer when it is disconnecting
	pub fn on_peer_disconnected(&self, io: &mut SyncIo, peer: NodeIndex) {
		trace!(target: "sync", "Disconnecting {}: {}", peer, io.peer_info(peer));

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
			if blocks.len() >= max{
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

		self.sync.write().on_block_data(&mut ProtocolContext::new(&self.context_data, io), peer, request, response);
	}

	/// Perform time based maintenance.
	pub fn tick(&self, io: &mut SyncIo) {
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
				.filter_map(|(id, peer)| peer.request_timestamp.as_ref().map(|r| (id, r)))
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
		if io.is_expired() {
			trace!(target: "sync", "Status packet from expired session {}:{}", who, io.peer_info(who));
			return;
		}

		{
			let mut peers = self.context_data.peers.write();
			let mut handshaking_peers = self.handshaking_peers.write();
			if peers.contains_key(&who) {
				debug!(target: "sync", "Unexpected status packet from {}:{}", who, io.peer_info(who));
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

			let peer = Peer {
				protocol_version: status.version,
				roles: status.roles,
				best_hash: status.best_hash,
				best_number: status.best_number,
				block_request: None,
				request_timestamp: None,
				known_extrinsics: HashSet::new(),
				known_blocks: HashSet::new(),
				next_request_id: 0,
			};
			peers.insert(who.clone(), peer);
			handshaking_peers.remove(&who);
			debug!(target: "sync", "Connected {} {}", who, io.peer_info(who));
		}

		let mut context = ProtocolContext::new(&self.context_data, io);
		self.sync.write().new_peer(&mut context, who);
		self.specialization.write().on_connect(&mut context, who, status.clone());
		self.on_demand.as_ref().map(|s| s.on_connect(who, status.roles));
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
				.cloned()
				.filter(|&(hash, _)| peer.known_extrinsics.insert(hash))
				.unzip();

			if !to_send.is_empty() {
				let node_id = io.peer_session_info(*who).map(|info| match info.id {
					Some(id) => format!("{}@{:x}", info.remote_address, id),
					None => info.remote_address.clone(),
				});

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
		sync.clear();
		spec.on_abort();
		peers.clear();
		handshaking_peers.clear();
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

	/// Execute a closure with access to a network context and specialization.
	pub fn with_spec<F, U>(&self, io: &mut SyncIo, f: F) -> U
		where F: FnOnce(&mut S, &mut Context<B>) -> U
	{
		f(&mut* self.specialization.write(), &mut ProtocolContext::new(&self.context_data, io))
	}
}

fn send_message<B: BlockT>(peers: &RwLock<HashMap<NodeIndex, Peer<B>>>, io: &mut SyncIo, who: NodeIndex, mut message: Message<B>) {
	match &mut message {
		&mut GenericMessage::BlockRequest(ref mut r) => {
			let mut peers = peers.write();
			if let Some(ref mut peer) = peers.get_mut(&who) {
				r.id = peer.next_request_id;
				peer.next_request_id = peer.next_request_id + 1;
				peer.block_request = Some(r.clone());
				peer.request_timestamp = Some(time::Instant::now());
			}
		},
		_ => (),
	}
	io.send(who, message.encode());
}

/// Hash a message.
pub(crate) fn hash_message<B: BlockT>(message: &Message<B>) -> B::Hash {
	let data = message.encode();
	HashFor::<B>::hash(&data)
}
