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
use serde_json;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash, HashFor, As};
use runtime_primitives::generic::BlockId;
use network::PeerId;

use message::{self, Message};
use message::generic::Message as GenericMessage;
use specialization::Specialization;
use sync::{ChainSync, Status as SyncStatus, SyncState};
use service::{Role, TransactionPool};
use config::ProtocolConfig;
use chain::Client;
use on_demand::OnDemandService;
use io::SyncIo;
use error;

const REQUEST_TIMEOUT_SEC: u64 = 40;

/// Current protocol version.
pub (crate) const CURRENT_VERSION: u32 = 0;
/// Current packet count.
pub (crate) const CURRENT_PACKET_COUNT: u8 = 1;


// Maximum allowed entries in `BlockResponse`
const MAX_BLOCK_DATA_RESPONSE: u32 = 128;

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, S: Specialization<B>> {
	config: ProtocolConfig,
	on_demand: Option<Arc<OnDemandService<B>>>,
	genesis_hash: B::Hash,
	sync: RwLock<ChainSync<B>>,
	specialization: RwLock<S>,
	context_data: ContextData<B>,
	// Connected peers pending Status message.
	handshaking_peers: RwLock<HashMap<PeerId, time::Instant>>,
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
	roles: Role,
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
	pub roles: Role,
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

	/// Disable a peer
	fn disable_peer(&mut self, peer_id: PeerId);

	/// Disconnect peer
	fn disconnect_peer(&mut self, peer_id: PeerId);

	/// Get peer info.
	fn peer_info(&self, peer: PeerId) -> Option<PeerInfo<B>>;

	/// Send a message to a peer.
	fn send_message(&mut self, peer_id: PeerId, data: ::message::Message<B>);
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
	pub fn send_message(&mut self, peer_id: PeerId, message: Message<B>) {
		send_message(&self.context_data.peers, self.io, peer_id, message)
	}

	pub fn disable_peer(&mut self, peer_id: PeerId) {
		self.io.disable_peer(peer_id);
	}

	pub fn disconnect_peer(&mut self, peer_id: PeerId) {
		self.io.disconnect_peer(peer_id)
	}

	/// Get peer info.
	pub fn peer_info(&self, peer: PeerId) -> Option<PeerInfo<B>> {
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
	fn send_message(&mut self, peer_id: PeerId, message: Message<B>) {
		ProtocolContext::send_message(self, peer_id, message);
	}

	fn disable_peer(&mut self, peer_id: PeerId) {
		ProtocolContext::disable_peer(self, peer_id);
	}

	fn disconnect_peer(&mut self, peer_id: PeerId) {
		ProtocolContext::disconnect_peer(self, peer_id);
	}

	fn peer_info(&self, peer_id: PeerId) -> Option<PeerInfo<B>> {
		ProtocolContext::peer_info(self, peer_id)
	}

	fn client(&self) -> &Client<B> {
		&*self.context_data.chain
	}
}

/// Data necessary to create a context.
pub(crate) struct ContextData<B: BlockT> {
	// All connected peers
	peers: RwLock<HashMap<PeerId, Peer<B>>>,
	chain: Arc<Client<B>>,
}

impl<B: BlockT, S: Specialization<B>> Protocol<B, S> {
	/// Create a new instance.
	pub fn new(
		config: ProtocolConfig,
		chain: Arc<Client<B>>,
		on_demand: Option<Arc<OnDemandService<B>>>,
		transaction_pool: Arc<TransactionPool<B>>,
		specialization: S,
	) -> error::Result<Self>  {
		let info = chain.info()?;
		let sync = ChainSync::new(config.roles, &info);
		let protocol = Protocol {
			config: config,
			context_data: ContextData {
				peers: RwLock::new(HashMap::new()),
				chain,
			},
			on_demand,
			genesis_hash: info.chain.genesis_hash,
			sync: RwLock::new(sync),
			specialization: RwLock::new(specialization),
			handshaking_peers: RwLock::new(HashMap::new()),
			transaction_pool: transaction_pool,
		};
		Ok(protocol)
	}

	pub(crate) fn context_data(&self) -> &ContextData<B> {
		&self.context_data
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

	pub fn handle_packet(&self, io: &mut SyncIo, peer_id: PeerId, data: &[u8]) {
		let message: Message<B> = match serde_json::from_slice(data) {
			Ok(m) => m,
			Err(e) => {
				debug!(target: "sync", "Invalid packet from {}: {}", peer_id, e);
				trace!(target: "sync", "Invalid packet: {}", String::from_utf8_lossy(data));
				io.disable_peer(peer_id);
				return;
			}
		};

		match message {
			GenericMessage::Status(s) => self.on_status_message(io, peer_id, s),
			GenericMessage::BlockRequest(r) => self.on_block_request(io, peer_id, r),
			GenericMessage::BlockResponse(r) => {
				let request = {
					let mut peers = self.context_data.peers.write();
					if let Some(ref mut peer) = peers.get_mut(&peer_id) {
						peer.request_timestamp = None;
						match mem::replace(&mut peer.block_request, None) {
							Some(r) => r,
							None => {
								debug!(target: "sync", "Unexpected response packet from {}", peer_id);
								io.disable_peer(peer_id);
								return;
							}
						}
					} else {
						debug!(target: "sync", "Unexpected packet from {}", peer_id);
						io.disable_peer(peer_id);
						return;
					}
				};
				if request.id != r.id {
					trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} got {})", peer_id, request.id, r.id);
					return;
				}
				self.on_block_response(io, peer_id, request, r);
			},
			GenericMessage::BlockAnnounce(announce) => self.on_block_announce(io, peer_id, announce),
			GenericMessage::Transactions(m) => self.on_extrinsics(io, peer_id, m),
			GenericMessage::RemoteCallRequest(request) => self.on_remote_call_request(io, peer_id, request),
			GenericMessage::RemoteCallResponse(response) => self.on_remote_call_response(io, peer_id, response),
			other => self.specialization.write().on_message(&mut ProtocolContext::new(&self.context_data, io), peer_id, other),
		}
	}

	pub fn send_message(&self, io: &mut SyncIo, peer_id: PeerId, message: Message<B>) {
		send_message::<B>(&self.context_data.peers, io, peer_id, message)
	}

	/// Called when a new peer is connected
	pub fn on_peer_connected(&self, io: &mut SyncIo, peer_id: PeerId) {
		trace!(target: "sync", "Connected {}: {}", peer_id, io.peer_info(peer_id));
		self.handshaking_peers.write().insert(peer_id, time::Instant::now());
		self.send_status(io, peer_id);
	}

	/// Called by peer when it is disconnecting
	pub fn on_peer_disconnected(&self, io: &mut SyncIo, peer: PeerId) {
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

	fn on_block_request(&self, io: &mut SyncIo, peer: PeerId, request: message::BlockRequest<B>) {
		trace!(target: "sync", "BlockRequest {} from {}: from {:?} to {:?} max {:?}", request.id, peer, request.from, request.to, request.max);
		let mut blocks = Vec::new();
		let mut id = match request.from {
			message::FromBlock::Hash(h) => BlockId::Hash(h),
			message::FromBlock::Number(n) => BlockId::Number(n),
		};
		let max = cmp::min(request.max.unwrap_or(u32::max_value()), MAX_BLOCK_DATA_RESPONSE) as usize;
		// TODO: receipts, etc.
		let (mut get_header, mut get_body, mut get_justification) = (false, false, false);
		for a in request.fields {
			match a {
				message::BlockAttribute::Header => get_header = true,
				message::BlockAttribute::Body => get_body = true,
				message::BlockAttribute::Receipt => unimplemented!(),
				message::BlockAttribute::MessageQueue => unimplemented!(),
				message::BlockAttribute::Justification => get_justification = true,
			}
		}
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
				body: (if get_body { self.context_data.chain.body(&BlockId::Hash(hash)).unwrap_or(None) } else { None }).map(|body| message::Body::Extrinsics(body)),
				receipt: None,
				message_queue: None,
				justification: justification.map(|j| message::generic::BlockJustification::V2(j)),
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

	fn on_block_response(&self, io: &mut SyncIo, peer: PeerId, request: message::BlockRequest<B>, response: message::BlockResponse<B>) {
		// TODO: validate response
		trace!(target: "sync", "BlockResponse {} from {} with {} blocks", response.id, peer, response.blocks.len());
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
			for (peer_id, timestamp) in peers.iter()
				.filter_map(|(id, peer)| peer.request_timestamp.as_ref().map(|r| (id, r)))
				.chain(handshaking_peers.iter()) {
				if (tick - *timestamp).as_secs() > REQUEST_TIMEOUT_SEC {
					trace!(target: "sync", "Timeout {}", peer_id);
					io.disconnect_peer(*peer_id);
					aborting.push(*peer_id);
				}
			}
		}

		self.specialization.write().maintain_peers(&mut ProtocolContext::new(&self.context_data, io));
		for p in aborting {
			self.on_peer_disconnected(io, p);
		}
	}

	pub fn peer_info(&self, peer: PeerId) -> Option<PeerInfo<B>> {
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
	fn on_status_message(&self, io: &mut SyncIo, peer_id: PeerId, status: message::Status<B>) {
		trace!(target: "sync", "New peer {} {:?}", peer_id, status);
		if io.is_expired() {
			trace!(target: "sync", "Status packet from expired session {}:{}", peer_id, io.peer_info(peer_id));
			return;
		}

		{
			let mut peers = self.context_data.peers.write();
			let mut handshaking_peers = self.handshaking_peers.write();
			if peers.contains_key(&peer_id) {
				debug!(target: "sync", "Unexpected status packet from {}:{}", peer_id, io.peer_info(peer_id));
				return;
			}
			if status.genesis_hash != self.genesis_hash {
				io.disable_peer(peer_id);
				trace!(target: "sync", "Peer {} genesis hash mismatch (ours: {}, theirs: {})", peer_id, self.genesis_hash, status.genesis_hash);
				return;
			}
			if status.version != CURRENT_VERSION {
				io.disable_peer(peer_id);
				trace!(target: "sync", "Peer {} unsupported eth protocol ({})", peer_id, status.version);
				return;
			}

			let peer = Peer {
				protocol_version: status.version,
				roles: message::Role::as_flags(&status.roles),
				best_hash: status.best_hash,
				best_number: status.best_number,
				block_request: None,
				request_timestamp: None,
				known_extrinsics: HashSet::new(),
				known_blocks: HashSet::new(),
				next_request_id: 0,
			};
			peers.insert(peer_id.clone(), peer);
			handshaking_peers.remove(&peer_id);
			debug!(target: "sync", "Connected {} {}", peer_id, io.peer_info(peer_id));
		}

		let mut context = ProtocolContext::new(&self.context_data, io);
		self.sync.write().new_peer(&mut context, peer_id);
		self.specialization.write().on_connect(&mut context, peer_id, status.clone());
		self.on_demand.as_ref().map(|s| s.on_connect(peer_id, message::Role::as_flags(&status.roles)));
	}

	/// Called when peer sends us new extrinsics
	fn on_extrinsics(&self, _io: &mut SyncIo, peer_id: PeerId, extrinsics: message::Transactions<B::Extrinsic>) {
		// Accept extrinsics only when fully synced
		if self.sync.read().status().state != SyncState::Idle {
			trace!(target: "sync", "{} Ignoring extrinsics while syncing", peer_id);
			return;
		}
		trace!(target: "sync", "Received {} extrinsics from {}", extrinsics.len(), peer_id);
		let mut peers = self.context_data.peers.write();
		if let Some(ref mut peer) = peers.get_mut(&peer_id) {
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
		for (peer_id, ref mut peer) in peers.iter_mut() {
			let (hashes, to_send): (Vec<_>, Vec<_>) = extrinsics
				.iter()
				.cloned()
				.filter(|&(hash, _)| peer.known_extrinsics.insert(hash))
				.unzip();

			if !to_send.is_empty() {
				let node_id = io.peer_session_info(*peer_id).map(|info| match info.id {
					Some(id) => format!("{}@{:x}", info.remote_address, id),
					None => info.remote_address.clone(),
				});

				if let Some(id) = node_id {
					for hash in hashes {
						propagated_to.entry(hash).or_insert_with(Vec::new).push(id.clone());
					}
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), peer_id);
				self.send_message(io, *peer_id, GenericMessage::Transactions(to_send));
			}
		}
		self.transaction_pool.on_broadcasted(propagated_to);
	}

	/// Send Status message
	fn send_status(&self, io: &mut SyncIo, peer_id: PeerId) {
		if let Ok(info) = self.context_data.chain.info() {
			let status = message::generic::Status {
				version: CURRENT_VERSION,
				genesis_hash: info.chain.genesis_hash,
				roles: self.config.roles.into(),
				best_number: info.chain.best_number,
				best_hash: info.chain.best_hash,
				chain_status: self.specialization.read().status(),

				parachain_id: None,
				validator_id: None,
				validator_signature: None,
			};
			self.send_message(io, peer_id, GenericMessage::Status(status))
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

	pub fn on_block_announce(&self, io: &mut SyncIo, peer_id: PeerId, announce: message::BlockAnnounce<B::Header>) {
		let header = announce.header;
		let hash = header.hash();
		{
			let mut peers = self.context_data.peers.write();
			if let Some(ref mut peer) = peers.get_mut(&peer_id) {
				peer.known_blocks.insert(hash.clone());
			}
		}
		self.sync.write().on_block_announce(&mut ProtocolContext::new(&self.context_data, io), peer_id, hash, &header);
	}

	pub fn on_block_imported(&self, io: &mut SyncIo, hash: B::Hash, header: &B::Header) {
		self.sync.write().update_chain_info(&header);
		self.specialization.write().on_block_imported(
			&mut ProtocolContext::new(&self.context_data, io),
			hash.clone(),
			header
		);

		// blocks are not announced by light clients
		if self.config.roles & Role::LIGHT == Role::LIGHT {
			return;
		}

		// send out block announcements
		let mut peers = self.context_data.peers.write();

		for (peer_id, ref mut peer) in peers.iter_mut() {
			if peer.known_blocks.insert(hash.clone()) {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, peer_id);
				self.send_message(io, *peer_id, GenericMessage::BlockAnnounce(message::BlockAnnounce {
					header: header.clone()
				}));
			}
		}
	}

	fn on_remote_call_request(&self, io: &mut SyncIo, peer_id: PeerId, request: message::RemoteCallRequest<B::Hash>) {
		trace!(target: "sync", "Remote call request {} from {} ({} at {})", request.id, peer_id, request.method, request.block);
		let proof = match self.context_data.chain.execution_proof(&request.block, &request.method, &request.data) {
			Ok((_, proof)) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote call request {} from {} ({} at {}) failed with: {}",
					request.id, peer_id, request.method, request.block, error);
				Default::default()
			},
		};

		self.send_message(io, peer_id, GenericMessage::RemoteCallResponse(message::RemoteCallResponse {
			id: request.id, proof,
		}));
	}

	fn on_remote_call_response(&self, io: &mut SyncIo, peer_id: PeerId, response: message::RemoteCallResponse) {
		trace!(target: "sync", "Remote call response {} from {}", response.id, peer_id);
		self.on_demand.as_ref().map(|s| s.on_remote_call_response(io, peer_id, response));
	}

	/// Execute a closure with access to a network context and specialization.
	pub fn with_spec<F, U>(&self, io: &mut SyncIo, f: F) -> U
		where F: FnOnce(&mut S, &mut Context<B>) -> U
	{
		f(&mut* self.specialization.write(), &mut ProtocolContext::new(&self.context_data, io))
	}
}

fn send_message<B: BlockT>(peers: &RwLock<HashMap<PeerId, Peer<B>>>, io: &mut SyncIo, peer_id: PeerId, mut message: Message<B>) {
	match &mut message {
		&mut GenericMessage::BlockRequest(ref mut r) => {
			let mut peers = peers.write();
			if let Some(ref mut peer) = peers.get_mut(&peer_id) {
				r.id = peer.next_request_id;
				peer.next_request_id = peer.next_request_id + 1;
				peer.block_request = Some(r.clone());
				peer.request_timestamp = Some(time::Instant::now());
			}
		},
		_ => (),
	}
	let data = serde_json::to_vec(&message).expect("Serializer is infallible; qed");
	if let Err(e) = io.send(peer_id, data) {
		debug!(target:"sync", "Error sending message: {:?}", e);
		io.disconnect_peer(peer_id);
	}
}

/// Hash a message.
pub(crate) fn hash_message<B: BlockT>(message: &Message<B>) -> B::Hash {
	let data = serde_json::to_vec(&message).expect("Serializer is infallible; qed");
	HashFor::<B>::hash(&data)
}
