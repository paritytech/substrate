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

use std::collections::{HashMap, HashSet, BTreeMap};
use std::{mem, cmp};
use std::sync::Arc;
use std::time;
use parking_lot::{RwLock, Mutex};
use futures::sync::oneshot;
use serde_json;
use primitives::block::{HeaderHash, ExtrinsicHash, Number as BlockNumber, Header, Id as BlockId};
use primitives::{Hash, blake2_256};
use runtime_support::Hashable;
use network::{PeerId, NodeId};

use message::{self, Message};
use sync::{ChainSync, Status as SyncStatus, SyncState};
use consensus::Consensus;
use service::{Role, TransactionPool, StatementStream, BftMessageStream};
use config::ProtocolConfig;
use chain::Client;
use io::SyncIo;
use error;
use super::header_hash;

const REQUEST_TIMEOUT_SEC: u64 = 15;
const PROTOCOL_VERSION: u32 = 0;

// Maximum allowed entries in `BlockResponse`
const MAX_BLOCK_DATA_RESPONSE: u32 = 128;

// Lock must always be taken in order declared here.
pub struct Protocol {
	config: ProtocolConfig,
	chain: Arc<Client>,
	genesis_hash: HeaderHash,
	sync: RwLock<ChainSync>,
	consensus: Mutex<Consensus>,
	// All connected peers
	peers: RwLock<HashMap<PeerId, Peer>>,
	// Connected peers pending Status message.
	handshaking_peers: RwLock<HashMap<PeerId, time::Instant>>,
	transaction_pool: Arc<TransactionPool>,
}

/// Syncing status and statistics
#[derive(Clone)]
pub struct ProtocolStatus {
	/// Sync status.
	pub sync: SyncStatus,
	/// Total number of connected peers
	pub num_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
}

/// Peer information
struct Peer {
	/// Protocol version
	protocol_version: u32,
	/// Roles
	roles: Role,
	/// Peer best block hash
	best_hash: HeaderHash,
	/// Peer best block number
	best_number: BlockNumber,
	/// Pending block request if any
	block_request: Option<message::BlockRequest>,
	/// Request timestamp
	request_timestamp: Option<time::Instant>,
	/// Holds a set of transactions known to this peer.
	known_transactions: HashSet<ExtrinsicHash>,
	/// Holds a set of blocks known to this peer.
	known_blocks: HashSet<HeaderHash>,
	/// Request counter,
	next_request_id: message::RequestId,
}

#[derive(Debug)]
pub struct PeerInfo {
	/// Roles
	pub roles: Role,
	/// Protocol version
	pub protocol_version: u32,
	/// Peer best block hash
	pub best_hash: HeaderHash,
	/// Peer best block number
	pub best_number: BlockNumber,
}

/// Transaction stats
#[derive(Debug)]
pub struct TransactionStats {
	/// Block number where this TX was first seen.
	pub first_seen: u64,
	/// Peers it was propagated to.
	pub propagated_to: BTreeMap<NodeId, usize>,
}

impl Protocol {
	/// Create a new instance.
	pub fn new(config: ProtocolConfig, chain: Arc<Client>, transaction_pool: Arc<TransactionPool>) -> error::Result<Protocol>  {
		let info = chain.info()?;
		let protocol = Protocol {
			config: config,
			chain: chain,
			genesis_hash: info.chain.genesis_hash,
			sync: RwLock::new(ChainSync::new(&info)),
			consensus: Mutex::new(Consensus::new()),
			peers: RwLock::new(HashMap::new()),
			handshaking_peers: RwLock::new(HashMap::new()),
			transaction_pool: transaction_pool,
		};
		Ok(protocol)
	}

	/// Returns protocol status
	pub fn status(&self) -> ProtocolStatus {
		let sync = self.sync.read();
		let peers = self.peers.read();
		ProtocolStatus {
			sync: sync.status(),
			num_peers: peers.values().count(),
			num_active_peers: peers.values().filter(|p| p.block_request.is_some()).count(),
		}
	}

	pub fn handle_packet(&self, io: &mut SyncIo, peer_id: PeerId, data: &[u8]) {
		let message: Message = match serde_json::from_slice(data) {
			Ok(m) => m,
			Err(e) => {
				debug!("Invalid packet from {}: {}", peer_id, e);
				io.disable_peer(peer_id);
				return;
			}
		};

		match message {
			Message::Status(s) => self.on_status_message(io, peer_id, s),
			Message::BlockRequest(r) => self.on_block_request(io, peer_id, r),
			Message::BlockResponse(r) => {
				let request = {
					let mut peers = self.peers.write();
					if let Some(ref mut peer) = peers.get_mut(&peer_id) {
						peer.request_timestamp = None;
						match mem::replace(&mut peer.block_request, None) {
							Some(r) => r,
							None => {
								debug!("Unexpected response packet from {}", peer_id);
								io.disable_peer(peer_id);
								return;
							}
						}
					} else {
						debug!("Unexpected packet from {}", peer_id);
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
			Message::BlockAnnounce(announce) => {
				self.on_block_announce(io, peer_id, announce);
			},
			Message::Statement(s) => self.on_statement(io, peer_id, s, blake2_256(data).into()),
			Message::CandidateRequest(r) => self.on_candidate_request(io, peer_id, r),
			Message::CandidateResponse(r) => self.on_candidate_response(io, peer_id, r),
			Message::BftMessage(m) => self.on_bft_message(io, peer_id, m, blake2_256(data).into()),
			Message::Transactions(m) => self.on_transactions(io, peer_id, m),
		}
	}

	pub fn send_message(&self, io: &mut SyncIo, peer_id: PeerId, mut message: Message) {
		match &mut message {
			&mut Message::BlockRequest(ref mut r) => {
				let mut peers = self.peers.write();
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

	pub fn hash_message(message: &Message) -> Hash {
		let data = serde_json::to_vec(&message).expect("Serializer is infallible; qed");
		blake2_256(&data).into()
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
		let removed = {
			let mut peers = self.peers.write();
			let mut handshaking_peers = self.handshaking_peers.write();
			handshaking_peers.remove(&peer);
			peers.remove(&peer).is_some()
		};
		if removed {
			self.consensus.lock().peer_disconnected(io, self, peer);
			self.sync.write().peer_disconnected(io, self, peer);
		}
	}

	fn on_block_request(&self, io: &mut SyncIo, peer: PeerId, request: message::BlockRequest) {
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
		while let Some(header) = self.chain.header(&id).unwrap_or(None) {
			if blocks.len() >= max{
				break;
			}
			let number = header.number;
			let hash = header_hash(&header);
			let block_data = message::BlockData {
				hash: hash,
				header: if get_header { Some(header) } else { None },
				body: if get_body { self.chain.body(&BlockId::Hash(hash)).unwrap_or(None) } else { None },
				receipt: None,
				message_queue: None,
				justification: if get_justification { self.chain.justification(&BlockId::Hash(hash)).unwrap_or(None) } else { None },
			};
			blocks.push(block_data);
			match request.direction {
				message::Direction::Ascending => id = BlockId::Number(number + 1),
				message::Direction::Descending => {
					if number == 0 {
						break;
					}
					id = BlockId::Number(number - 1)
				}
			}
		}
		let response = message::BlockResponse {
			id: request.id,
			blocks: blocks,
		};
		self.send_message(io, peer, Message::BlockResponse(response))
	}

	fn on_block_response(&self, io: &mut SyncIo, peer: PeerId, request: message::BlockRequest, response: message::BlockResponse) {
		// TODO: validate response
		trace!(target: "sync", "BlockResponse {} from {} with {} blocks", response.id, peer, response.blocks.len());
		self.sync.write().on_block_data(io, self, peer, request, response);
	}

	fn on_candidate_request(&self, io: &mut SyncIo, peer: PeerId, request: message::CandidateRequest) {
		trace!(target: "sync", "CandidateRequest {} from {} for {}", request.id, peer, request.hash);
		self.consensus.lock().on_candidate_request(io, self, peer, request);
	}

	fn on_candidate_response(&self, io: &mut SyncIo, peer: PeerId, response: message::CandidateResponse) {
		trace!(target: "sync", "CandidateResponse {} from {} with {:?} bytes", response.id, peer, response.data.as_ref().map(|d| d.len()));
		self.consensus.lock().on_candidate_response(io, self, peer, response);
	}

	fn on_statement(&self, io: &mut SyncIo, peer: PeerId, statement: message::Statement, hash: Hash) {
		trace!(target: "sync", "Statement from {}: {:?}", peer, statement);
		self.consensus.lock().on_statement(io, self, peer, statement, hash);
	}

	fn on_bft_message(&self, io: &mut SyncIo, peer: PeerId, message: message::LocalizedBftMessage, hash: Hash) {
		trace!(target: "sync", "BFT message from {}: {:?}", peer, message);
		self.consensus.lock().on_bft_message(io, self, peer, message, hash);
	}

	/// See `ConsensusService` trait.
	pub fn send_bft_message(&self, io: &mut SyncIo, message: message::LocalizedBftMessage) {
		self.consensus.lock().send_bft_message(io, self, message)
	}

	/// See `ConsensusService` trait.
	pub fn bft_messages(&self) -> BftMessageStream {
		self.consensus.lock().bft_messages()
	}

	/// See `ConsensusService` trait.
	pub fn statements(&self) -> StatementStream {
		self.consensus.lock().statements()
	}

	/// See `ConsensusService` trait.
	pub fn fetch_candidate(&self, io: &mut SyncIo, hash: &Hash) -> oneshot::Receiver<Vec<u8>> {
		self.consensus.lock().fetch_candidate(io, self, hash)
	}

	/// See `ConsensusService` trait.
	pub fn send_statement(&self, io: &mut SyncIo, statement: message::Statement) {
		self.consensus.lock().send_statement(io, self, statement)
	}

	/// See `ConsensusService` trait.
	pub fn set_local_candidate(&self, candidate: Option<(Hash, Vec<u8>)>) {
		self.consensus.lock().set_local_candidate(candidate)
	}

	/// Perform time based maintenance.
	pub fn tick(&self, io: &mut SyncIo) {
		self.maintain_peers(io);
		self.consensus.lock().collect_garbage();
	}

	fn maintain_peers(&self, io: &mut SyncIo) {
		let tick = time::Instant::now();
		let mut aborting = Vec::new();
		{
			let peers = self.peers.read();
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
		for p in aborting {
			self.on_peer_disconnected(io, p);
		}
	}

	pub fn peer_info(&self, peer: PeerId) -> Option<PeerInfo> {
		self.peers.read().get(&peer).map(|p| {
			PeerInfo {
				roles: p.roles,
				protocol_version: p.protocol_version,
				best_hash: p.best_hash,
				best_number: p.best_number,
			}
		})
	}

	/// Called by peer to report status
	fn on_status_message(&self, io: &mut SyncIo, peer_id: PeerId, status: message::Status) {
		trace!(target: "sync", "New peer {} {:?}", peer_id, status);
		if io.is_expired() {
			trace!(target: "sync", "Status packet from expired session {}:{}", peer_id, io.peer_info(peer_id));
			return;
		}

		{
			let mut peers = self.peers.write();
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
			if status.version != PROTOCOL_VERSION {
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
				known_transactions: HashSet::new(),
				known_blocks: HashSet::new(),
				next_request_id: 0,
			};
			peers.insert(peer_id.clone(), peer);
			handshaking_peers.remove(&peer_id);
			debug!(target: "sync", "Connected {} {}", peer_id, io.peer_info(peer_id));
		}
		self.sync.write().new_peer(io, self, peer_id);
		self.consensus.lock().new_peer(io, self, peer_id, &status.roles);
	}

	/// Called when peer sends us new transactions
	fn on_transactions(&self, _io: &mut SyncIo, peer_id: PeerId, transactions: message::Transactions) {
		// Accept transactions only when fully synced
		if self.sync.read().status().state != SyncState::Idle {
			trace!(target: "sync", "{} Ignoring transactions while syncing", peer_id);
			return;
		}
		trace!(target: "sync", "Received {} transactions from {}", peer_id, transactions.len());
		let mut peers = self.peers.write();
		if let Some(ref mut peer) = peers.get_mut(&peer_id) {
			for t in transactions {
				if let Some(hash) = self.transaction_pool.import(&t) {
					peer.known_transactions.insert(hash);
				}
			}
		}
	}

	/// Called when peer sends us new transactions
	pub fn propagate_transactions(&self, io: &mut SyncIo, transactions: &[(ExtrinsicHash, Vec<u8>)]) {
		// Accept transactions only when fully synced
		if self.sync.read().status().state != SyncState::Idle {
			return;
		}
		let mut peers = self.peers.write();
		for (peer_id, ref mut peer) in peers.iter_mut() {
			let to_send: Vec<_> = transactions.iter().filter_map(|&(hash, ref t)|
				if peer.known_transactions.insert(hash.clone()) { Some(t.clone()) } else { None }).collect();
			if !to_send.is_empty() {
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), peer_id);
				self.send_message(io, *peer_id, Message::Transactions(to_send));
			}
		}
	}

	/// Send Status message
	fn send_status(&self, io: &mut SyncIo, peer_id: PeerId) {
		if let Ok(info) = self.chain.info() {
			let status = message::Status {
				version: PROTOCOL_VERSION,
				genesis_hash: info.chain.genesis_hash,
				roles: self.config.roles.into(),
				best_number: info.chain.best_number,
				best_hash: info.chain.best_hash,
				validator_signature: None,
				validator_id: None,
				parachain_id: None,
			};
			self.send_message(io, peer_id, Message::Status(status))
		}
	}

	pub fn abort(&self) {
		let mut sync = self.sync.write();
		let mut peers = self.peers.write();
		let mut handshaking_peers = self.handshaking_peers.write();
		sync.clear();
		peers.clear();
		handshaking_peers.clear();
		self.consensus.lock().restart();
	}

	pub fn on_block_announce(&self, io: &mut SyncIo, peer_id: PeerId, announce: message::BlockAnnounce) {
		let header = announce.header;
		let hash: HeaderHash = header.blake2_256().into();
		{
			let mut peers = self.peers.write();
			if let Some(ref mut peer) = peers.get_mut(&peer_id) {
				peer.known_blocks.insert(hash.clone());
			}
		}
		self.sync.write().on_block_announce(io, self, peer_id, hash, &header);
	}

	pub fn on_block_imported(&self, io: &mut SyncIo, hash: HeaderHash, header: &Header) {
		self.sync.write().update_chain_info(&header);
		// send out block announcements
		let mut peers = self.peers.write();

		for (peer_id, ref mut peer) in peers.iter_mut() {
			if peer.known_blocks.insert(hash.clone()) {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, peer_id);
				self.send_message(io, *peer_id, Message::BlockAnnounce(message::BlockAnnounce {
					header: header.clone()
				}));
			}
		}
	}

	pub fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats> {
		BTreeMap::new()
	}

	pub fn chain(&self) -> &Client {
		&*self.chain
	}
}
