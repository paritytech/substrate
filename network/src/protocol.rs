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
use std::mem;
use std::sync::Arc;
use parking_lot::RwLock;
use serde_json;
use std::time;
use primitives::block::{HeaderHash, TransactionHash, Number as BlockNumber};
use network::{PeerId, NodeId};

use message::{self, Message};
use sync::{ChainSync, Status as SyncStatus};
use service::{RelayChain, Role};
use config::ProtocolConfig;
use io::SyncIo;

const REQUEST_TIMEOUT_SEC: u64 = 15;
const PROTOCOL_VERSION: u32 = 0;

// Lock must always be taken in order declared here.
pub struct Protocol {
	config: ProtocolConfig,
	chain: Arc<RelayChain>,
	sync: RwLock<ChainSync>,
	/// All connected peers
	peers: RwLock<HashMap<PeerId, Peer>>,
	/// Connected peers pending Status message.
	handshaking_peers: RwLock<HashMap<PeerId, time::Instant>>,
}

/// Syncing status and statistics
#[derive(Clone, Copy)]
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
	_best_hash: HeaderHash,
	/// Peer best block number
	_best_number: BlockNumber,
	/// Pending request if any
	request: Option<Message>,
	/// Request timestamp
	request_timestamp: Option<time::Instant>,
	/// Holds a set of transactions recently sent to this peer to avoid spamming.
	_last_sent_transactions: HashSet<TransactionHash>,
}

#[derive(Debug)]
pub struct PeerInfo {
	/// Roles
	roles: Role,
	/// Protocol version
	protocol_version: u32,
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
	pub fn new(config: ProtocolConfig, chain: Arc<RelayChain>) -> Protocol {
		let protocol = Protocol {
			config: config,
			chain: chain,
			sync: RwLock::new(ChainSync::new()),
			peers: RwLock::new(HashMap::new()),
			handshaking_peers: RwLock::new(HashMap::new()),
		};
		protocol.sync.write().start(&protocol);
		protocol
	}

	/// Returns protocol status
	pub fn status(&self) -> ProtocolStatus {
		let sync = self.sync.read();
		let peers = self.peers.read();
		ProtocolStatus {
			sync: sync.status(),
			num_peers: peers.values().count(),
			num_active_peers: peers.values().filter(|p| p.request.is_some()).count(),
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

		let request = if message.is_response() {
			let mut peers = self.peers.write();
			if let Some(ref mut peer) = peers.get_mut(&peer_id) {
				// TODO: check id
				if peer.request.is_none() {
					debug!("Unexpected response packet from {}", peer_id);
					io.disable_peer(peer_id);
					return;
				}
				peer.request_timestamp = None;
				mem::replace(&mut peer.request, None)
			} else {
				debug!("Unexpected packet from {}", peer_id);
				io.disable_peer(peer_id);
				return;
			}
		} else {
			None
		};

		match message {
			Message::Status(s) => self.on_status_message(io, peer_id, s),
			Message::BlockRequest(r) => self.on_block_request(io, peer_id, r),
			Message::BlockResponse(r) => {
				let request = request.expect("BlockResponse is response; responses without requests are filtered out; qed");
				let block_request = match request {
					Message::BlockRequest(r) => r,
					_ => {
						debug!("Unexpected response packet type from {}", peer_id);
						io.disable_peer(peer_id);
						return;
					}
				};
				self.on_block_response(io, peer_id, block_request, r);
			},
		}
	}

	pub fn send_message(&self, io: &mut SyncIo, peer_id: PeerId, message: Message) {
		let data = serde_json::to_vec(&message).expect("Serializer is infallible; qed");
		let mut peers = self.peers.write();
		if let Some(ref mut peer) = peers.get_mut(&peer_id) {
			if message.is_request() {
				peer.request = Some(message);
				peer.request_timestamp = Some(time::Instant::now());
			} else {
				peer.request = None;
				peer.request_timestamp = None;
			}
		}
		if let Err(e) = io.send(peer_id, data) {
			debug!(target:"sync", "Error sending message: {:?}", e);
			io.disconnect_peer(peer_id);
		}
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
			self.sync.write().peer_disconnected(io, self, peer);
		}
	}

	pub fn on_block_request(&self, _io: &mut SyncIo, _peer_id: PeerId, _request: message::BlockRequest) {
	}

	pub fn on_block_response(&self, _io: &mut SyncIo, _peer_id: PeerId, _request: message::BlockRequest, _response: message::BlockResponse) {
	}

	pub fn tick(&self, io: &mut SyncIo) {
		self.maintain_peers(io);
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
					trace!(target:"sync", "Timeout {}", peer_id);
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
			let chain_info = self.chain.chain_info();
			if status.genesis_hash != chain_info.genesis_hash {
				io.disable_peer(peer_id);
				trace!(target: "sync", "Peer {} genesis hash mismatch (ours: {}, theirs: {})", peer_id, chain_info.genesis_hash, status.genesis_hash);
				return;
			}
			if status.version != PROTOCOL_VERSION {
				io.disable_peer(peer_id);
				trace!(target: "sync", "Peer {} unsupported eth protocol ({})", peer_id, status.version);
				return;
			}

			let peer = Peer {
				protocol_version: status.version,
				roles: status.roles.into(),
				_best_hash: status.best_hash,
				_best_number: status.best_number,
				request: None,
				request_timestamp: None,
				_last_sent_transactions: HashSet::new(),
			};
			peers.insert(peer_id.clone(), peer);
			handshaking_peers.remove(&peer_id);
			debug!(target: "sync", "Connected {} {}", peer_id, io.peer_info(peer_id));
		}
		self.sync.write().new_peer(io, self, peer_id);
	}

	/// Send Status message
	fn send_status(&self, io: &mut SyncIo, peer_id: PeerId) {
		let chain_info = self.chain.chain_info();
		let status = message::Status {
			version: PROTOCOL_VERSION,
			genesis_hash: chain_info.genesis_hash,
			roles: self.config.roles.into(),
			best_number: chain_info.best_number,
			best_hash: chain_info.best_hash,
			validator_signature: None,
			validator_id: None,
			parachain_id: None,
		};
		self.send_message(io, peer_id, Message::Status(status))
	}

	pub fn abort(&self) {
		let mut sync = self.sync.write();
		let mut peers = self.peers.write();
		let mut handshaking_peers = self.handshaking_peers.write();
		sync.abort();
		peers.clear();
		handshaking_peers.clear();
	}

	pub fn on_new_block(&self) {
	}

	pub fn on_new_transactions(&self) {
	}

	pub fn transactions_stats(&self) -> BTreeMap<TransactionHash, TransactionStats> {
		BTreeMap::new()
	}
}



