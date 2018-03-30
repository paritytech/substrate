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

//! Consensus related bits of the network service.

use std::collections::HashMap;
use multiqueue;
use futures::sync::oneshot;
use io::SyncIo;
use protocol::Protocol;
use network::PeerId;
use primitives::Hash;
use message::{self, Message};
use runtime_support::Hashable;

//TODO: The queue is preallocated in multiqueue. Make it unbounded
const QUEUE_SIZE: u64 = 1 << 16;

struct CandidateRequest {
	id: message::RequestId,
	completion: oneshot::Sender<Vec<u8>>,
}

struct PeerConsensus {
	candidate_fetch: Option<CandidateRequest>,
	candidate_available: Option<Hash>,
}

/// Consensus network protocol handler. Manages statements and candidate requests.
pub struct Consensus {
	peers: HashMap<PeerId, PeerConsensus>,
	our_candidate: Option<(Hash, Vec<u8>)>,
	statement_sink: multiqueue::BroadcastFutSender<message::Statement>,
	statement_stream: multiqueue::BroadcastFutReceiver<message::Statement>,
	bft_message_sink: multiqueue::BroadcastFutSender<message::BftMessage>,
	bft_message_stream: multiqueue::BroadcastFutReceiver<message::BftMessage>,
}

impl Consensus {
	/// Create a new instance.
	pub fn new() -> Consensus {
		let (statement_sink, statement_stream) = multiqueue::broadcast_fut_queue(QUEUE_SIZE);
		let (bft_sink, bft_stream) = multiqueue::broadcast_fut_queue(QUEUE_SIZE);
		Consensus {
			peers: HashMap::new(),
			our_candidate: None,
			statement_sink: statement_sink,
			statement_stream: statement_stream,
			bft_message_sink: bft_sink,
			bft_message_stream: bft_stream,
		}
	}

	/// Closes all notification streams.
	pub fn restart(&mut self) {
		let (statement_sink, statement_stream) = multiqueue::broadcast_fut_queue(QUEUE_SIZE);
		let (bft_sink, bft_stream) = multiqueue::broadcast_fut_queue(QUEUE_SIZE);
		self.statement_sink = statement_sink;
		self.statement_stream = statement_stream;
		self.bft_message_sink = bft_sink;
		self.bft_message_stream = bft_stream;
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, _io: &mut SyncIo, _protocol: &Protocol, peer_id: PeerId, roles: &[message::Role]) {
		if roles.iter().any(|r| *r == message::Role::Validator) {
			trace!(target:"sync", "Registering validator {}", peer_id);
			self.peers.insert(peer_id, PeerConsensus {
				candidate_fetch: None,
				candidate_available: None,
			});
		}
	}

	pub fn on_statement(&mut self, peer_id: PeerId, statement: message::Statement) {
		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			// TODO: validate signature?
			match &statement.statement {
				&message::UnsignedStatement::Candidate(ref receipt) => peer.candidate_available = Some(Hash::from(receipt.blake2_256())),
				&message::UnsignedStatement::Available(ref hash) => peer.candidate_available = Some(*hash),
				&message::UnsignedStatement::Valid(_) | &message::UnsignedStatement::Invalid(_) => (),
			}
			if let Err(e) = self.statement_sink.try_send(statement) {
				trace!(target:"sync", "Error broadcasting statement notification: {:?}", e);
			}
		} else {
			trace!(target:"sync", "Ignored statement from unregistered peer {}", peer_id);
		}
	}

	pub fn statements(&self) -> multiqueue::BroadcastFutReceiver<message::Statement>{
		self.statement_stream.add_stream()
	}

	pub fn on_bft_message(&mut self, peer_id: PeerId, message: message::BftMessage) {
		if self.peers.contains_key(&peer_id) {
			// TODO: validate signature?
			if let Err(e) = self.bft_message_sink.try_send(message) {
				trace!(target:"sync", "Error broadcasting BFT message notification: {:?}", e);
			}
		} else {
			trace!(target:"sync", "Ignored BFT statement from unregistered peer {}", peer_id);
		}
	}

	pub fn bft_messages(&self) -> multiqueue::BroadcastFutReceiver<message::BftMessage>{
		self.bft_message_stream.add_stream()
	}

	pub fn fetch_candidate(&mut self, io: &mut SyncIo, protocol: &Protocol, hash: &Hash) -> oneshot::Receiver<Vec<u8>> {
		// Request from the first peer that has it available.
		// TODO: random peer selection.
		trace!(target:"sync", "Trying to fetch candidate {:?}", hash);
		let (sender, receiver) = oneshot::channel();
		if let Some((peer_id, ref mut peer)) = self.peers.iter_mut()
			.find(|&(_, ref peer)| peer.candidate_fetch.is_none() && peer.candidate_available.as_ref().map_or(false, |h| h == hash)) {

			trace!(target:"sync", "Fetching candidate from {}", peer_id);
			let id = 0; //TODO: generate unique id
			peer.candidate_fetch = Some(CandidateRequest {
				id: id,
				completion: sender,
			});
			let request = message::CandidateRequest {
				id: id,
				hash: *hash,
			};
			protocol.send_message(io, *peer_id, Message::CandidateRequest(request));
		}
		// If no peer found `sender` is dropped and `receiver` is canceled immediatelly.
		return receiver;
	}

	pub fn send_statement(&mut self, io: &mut SyncIo, protocol: &Protocol, statement: message::Statement) {
		// Broadcast statement to all validators.
		trace!(target:"sync", "Broadcasting statement {:?}", statement);
		for peer in self.peers.keys() {
			protocol.send_message(io, *peer, Message::Statement(statement.clone()));
		}
	}

	pub fn send_bft_message(&mut self, io: &mut SyncIo, protocol: &Protocol, message: message::BftMessage) {
		// Broadcast message to all validators.
		trace!(target:"sync", "Broadcasting BFT message {:?}", message);
		for peer in self.peers.keys() {
			protocol.send_message(io, *peer, Message::BftMessage(message.clone()));
		}
	}

	pub fn set_local_candidate(&mut self, candidate: Option<(Hash, Vec<u8>)>) {
		trace!(target:"sync", "Set local candidate to {:?}", candidate.as_ref().map(|&(h, _)| h));
		self.our_candidate = candidate;
	}

	pub fn on_candidate_request(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId, request: message::CandidateRequest) {
		let response = match self.our_candidate {
			Some((ref hash, ref data)) if *hash == request.hash => Some(data.clone()),
			_ => None,
		};
		let msg = message::CandidateResponse {
			id: request.id,
			data: response,
		};
		protocol.send_message(io, peer_id, Message::CandidateResponse(msg));
	}

	pub fn on_candidate_response(&mut self, io: &mut SyncIo, _protocol: &Protocol, peer_id: PeerId, response: message::CandidateResponse) {
		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			if let Some(request) = peer.candidate_fetch.take() {
				if response.id == request.id {
					if let Some(data) = response.data {
						if let Err(e) = request.completion.send(data) {
							trace!(target:"sync", "Error sending candidate data notification: {:?}", e);
						}
					}
				} else {
					trace!(target:"sync", "Unexpected candidate response from {}", peer_id);
					io.disable_peer(peer_id);
				}
			} else {
				trace!(target:"sync", "Unexpected candidate response from {}", peer_id);
				io.disable_peer(peer_id);
			}
		}
	}

	pub fn peer_disconnected(&mut self, _io: &mut SyncIo, _protocol: &Protocol, peer_id: PeerId) {
		self.peers.remove(&peer_id);
	}
}
