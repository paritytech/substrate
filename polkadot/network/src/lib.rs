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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot-specific network implementation.
//!
//! This manages gossip of consensus messages for BFT and for parachain statements,
//! parachain block and extrinsic data fetching, communication between collators and validators,
//! and more.

extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_network;
extern crate substrate_primitives;

extern crate polkadot_api;
extern crate polkadot_consensus;
extern crate polkadot_primitives;

extern crate ed25519;
extern crate futures;
extern crate parking_lot;
extern crate tokio;
extern crate rhododendron;

#[macro_use]
extern crate log;

mod router;
pub mod consensus;

use codec::Slicable;
use futures::sync::oneshot;
use parking_lot::Mutex;
use polkadot_consensus::{Statement, SignedStatement, GenericStatement};
use polkadot_primitives::{Block, SessionKey, Hash};
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic, CandidateReceipt};
use substrate_network::{PeerId, RequestId, Context};
use substrate_network::consensus_gossip::ConsensusGossip;
use substrate_network::{message, generic_message};
use substrate_network::specialization::Specialization;
use substrate_network::StatusMessage as GenericFullStatus;

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[cfg(test)]
mod tests;

/// Polkadot protocol id.
pub const DOT_PROTOCOL_ID: ::substrate_network::ProtocolId = *b"dot";

type FullStatus = GenericFullStatus<Block>;

/// Specialization of the network service for the polkadot protocol.
pub type NetworkService = ::substrate_network::Service<Block, PolkadotProtocol>;

/// Status of a Polkadot node.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Status {
	collating_for: Option<ParaId>,
}

impl Slicable for Status {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match self.collating_for {
			Some(ref id) => {
				v.push(1);
				id.using_encoded(|s| v.extend(s));
			}
			None => {
				v.push(0);
			}
		}
		v
	}

	fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
		let collating_for = match input.read_byte()? {
			0 => None,
			1 => Some(ParaId::decode(input)?),
			_ => return None,
		};
		Some(Status { collating_for })
	}
}

struct BlockDataRequest {
	attempted_peers: HashSet<SessionKey>,
	consensus_parent: Hash,
	candidate_hash: Hash,
	block_data_hash: Hash,
	sender: oneshot::Sender<BlockData>,
}

struct PeerInfo {
	status: Status,
	validator: bool,
	session_keys: HashMap<Hash, SessionKey>,
}

#[derive(Default)]
struct KnowledgeEntry {
	knows_block_data: Vec<SessionKey>,
	knows_extrinsic: Vec<SessionKey>,
	block_data: Option<BlockData>,
	extrinsic: Option<Extrinsic>,
}

/// Tracks knowledge of peers.
struct Knowledge {
	candidates: HashMap<Hash, KnowledgeEntry>,
}

impl Knowledge {
	pub fn new() -> Self {
		Knowledge {
			candidates: HashMap::new(),
		}
	}

	fn note_statement(&mut self, from: SessionKey, statement: &Statement) {
		match *statement {
			GenericStatement::Candidate(ref c) => {
				let mut entry = self.candidates.entry(c.hash()).or_insert_with(Default::default);
				entry.knows_block_data.push(from);
				entry.knows_extrinsic.push(from);
			}
			GenericStatement::Available(ref hash) => {
				let mut entry = self.candidates.entry(*hash).or_insert_with(Default::default);
				entry.knows_block_data.push(from);
				entry.knows_extrinsic.push(from);
			}
			GenericStatement::Valid(ref hash) | GenericStatement::Invalid(ref hash) => self.candidates.entry(*hash)
				.or_insert_with(Default::default)
				.knows_block_data
				.push(from),
		}
	}

	fn note_candidate(&mut self, hash: Hash, block_data: Option<BlockData>, extrinsic: Option<Extrinsic>) {
		let entry = self.candidates.entry(hash).or_insert_with(Default::default);
		entry.block_data = entry.block_data.take().or(block_data);
		entry.extrinsic = entry.extrinsic.take().or(extrinsic);
	}
}

struct CurrentConsensus {
	knowledge: Arc<Mutex<Knowledge>>,
	parent_hash: Hash,
	session_keys: HashMap<SessionKey, PeerId>,
	local_session_key: SessionKey,
}

impl CurrentConsensus {
	// get locally stored block data for a candidate.
	fn block_data(&self, hash: &Hash) -> Option<BlockData> {
		self.knowledge.lock().candidates.get(hash)
			.and_then(|entry| entry.block_data.clone())
	}

	fn peer_disconnected(&mut self, peer: &PeerInfo) {
		if let Some(key) = peer.session_keys.get(&self.parent_hash) {
			self.session_keys.remove(key);
		}
	}
}

/// Polkadot-specific messages.
#[derive(Serialize, Deserialize)]
pub enum Message {
	/// signed statement and localized parent hash.
	Statement(Hash, SignedStatement),
	/// Tell the peer your session key for the current block.
	// TODO: do this with a random challenge protocol
	SessionKey(Hash, SessionKey),
	/// Requesting parachain block data by candidate hash.
	RequestBlockData(RequestId, Hash),
	/// Provide block data by candidate hash or nothing if unknown.
	BlockData(RequestId, Option<BlockData>),
}

fn send_polkadot_message(ctx: &mut Context<Block>, to: PeerId, message: Message) {
	let encoded = ::serde_json::to_vec(&message).expect("serialization of messages infallible; qed");
	ctx.send_message(to, generic_message::Message::ChainSpecific(encoded))
}

/// Polkadot protocol attachment for substrate.
pub struct PolkadotProtocol {
	peers: HashMap<PeerId, PeerInfo>,
	consensus_gossip: ConsensusGossip<Block>,
	collators: HashMap<ParaId, Vec<PeerId>>,
	collating_for: Option<ParaId>,
	live_consensus: Option<CurrentConsensus>,
	in_flight: HashMap<(RequestId, PeerId), BlockDataRequest>,
	pending: Vec<BlockDataRequest>,
	next_req_id: u64,
}

impl PolkadotProtocol {
	/// Instantiate a polkadot protocol handler.
	pub fn new() -> Self {
		PolkadotProtocol {
			peers: HashMap::new(),
			consensus_gossip: ConsensusGossip::new(),
			collators: HashMap::new(),
			collating_for: None,
			live_consensus: None,
			in_flight: HashMap::new(),
			pending: Vec::new(),
			next_req_id: 1,
		}
	}

	/// Send a statement to a validator.
	fn send_statement(&mut self, ctx: &mut Context<Block>, _val: SessionKey, parent_hash: Hash, statement: SignedStatement) {
		// TODO: something more targeted than gossip.
		let raw = ::serde_json::to_vec(&Message::Statement(parent_hash, statement))
			.expect("message serialization infallible; qed");

		self.consensus_gossip.multicast_chain_specific(ctx, raw, parent_hash);
	}

	/// Fetch block data by candidate receipt.
	fn fetch_block_data(&mut self, ctx: &mut Context<Block>, candidate: &CandidateReceipt, relay_parent: Hash) -> oneshot::Receiver<BlockData> {
		let (tx, rx) = oneshot::channel();

		self.pending.push(BlockDataRequest {
			attempted_peers: Default::default(),
			consensus_parent: relay_parent,
			candidate_hash: candidate.hash(),
			block_data_hash: candidate.block_data_hash,
			sender: tx,
		});

		self.dispatch_pending_requests(ctx);
		rx
	}

	/// Note new consensus session.
	fn new_consensus(&mut self, ctx: &mut Context<Block>, mut consensus: CurrentConsensus) {
		let parent_hash = consensus.parent_hash;
		let old_parent = self.live_consensus.as_ref().map(|c| c.parent_hash);

		for (id, info) in self.peers.iter_mut().filter(|&(_, ref info)| info.validator) {
			send_polkadot_message(
				ctx,
				*id,
				Message::SessionKey(parent_hash, consensus.local_session_key)
			);

			if let Some(key) = info.session_keys.get(&parent_hash) {
				consensus.session_keys.insert(*key, *id);
			}

			if let Some(ref old_parent) = old_parent {
				info.session_keys.remove(old_parent);
			}
		}

		self.live_consensus = Some(consensus);
		self.consensus_gossip.collect_garbage(old_parent.as_ref());
	}

	fn dispatch_pending_requests(&mut self, ctx: &mut Context<Block>) {
		let consensus = match self.live_consensus {
			Some(ref mut c) => c,
			None => {
				self.pending.clear();
				return;
			}
		};

		let knowledge = consensus.knowledge.lock();
		let mut new_pending = Vec::new();
		for mut pending in ::std::mem::replace(&mut self.pending, Vec::new()) {
			if pending.consensus_parent != consensus.parent_hash { continue }

			if let Some(entry) = knowledge.candidates.get(&pending.candidate_hash) {
				// answer locally
				if let Some(ref data) = entry.block_data {
					let _ = pending.sender.send(data.clone());
					continue;
				}

				let next_peer = entry.knows_block_data.iter()
					.filter_map(|x| consensus.session_keys.get(x).map(|id| (*x, *id)))
					.find(|&(ref key, _)| pending.attempted_peers.insert(*key))
					.map(|(_, id)| id);

				// dispatch to peer
				if let Some(peer_id) = next_peer {
					let req_id = self.next_req_id;
					self.next_req_id += 1;

					send_polkadot_message(
						ctx,
						peer_id,
						Message::RequestBlockData(req_id, pending.candidate_hash)
					);

					self.in_flight.insert((req_id, peer_id), pending);

					continue;
				}
			}

			new_pending.push(pending);
		}

		self.pending = new_pending;
	}

	fn on_polkadot_message(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, raw: Vec<u8>, msg: Message) {
		match msg {
			Message::Statement(parent_hash, _statement) =>
				self.consensus_gossip.on_chain_specific(ctx, peer_id, raw, parent_hash),
			Message::SessionKey(parent_hash, key) => {
				{
					let info = match self.peers.get_mut(&peer_id) {
						Some(peer) => peer,
						None => return,
					};

					if !info.validator {
						ctx.disable_peer(peer_id);
						return;
					}

					match self.live_consensus {
						Some(ref mut consensus) if consensus.parent_hash == parent_hash => {
							consensus.session_keys.insert(key, peer_id);
						}
						_ => {}
					}

					info.session_keys.insert(parent_hash, key);
				}
				self.dispatch_pending_requests(ctx);
			}
			Message::RequestBlockData(req_id, hash) => {
				let block_data = self.live_consensus.as_ref()
					.and_then(|c| c.block_data(&hash));

				send_polkadot_message(ctx, peer_id, Message::BlockData(req_id, block_data));
			}
			Message::BlockData(req_id, data) => self.on_block_data(ctx, peer_id, req_id, data),
		}
	}

	fn on_block_data(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, req_id: RequestId, data: Option<BlockData>) {
		match self.in_flight.remove(&(req_id, peer_id)) {
			Some(req) => {
				if let Some(data) = data {
					if data.hash() == req.block_data_hash {
						let _ = req.sender.send(data);
						return
					}
				}

				self.pending.push(req);
				self.dispatch_pending_requests(ctx);
			}
			None => ctx.disable_peer(peer_id),
		}
	}
}

impl Specialization<Block> for PolkadotProtocol {
	fn status(&self) -> Vec<u8> {
		Status { collating_for: self.collating_for.clone() }.encode()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, status: FullStatus) {
		let local_status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				Status { collating_for: None }
			}
		};

		if let Some(ref para_id) = local_status.collating_for {
			self.collators.entry(para_id.clone())
				.or_insert_with(Vec::new)
				.push(peer_id);
		}

		let validator = status.roles.iter().any(|r| *r == message::Role::Authority);
		self.peers.insert(peer_id, PeerInfo {
			status: local_status,
			session_keys: Default::default(),
			validator,
		});

		self.consensus_gossip.new_peer(ctx, peer_id, &status.roles);

		if let (true, &Some(ref consensus)) = (validator, &self.live_consensus) {
			send_polkadot_message(
				ctx,
				peer_id,
				Message::SessionKey(consensus.parent_hash, consensus.local_session_key)
			);
		}

		self.dispatch_pending_requests(ctx);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, peer_id: PeerId) {
		if let Some(info) = self.peers.remove(&peer_id) {
			if let Some(collators) = info.status.collating_for.and_then(|id| self.collators.get_mut(&id)) {
				if let Some(pos) = collators.iter().position(|x| x == &peer_id) {
					collators.swap_remove(pos);
				}
			}

			if let (true, &mut Some(ref mut consensus)) = (info.validator, &mut self.live_consensus) {
				consensus.peer_disconnected(&info);
			}

			{
				let pending = &mut self.pending;
				self.in_flight.retain(|&(_, ref peer), val| {
					let retain = peer != &peer_id;
					if !retain {
						let (sender, _) = oneshot::channel();
						pending.push(::std::mem::replace(val, BlockDataRequest {
							attempted_peers: Default::default(),
							consensus_parent: Default::default(),
							candidate_hash: Default::default(),
							block_data_hash: Default::default(),
							sender,
						}));
					}

					retain
				});
			}
			self.consensus_gossip.peer_disconnected(ctx, peer_id);
			self.dispatch_pending_requests(ctx);
		}
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, message: message::Message<Block>) {
		match message {
			generic_message::Message::BftMessage(msg) => {
				// TODO: check signature here? what if relevant block is unknown?
				self.consensus_gossip.on_bft_message(ctx, peer_id, msg)
			}
			generic_message::Message::ChainSpecific(raw) => {
				match serde_json::from_slice(&raw) {
					Ok(msg) => self.on_polkadot_message(ctx, peer_id, raw, msg),
					Err(e) => {
						trace!(target: "p_net", "Bad message from {}: {}", peer_id, e);
						ctx.disable_peer(peer_id);
					}
				}
			}
			_ => {}
		}
	}

	fn on_abort(&mut self) {
		self.consensus_gossip.abort();
	}

	fn maintain_peers(&mut self, ctx: &mut Context<Block>) {
		self.consensus_gossip.collect_garbage(None);
		self.dispatch_pending_requests(ctx);
	}
}
