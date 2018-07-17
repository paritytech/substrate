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

mod collator_pool;
mod router;
pub mod consensus;

use codec::{Decode, Encode, Input, Output};
use futures::sync::oneshot;
use parking_lot::Mutex;
use polkadot_consensus::{Statement, SignedStatement, GenericStatement};
use polkadot_primitives::{AccountId, Block, SessionKey, Hash, Header};
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic, CandidateReceipt, Collation};
use substrate_network::{PeerId, RequestId, Context};
use substrate_network::consensus_gossip::ConsensusGossip;
use substrate_network::{message, generic_message};
use substrate_network::specialization::Specialization;
use substrate_network::StatusMessage as GenericFullStatus;
use self::collator_pool::{CollatorPool, Role, Action};

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
	collating_for: Option<(AccountId, ParaId)>,
}

impl Encode for Status {
	fn encode_to<T: codec::Output>(&self, dest: &mut T) {
		match self.collating_for {
			Some(ref details) => {
				dest.push_byte(1);
				dest.push(details);
			}
			None => {
				dest.push_byte(0);
			}
		}
	}
}

impl Decode for Status {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		let collating_for = match input.read_byte()? {
			0 => None,
			1 => Some(Decode::decode(input)?),
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
	/// Tell a collator their role.
	CollatorRole(Role),
	/// A collation provided by a peer. Relay parent and collation.
	Collation(Hash, Collation),
}

impl Encode for Message {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match *self {
			Message::Statement(ref h, ref s) => {
				dest.push_byte(0);
				dest.push(h);
				dest.push(s);
			}
			Message::SessionKey(ref h, ref k) => {
				dest.push_byte(1);
				dest.push(h);
				dest.push(k);
			}
			Message::RequestBlockData(ref id, ref d) => {
				dest.push_byte(2);
				dest.push(id);
				dest.push(d);
			}
			Message::BlockData(ref id, ref d) => {
				dest.push_byte(3);
				dest.push(id);
				dest.push(d);
			}
			Message::CollatorRole(ref r) => {
				dest.push_byte(4);
				dest.push(r);
			}
			Message::Collation(ref h, ref c) => {
				dest.push_byte(5);
				dest.push(h);
				dest.push(c);
			}
		}
	}
}

impl Decode for Message {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			0 => Some(Message::Statement(Decode::decode(input)?, Decode::decode(input)?)),
			1 => Some(Message::SessionKey(Decode::decode(input)?, Decode::decode(input)?)),
			2 => Some(Message::RequestBlockData(Decode::decode(input)?, Decode::decode(input)?)),
			3 => Some(Message::BlockData(Decode::decode(input)?, Decode::decode(input)?)),
			4 => Some(Message::CollatorRole(Decode::decode(input)?)),
			5 => Some(Message::Collation(Decode::decode(input)?, Decode::decode(input)?)),
			_ => None,
		}
	}
}

fn send_polkadot_message(ctx: &mut Context<Block>, to: PeerId, message: Message) {
	let encoded = message.encode();
	ctx.send_message(to, generic_message::Message::ChainSpecific(encoded))
}

/// Polkadot protocol attachment for substrate.
pub struct PolkadotProtocol {
	peers: HashMap<PeerId, PeerInfo>,
	consensus_gossip: ConsensusGossip<Block>,
	collators: CollatorPool,
	live_consensus: Option<CurrentConsensus>,
	in_flight: HashMap<(RequestId, PeerId), BlockDataRequest>,
	pending: Vec<BlockDataRequest>,
	next_req_id: u64,
}

impl Default for PolkadotProtocol {
	fn default() -> Self {
		Self::new()
	}
}

impl PolkadotProtocol {
	/// Instantiate a polkadot protocol handler.
	pub fn new() -> Self {
		PolkadotProtocol {
			peers: HashMap::new(),
			consensus_gossip: ConsensusGossip::new(),
			collators: CollatorPool::new(),
			live_consensus: None,
			in_flight: HashMap::new(),
			pending: Vec::new(),
			next_req_id: 1,
		}
	}

	/// Send a statement to a validator.
	fn send_statement(&mut self, ctx: &mut Context<Block>, _val: SessionKey, parent_hash: Hash, statement: SignedStatement) {
		// TODO: something more targeted than gossip.
		let raw = Message::Statement(parent_hash, statement).encode();
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

		// TODO: optimize for when session key changes and only send to collators who are relevant in next few blocks.
		for (id, info) in self.peers.iter_mut()
			.filter(|&(_, ref info)| info.validator || info.status.collating_for.is_some())
		{
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
						ctx.disable_peer(peer_id, "Unknown Polkadot-protocol reason");
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
			Message::Collation(relay_parent, collation) => self.on_collation(ctx, peer_id, relay_parent, collation),
			Message::CollatorRole(_) => {},
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
			None => ctx.disable_peer(peer_id, "Unknown Polkadot-protocol reason"),
		}
	}
}

impl Specialization<Block> for PolkadotProtocol {
	fn status(&self) -> Vec<u8> {
		Status { collating_for: None }.encode()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, status: FullStatus) {
		let local_status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				Status { collating_for: None }
			}
		};

		if let Some((ref acc_id, ref para_id)) = local_status.collating_for {
			if self.collator_peer_id(acc_id.clone()).is_some() {
				ctx.disable_peer(peer_id, "Unknown Polkadot-protocol reason");
				return
			}

			let collator_role = self.collators.on_new_collator(acc_id.clone(), para_id.clone());
			send_polkadot_message(
				ctx,
				peer_id,
				Message::CollatorRole(collator_role),
			);
		}

		let validator = status.roles.contains(substrate_network::Roles::AUTHORITY);
		let send_key = validator || local_status.collating_for.is_some();

		self.peers.insert(peer_id, PeerInfo {
			status: local_status,
			session_keys: Default::default(),
			validator,
		});

		self.consensus_gossip.new_peer(ctx, peer_id, status.roles);
		if let (true, &Some(ref consensus)) = (send_key, &self.live_consensus) {
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
			if let Some((acc_id, _)) = info.status.collating_for {
				let new_primary = self.collators.on_disconnect(acc_id)
					.and_then(|new_primary| self.collator_peer_id(new_primary));

				if let Some(new_primary) = new_primary {
					send_polkadot_message(
						ctx,
						new_primary,
						Message::CollatorRole(Role::Primary),
					)
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
				match Message::decode(&mut raw.as_slice()) {
					Some(msg) => self.on_polkadot_message(ctx, peer_id, raw, msg),
					None => {
						trace!(target: "p_net", "Bad message from {}", peer_id);
						ctx.disable_peer(peer_id, "Invalid polkadot protocol message format");
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
		self.collators.collect_garbage(None);
		self.dispatch_pending_requests(ctx);

		for collator_action in self.collators.maintain_peers() {
			match collator_action {
				Action::Disconnect(collator) => self.disconnect_bad_collator(ctx, collator),
				Action::NewRole(account_id, role) => if let Some(collator) = self.collator_peer_id(account_id) {
					send_polkadot_message(
						ctx,
						collator,
						Message::CollatorRole(role),
					)
				},
			}
		}
	}

	fn on_block_imported(&mut self, _ctx: &mut Context<Block>, hash: Hash, _header: &Header) {
		self.collators.collect_garbage(Some(&hash));
	}
}

impl PolkadotProtocol {
	// we received a collation from a peer
	fn on_collation(&mut self, ctx: &mut Context<Block>, from: PeerId, relay_parent: Hash, collation: Collation) {
		let collation_para = collation.receipt.parachain_index;
		let collated_acc = collation.receipt.collator;

		match self.peers.get(&from) {
			None => ctx.disconnect_peer(from),
			Some(peer_info) => match peer_info.status.collating_for {
				None => ctx.disable_peer(from, "Unknown Polkadot-protocol reason"),
				Some((ref acc_id, ref para_id)) => {
					let structurally_valid = para_id == &collation_para && acc_id == &collated_acc;
					if structurally_valid && collation.receipt.check_signature().is_ok() {
						self.collators.on_collation(acc_id.clone(), relay_parent, collation)
					} else {
						ctx.disable_peer(from, "Unknown Polkadot-protocol reason")
					};
				}
			},
		}
	}

	fn await_collation(&mut self, relay_parent: Hash, para_id: ParaId) -> oneshot::Receiver<Collation> {
		let (tx, rx) = oneshot::channel();
		self.collators.await_collation(relay_parent, para_id, tx);
		rx
	}

	// get connected peer with given account ID for collation.
	fn collator_peer_id(&self, account_id: AccountId) -> Option<PeerId> {
		let check_info = |info: &PeerInfo| info
			.status
			.collating_for
			.as_ref()
			.map_or(false, |&(ref acc_id, _)| acc_id == &account_id);

		self.peers
			.iter()
			.filter(|&(_, info)| check_info(info))
			.map(|(peer_id, _)| *peer_id)
			.next()
	}

	// disconnect a collator by account-id.
	fn disconnect_bad_collator(&self, ctx: &mut Context<Block>, account_id: AccountId) {
		if let Some(peer_id) = self.collator_peer_id(account_id) {
			ctx.disable_peer(peer_id, "Unknown Polkadot-protocol reason")
		}
	}
}
