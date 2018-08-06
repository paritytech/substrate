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
extern crate polkadot_availability_store as av_store;
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
mod local_collations;
mod router;
pub mod consensus;

use codec::{Decode, Encode, Input, Output};
use futures::sync::oneshot;
use parking_lot::Mutex;
use polkadot_consensus::{Statement, SignedStatement, GenericStatement};
use polkadot_primitives::{AccountId, Block, SessionKey, Hash, Header};
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic, CandidateReceipt, Collation};
use substrate_network::{NodeIndex, RequestId, Context, Severity};
use substrate_network::consensus_gossip::ConsensusGossip;
use substrate_network::{message, generic_message};
use substrate_network::specialization::Specialization;
use substrate_network::StatusMessage as GenericFullStatus;
use self::collator_pool::{CollatorPool, Role, Action};
use self::local_collations::LocalCollations;

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

// ensures collator-protocol messages are sent in correct order.
// session key must be sent before collator role.
enum CollatorState {
	Fresh,
	RolePending(Role),
	Primed,
}

impl CollatorState {
	fn send_key<F: FnMut(Message)>(&mut self, key: SessionKey, mut f: F) {
		f(Message::SessionKey(key));
		if let CollatorState::RolePending(role) = ::std::mem::replace(self, CollatorState::Primed) {
			f(Message::CollatorRole(role));
		}
	}

	fn set_role<F: FnMut(Message)>(&mut self, role: Role, mut f: F) {
		if let CollatorState::Primed = *self {
			f(Message::CollatorRole(role));
		} else {
			*self = CollatorState::RolePending(role);
		}
	}
}

struct PeerInfo {
	collating_for: Option<(AccountId, ParaId)>,
	validator_key: Option<SessionKey>,
	claimed_validator: bool,
	collator_state: CollatorState,
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
	local_session_key: SessionKey,
}

impl CurrentConsensus {
	// get locally stored block data for a candidate.
	fn block_data(&self, relay_parent: &Hash, hash: &Hash) -> Option<BlockData> {
		if relay_parent != &self.parent_hash { return None }

		self.knowledge.lock().candidates.get(hash)
			.and_then(|entry| entry.block_data.clone())
	}
}

/// Polkadot-specific messages.
#[derive(Debug)]
pub enum Message {
	/// signed statement and localized parent hash.
	Statement(Hash, SignedStatement),
	/// As a validator, tell the peer your current session key.
	// TODO: do this with a cryptographic proof of some kind
	SessionKey(SessionKey),
	/// Requesting parachain block data by (relay_parent, candidate_hash).
	RequestBlockData(RequestId, Hash, Hash),
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
			Message::SessionKey(ref k) => {
				dest.push_byte(1);
				dest.push(k);
			}
			Message::RequestBlockData(ref id, ref r, ref d) => {
				dest.push_byte(2);
				dest.push(id);
				dest.push(r);
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
			1 => Some(Message::SessionKey(Decode::decode(input)?)),
			2 => {
				let x: (_, _, _) = Decode::decode(input)?;
				Some(Message::RequestBlockData(x.0, x.1, x.2))
			}
			3 => Some(Message::BlockData(Decode::decode(input)?, Decode::decode(input)?)),
			4 => Some(Message::CollatorRole(Decode::decode(input)?)),
			5 => Some(Message::Collation(Decode::decode(input)?, Decode::decode(input)?)),
			_ => None,
		}
	}
}

fn send_polkadot_message(ctx: &mut Context<Block>, to: NodeIndex, message: Message) {
	trace!(target: "p_net", "Sending polkadot message to {}: {:?}", to, message);
	let encoded = message.encode();
	ctx.send_message(to, generic_message::Message::ChainSpecific(encoded))
}

/// Polkadot protocol attachment for substrate.
pub struct PolkadotProtocol {
	peers: HashMap<NodeIndex, PeerInfo>,
	collating_for: Option<(AccountId, ParaId)>,
	consensus_gossip: ConsensusGossip<Block>,
	collators: CollatorPool,
	validators: HashMap<SessionKey, NodeIndex>,
	local_collations: LocalCollations<Collation>,
	live_consensus: Option<CurrentConsensus>,
	in_flight: HashMap<(RequestId, NodeIndex), BlockDataRequest>,
	pending: Vec<BlockDataRequest>,
	extrinsic_store: Option<::av_store::Store>,
	next_req_id: u64,
}

impl PolkadotProtocol {
	/// Instantiate a polkadot protocol handler.
	pub fn new(collating_for: Option<(AccountId, ParaId)>) -> Self {
		PolkadotProtocol {
			peers: HashMap::new(),
			consensus_gossip: ConsensusGossip::new(),
			collators: CollatorPool::new(),
			collating_for,
			validators: HashMap::new(),
			local_collations: LocalCollations::new(),
			live_consensus: None,
			in_flight: HashMap::new(),
			pending: Vec::new(),
			extrinsic_store: None,
			next_req_id: 1,
		}
	}

	/// Gossip a consensus statement.
	fn gossip_statement(&mut self, ctx: &mut Context<Block>, parent_hash: Hash, statement: SignedStatement) {
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
	fn new_consensus(&mut self, ctx: &mut Context<Block>, consensus: CurrentConsensus) {
		let old_data = self.live_consensus.as_ref().map(|c| (c.parent_hash, c.local_session_key));

		if Some(&consensus.local_session_key) != old_data.as_ref().map(|&(_, ref key)| key) {
			for (id, peer_data) in self.peers.iter_mut()
				.filter(|&(_, ref info)| info.claimed_validator || info.collating_for.is_some())
			{
				peer_data.collator_state.send_key(consensus.local_session_key, |msg| send_polkadot_message(
					ctx,
					*id,
					msg
				));
			}
		}

		self.live_consensus = Some(consensus);
		self.consensus_gossip.collect_garbage(old_data.as_ref().map(|&(ref hash, _)| hash));
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

				let validator_keys = &mut self.validators;
				let next_peer = entry.knows_block_data.iter()
					.filter_map(|x| validator_keys.get(x).map(|id| (*x, *id)))
					.find(|&(ref key, _)| pending.attempted_peers.insert(*key))
					.map(|(_, id)| id);

				// dispatch to peer
				if let Some(who) = next_peer {
					let req_id = self.next_req_id;
					self.next_req_id += 1;

					send_polkadot_message(
						ctx,
						who,
						Message::RequestBlockData(req_id, pending.consensus_parent, pending.candidate_hash)
					);

					self.in_flight.insert((req_id, who), pending);

					continue;
				}
			}

			new_pending.push(pending);
		}

		self.pending = new_pending;
	}

	fn on_polkadot_message(&mut self, ctx: &mut Context<Block>, who: NodeIndex, raw: Vec<u8>, msg: Message) {
		trace!(target: "p_net", "Polkadot message from {}: {:?}", who, msg);
		match msg {
			Message::Statement(parent_hash, _statement) =>
				self.consensus_gossip.on_chain_specific(ctx, who, raw, parent_hash),
			Message::SessionKey(key) => self.on_session_key(ctx, who, key),
			Message::RequestBlockData(req_id, relay_parent, candidate_hash) => {
				let block_data = self.live_consensus.as_ref()
					.and_then(|c| c.block_data(&relay_parent, &candidate_hash))
					.or_else(|| self.extrinsic_store.as_ref()
						.and_then(|s| s.block_data(relay_parent, candidate_hash))
					);

				send_polkadot_message(ctx, who, Message::BlockData(req_id, block_data));
			}
			Message::BlockData(req_id, data) => self.on_block_data(ctx, who, req_id, data),
			Message::Collation(relay_parent, collation) => self.on_collation(ctx, who, relay_parent, collation),
			Message::CollatorRole(role) => self.on_new_role(ctx, who, role),
		}
	}

	fn on_session_key(&mut self, ctx: &mut Context<Block>, who: NodeIndex, key: SessionKey) {
		{
			let info = match self.peers.get_mut(&who) {
				Some(peer) => peer,
				None => {
					trace!(target: "p_net", "Network inconsistency: message received from unconnected peer {}", who);
					return
				}
			};

			if !info.claimed_validator {
				ctx.report_peer(who, Severity::Bad("Session key broadcasted without setting authority role"));
				return;
			}

			if let Some(old_key) = ::std::mem::replace(&mut info.validator_key, Some(key)) {
				self.validators.remove(&old_key);

				for (relay_parent, collation) in self.local_collations.fresh_key(&old_key, &key) {
					send_polkadot_message(
						ctx,
						who,
						Message::Collation(relay_parent, collation),
					)
				}

			}
			self.validators.insert(key, who);
		}

		self.dispatch_pending_requests(ctx);
	}

	fn on_block_data(&mut self, ctx: &mut Context<Block>, who: NodeIndex, req_id: RequestId, data: Option<BlockData>) {
		match self.in_flight.remove(&(req_id, who)) {
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
			None => ctx.report_peer(who, Severity::Bad("Unexpected block data response")),
		}
	}

	// when a validator sends us (a collator) a new role.
	fn on_new_role(&mut self, ctx: &mut Context<Block>, who: NodeIndex, role: Role) {
		let info = match self.peers.get(&who) {
			Some(peer) => peer,
			None => {
				trace!(target: "p_net", "Network inconsistency: message received from unconnected peer {}", who);
				return
			}
		};

		debug!(target: "p_net", "New collator role {:?} from {}", role, who);

		match info.validator_key {
			None => ctx.report_peer(
				who,
				Severity::Bad("Sent collator role without registering first as validator"),
			),
			Some(key) => for (relay_parent, collation) in self.local_collations.note_validator_role(key, role) {
				debug!(target: "p_net", "Broadcasting collation on relay parent {:?}", relay_parent);
				send_polkadot_message(
					ctx,
					who,
					Message::Collation(relay_parent, collation),
				)
			},
		}
	}
}

impl Specialization<Block> for PolkadotProtocol {
	fn status(&self) -> Vec<u8> {
		Status { collating_for: self.collating_for.clone() }.encode()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, who: NodeIndex, status: FullStatus) {
		let local_status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				Status { collating_for: None }
			}
		};

		let validator = status.roles.contains(substrate_network::Roles::AUTHORITY);
		let send_key = validator || local_status.collating_for.is_some();

		let mut peer_info = PeerInfo {
			collating_for: local_status.collating_for,
			validator_key: None,
			claimed_validator: validator,
			collator_state: CollatorState::Fresh,
		};

		if let Some((ref acc_id, ref para_id)) = local_status.collating_for {
			if self.collator_peer(acc_id.clone()).is_some() {
				ctx.report_peer(who, Severity::Useless("Unknown Polkadot-specific reason"));
				return
			}

			let collator_role = self.collators.on_new_collator(acc_id.clone(), para_id.clone());

			peer_info.collator_state.set_role(collator_role, |msg| send_polkadot_message(
				ctx,
				who,
				msg,
			));
		}

		if let (true, &Some(ref consensus)) = (send_key, &self.live_consensus) {
			peer_info.collator_state.send_key(consensus.local_session_key, |msg| send_polkadot_message(
				ctx,
				who,
				msg,
			));
		}

		self.peers.insert(who, peer_info);
		self.consensus_gossip.new_peer(ctx, who, status.roles);
		self.dispatch_pending_requests(ctx);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, who: NodeIndex) {
		if let Some(info) = self.peers.remove(&who) {
			if let Some((acc_id, _)) = info.collating_for {
				let new_primary = self.collators.on_disconnect(acc_id)
					.and_then(|new_primary| self.collator_peer(new_primary));

				if let Some((new_primary, primary_info)) = new_primary {
					primary_info.collator_state.set_role(Role::Primary, |msg| send_polkadot_message(
						ctx,
						new_primary,
						msg,
					));
				}
			}

			if let Some(validator_key) = info.validator_key {
				self.validators.remove(&validator_key);
				self.local_collations.on_disconnect(&validator_key);
			}

			{
				let pending = &mut self.pending;
				self.in_flight.retain(|&(_, ref peer), val| {
					let retain = peer != &who;
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
			self.consensus_gossip.peer_disconnected(ctx, who);
			self.dispatch_pending_requests(ctx);
		}
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, who: NodeIndex, message: message::Message<Block>) {
		match message {
			generic_message::Message::BftMessage(msg) => {
				trace!(target: "p_net", "Polkadot BFT message from {}: {:?}", who, msg);
				// TODO: check signature here? what if relevant block is unknown?
				self.consensus_gossip.on_bft_message(ctx, who, msg)
			}
			generic_message::Message::ChainSpecific(raw) => {
				match Message::decode(&mut raw.as_slice()) {
					Some(msg) => self.on_polkadot_message(ctx, who, raw, msg),
					None => {
						trace!(target: "p_net", "Bad message from {}", who);
						ctx.report_peer(who, Severity::Bad("Invalid polkadot protocol message format"));
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
		self.local_collations.collect_garbage(None);
		self.dispatch_pending_requests(ctx);

		for collator_action in self.collators.maintain_peers() {
			match collator_action {
				Action::Disconnect(collator) => self.disconnect_bad_collator(ctx, collator),
				Action::NewRole(account_id, role) => if let Some((collator, info)) = self.collator_peer(account_id) {
					info.collator_state.set_role(role, |msg| send_polkadot_message(
						ctx,
						collator,
						msg,
					))
				},
			}
		}
	}

	fn on_block_imported(&mut self, _ctx: &mut Context<Block>, hash: Hash, header: &Header) {
		self.collators.collect_garbage(Some(&hash));
		self.local_collations.collect_garbage(Some(&header.parent_hash));
	}
}

impl PolkadotProtocol {
	// we received a collation from a peer
	fn on_collation(&mut self, ctx: &mut Context<Block>, from: NodeIndex, relay_parent: Hash, collation: Collation) {
		let collation_para = collation.receipt.parachain_index;
		let collated_acc = collation.receipt.collator;

		match self.peers.get(&from) {
			None => ctx.report_peer(from, Severity::Useless("Unknown Polkadot specific reason")),
			Some(peer_info) => match peer_info.collating_for {
				None => ctx.report_peer(from, Severity::Bad("Sent collation without registering collator intent")),
				Some((ref acc_id, ref para_id)) => {
					let structurally_valid = para_id == &collation_para && acc_id == &collated_acc;
					if structurally_valid && collation.receipt.check_signature().is_ok() {
						debug!(target: "p_net", "Received collation for parachain {:?} from peer {}", para_id, from);
						self.collators.on_collation(acc_id.clone(), relay_parent, collation)
					} else {
						ctx.report_peer(from, Severity::Bad("Sent malformed collation"))
					};
				}
			},
		}
	}

	fn await_collation(&mut self, relay_parent: Hash, para_id: ParaId) -> oneshot::Receiver<Collation> {
		let (tx, rx) = oneshot::channel();
		debug!(target: "p_net", "Attempting to get collation for parachain {:?} on relay parent {:?}", para_id, relay_parent);
		self.collators.await_collation(relay_parent, para_id, tx);
		rx
	}

	// get connected peer with given account ID for collation.
	fn collator_peer(&mut self, account_id: AccountId) -> Option<(NodeIndex, &mut PeerInfo)> {
		let check_info = |info: &PeerInfo| info
			.collating_for
			.as_ref()
			.map_or(false, |&(ref acc_id, _)| acc_id == &account_id);

		self.peers
			.iter_mut()
			.filter(|&(_, ref info)| check_info(&**info))
			.map(|(who, info)| (*who, info))
			.next()
	}

	// disconnect a collator by account-id.
	fn disconnect_bad_collator(&mut self, ctx: &mut Context<Block>, account_id: AccountId) {
		if let Some((who, _)) = self.collator_peer(account_id) {
			ctx.report_peer(who, Severity::Bad("Consensus layer determined the given collator misbehaved"))
		}
	}
}

impl PolkadotProtocol {
	/// Add a local collation and broadcast it to the necessary peers.
	pub fn add_local_collation(
		&mut self,
		ctx: &mut Context<Block>,
		relay_parent: Hash,
		targets: HashSet<SessionKey>,
		collation: Collation,
	) {
		debug!(target: "p_net", "Importing local collation on relay parent {:?} and parachain {:?}",
			relay_parent, collation.receipt.parachain_index);

		for (primary, cloned_collation) in self.local_collations.add_collation(relay_parent, targets, collation.clone()) {
			match self.validators.get(&primary) {
				Some(who) => {
					debug!(target: "p_net", "Sending local collation to {:?}", primary);
					send_polkadot_message(
						ctx,
						*who,
						Message::Collation(relay_parent, cloned_collation),
					)
				},
				None =>
					warn!(target: "polkadot_network", "Encountered tracked but disconnected validator {:?}", primary),
			}
		}
	}

	/// register availability store.
	pub fn register_availability_store(&mut self, extrinsic_store: ::av_store::Store) {
		self.extrinsic_store = Some(extrinsic_store);
	}
}
