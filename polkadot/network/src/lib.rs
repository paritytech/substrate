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
extern crate tokio;

#[macro_use]
extern crate log;

use codec::Slicable;
use polkadot_consensus::SignedStatement;
use polkadot_primitives::{Block, Hash};
use polkadot_primitives::parachain::Id as ParaId;
use substrate_network::{PeerId, RequestId, Context};
use substrate_network::consensus_gossip::ConsensusGossip;
use substrate_network::{message, generic_message};
use substrate_network::specialization::Specialization;
use substrate_network::StatusMessage as GenericFullStatus;

use std::collections::HashMap;

pub mod consensus;

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

/// Request candidate block data from a peer.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CandidateRequest {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate receipt hash.
	pub hash: Hash,
}

/// Candidate block data response.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CandidateResponse {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate data. Empty if the peer does not have the candidate anymore.
	pub data: Option<Vec<u8>>,
}

struct PeerInfo {
	status: Status,
}

/// Polkadot protocol attachment for substrate.
pub struct PolkadotProtocol {
	peers: HashMap<PeerId, PeerInfo>,
	consensus_gossip: ConsensusGossip<Block>,
	collators: HashMap<ParaId, Vec<PeerId>>,
	collating_for: Option<ParaId>,
}

/// Polkadot-specific messages.
#[derive(Serialize, Deserialize)]
pub enum Message {
	/// signed statement and localized parent hash.
	Statement(Hash, SignedStatement),
}

impl Specialization<Block> for PolkadotProtocol {
	fn status(&self) -> Vec<u8> {
		Status { collating_for: self.collating_for.clone() }.encode()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, status: FullStatus) {
		let local_status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				ctx.disable_peer(peer_id);
				return;
			}
		};

		if let Some(ref para_id) = local_status.collating_for {
			self.collators.entry(para_id.clone())
				.or_insert_with(Vec::new)
				.push(peer_id);
		}

		self.peers.insert(peer_id, PeerInfo { status: local_status });
		self.consensus_gossip.new_peer(ctx, peer_id, &status.roles);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, peer_id: PeerId) {
		if let Some(info) = self.peers.remove(&peer_id) {
			if let Some(collators) = info.status.collating_for.and_then(|id| self.collators.get_mut(&id)) {
				if let Some(pos) = collators.iter().position(|x| x == &peer_id) {
					collators.swap_remove(pos);
				}
			}

			self.consensus_gossip.peer_disconnected(ctx, peer_id);
		}
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, peer_id: PeerId, message: message::Message<Block>) {
		match message {
			generic_message::Message::BftMessage(msg) => {
				// TODO: check signature here? what if relevant block is unknown?
				self.consensus_gossip.on_bft_message(ctx, peer_id, msg)
			}
			generic_message::Message::ChainSpecific(raw) => {
				let msg = match serde_json::from_slice(&raw) {
					Ok(msg) => msg,
					Err(e) => {
						trace!(target: "p_net", "Bad message from {}: {}", peer_id, e);
						ctx.disable_peer(peer_id);
						return;
					}
				};

				match msg {
					Message::Statement(parent_hash, statement) =>
						self.consensus_gossip.on_chain_specific(ctx, peer_id, raw, parent_hash),
				}
			}
			_ => {}
		}
	}

	fn on_abort(&mut self) {
		self.consensus_gossip.abort();
	}
}
