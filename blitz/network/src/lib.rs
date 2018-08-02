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

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_network;

extern crate substrate_primitives;
// extern crate polkadot_consensus as consensus;
extern crate blitz_primitives;
extern crate ed25519;
extern crate futures;

#[macro_use]
extern crate serde_derive;
extern crate serde_json;

#[macro_use]
extern crate log;

mod message;

// TODO [dk] move it to state probably
pub mod transaction;

use message::BlitzMessage;
use codec::{Encode, Decode};
use substrate_primitives::{AuthorityId};
use substrate_network::{NodeIndex, RequestId, Context, Severity};
use substrate_network::specialization::Specialization;
use substrate_network::StatusMessage as GenericFullStatus;
use blitz_primitives::{Block, Hash};

use std::collections::HashMap;

/// Blitz protocol id.
pub const BLITZ_PROTOCOL_ID: ::substrate_network::ProtocolId = *b"blz";

/// Specialization of the network service for the polkadot protocol.
pub type NetworkService = ::substrate_network::Service<Block, BlitzProtocol>;

type FullStatus = GenericFullStatus<Block>;

/// Status of a Polkadot node.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Status {
	// collating_for: Option<ParaId>,
}

impl Encode for Status {
	fn encode_to<T: codec::Output>(&self, dest: &mut T) {
		// match self.collating_for {
		// 	Some(ref details) => {
		// 		dest.push_byte(1);
		// 		dest.push(details);
		// 	}
		// 	None => {
		// 		dest.push_byte(0);
		// 	}
		// }
		unimplemented!()
	}
}

impl Decode for Status {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		// let collating_for = match input.read_byte()? {
		// 	0 => None,
		// 	1 => Some(Decode::decode(input)?),
		// 	_ => return None,
		// };
		// Some(Status { collating_for })
		unimplemented!()
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

/// Statements circulated among peers.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnsignedStatement {
	/// Broadcast by a authority to indicate that this is his candidate for
	/// inclusion.
	///
	/// Broadcasting two different candidate messages per round is not allowed.
	Candidate(Vec<u8>),
	/// Broadcast by a authority to attest that the candidate with given digest
	/// is valid.
	Valid(Hash),
	/// Broadcast by a authority to attest that the auxiliary data for a candidate
	/// with given digest is available.
	Available(Hash),
	/// Broadcast by a authority to attest that the candidate with given digest
	/// is invalid.
	Invalid(Hash),
}

/// A signed statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Statement {
	/// Parent relay chain block header hash.
	pub parent_hash: Hash,
	/// The statement.
	pub statement: UnsignedStatement,
	/// The signature.
	pub signature: ed25519::Signature,
	/// The sender.
	pub sender: AuthorityId,
}

struct PeerInfo {
	status: Status,
}

/// Blitz protocol attachment for substrate.
#[derive(Default)]
pub struct BlitzProtocol {
	peers: HashMap<NodeIndex, PeerInfo>,
	// collators: HashMap<ParaId, Vec<NodeIndex>>,
	// collating_for: Option<ParaId>,
}

impl Specialization<Block> for BlitzProtocol {
	fn status(&self) -> Vec<u8> {
		Status { /*collating_for: self.collating_for.clone()*/ }.encode()
	}

	fn on_connect(&mut self, ctx: &mut Context<Block>, peer_id: NodeIndex, status: FullStatus) {
		let status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				ctx.report_peer(peer_id, Severity::Bad("could not decode status message"));
				return;
			}
		};

		// if let Some(ref para_id) = status.collating_for {
		// 	self.collators.entry(para_id.clone())
		// 		.or_insert_with(Vec::new)
		// 		.push(peer_id);
		// }

		self.peers.insert(peer_id, PeerInfo { status });
	}

	fn on_disconnect(&mut self, _ctx: &mut Context<Block>, peer_id: NodeIndex) {
		if let Some(info) = self.peers.remove(&peer_id) {
			/*if let Some(collators) = info.status.collating_for.and_then(|id| self.collators.get_mut(&id)) {
				if let Some(pos) = collators.iter().position(|x| x == &peer_id) {
					collators.swap_remove(pos);
				}
			}*/
		}
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, peer_id: NodeIndex, message: substrate_network::message::Message<Block>) {
		use substrate_network::generic_message::Message;

		match message {
			Message::BftMessage(bft_message) => {
				// TODO
			}

			Message::ChainSpecific(raw_data) => {
				let message: BlitzMessage = match serde_json::from_slice(&raw_data) {
					Ok(m) => m,
					Err(e) => {
						trace!(target: "b_net", "Bad message from {}: {}", peer_id, e);
						ctx.report_peer(peer_id, Severity::Bad("could not decode chain specific message"));
						return;
					}
				};

				// TODO process incoming blitz message
			}

			_ => {}
		}
	}
}

impl BlitzProtocol {
	fn send_message(ctx: &mut Context<Block>, peer_id: NodeIndex, message: BlitzMessage) {
		let data = serde_json::to_vec(&message).expect("serialization is infallible");
		ctx.send_message(peer_id, substrate_network::generic_message::Message::ChainSpecific(data));
	}
}
