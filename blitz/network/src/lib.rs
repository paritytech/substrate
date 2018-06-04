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

mod message;
mod transaction;

use codec::Slicable;
use substrate_primitives::{AuthorityId, Hash};
use substrate_network::{PeerId, RequestId};
use substrate_network::specialization::{Specialization, HandlerContext};
use substrate_network::StatusMessage as FullStatus;

// use polkadot_primitives::parachain::Id as ParaId;

use std::collections::HashMap;

/// Blitz protocol id.
pub const BLITZ_PROTOCOL_ID: ::substrate_network::ProtocolId = *b"blz";

/// Specialization of the network service for the polkadot protocol.
pub type NetworkService = ::substrate_network::Service<BlitzProtocol>;

/// Status of a Polkadot node.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Status {
	// collating_for: Option<ParaId>,
}

impl Slicable for Status {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		// match self.collating_for {
		// 	Some(ref id) => {
		// 		v.push(1);
		// 		id.using_encoded(|s| v.extend(s));
		// 	}
		// 	None => {
		// 		v.push(0);
		// 	}
		// }
		v
	}

	fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
		// let collating_for = match input.read_byte()? {
		// 	0 => None,
		// 	// 1 => Some(ParaId::decode(input)?),
		// 	_ => return None,
		// };
		Some(Status { /* collating_for */ })
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
	peers: HashMap<PeerId, PeerInfo>,
	// collators: HashMap<ParaId, Vec<PeerId>>,
	// collating_for: Option<ParaId>,
}

impl Specialization for BlitzProtocol {
	fn status(&self) -> Vec<u8> {
		Status { /*collating_for: self.collating_for.clone()*/ }.encode()
	}

	fn on_peer_connected(&mut self, ctx: &mut HandlerContext, peer_id: PeerId, status: FullStatus) {
		let status = match Status::decode(&mut &status.chain_status[..]) {
			Some(status) => status,
			None => {
				ctx.disable_peer(peer_id);
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

	fn on_peer_disconnected(&mut self, _ctx: &mut HandlerContext, peer_id: PeerId) {
		if let Some(info) = self.peers.remove(&peer_id) {
			/*if let Some(collators) = info.status.collating_for.and_then(|id| self.collators.get_mut(&id)) {
				if let Some(pos) = collators.iter().position(|x| x == &peer_id) {
					collators.swap_remove(pos);
				}
			}*/
		}
	}

	fn on_message(&mut self, ctx: &mut HandlerContext, peer_id: PeerId, message: Vec<u8>) {
		let message: message::BlitzMessage = match serde_json::from_slice(&message) {
			Ok(m) => m,
			Err(e) => {
				//debug!("Invalid packet from {}: {}", peer_id, e);

				ctx.disable_peer(peer_id);
				return;
			}
		};

		// TODO [dk] process incoming message
	}
}
