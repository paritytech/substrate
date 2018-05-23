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

extern crate substrate_network;
extern crate substrate_primitives;
extern crate polkadot_primitives;
extern crate ed25519;

use substrate_primitives::Hash;
use substrate_network::{PeerId, RequestId};
use substrate_network::specialization::{Specialization, HandlerContext};

use polkadot_primitives::parachain::Id as ParaId;

use std::collections::HashMap;

/// Status of a Polkadot node.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Status {
	collating_for: Option<ParaId>,
}

/// Request candidate block data from a peer.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct CandidateRequest {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate receipt hash.
	pub hash: Hash,
}

/// Candidate block data response.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct CandidateResponse {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate data. Empty if the peer does not have the candidate anymore.
	pub data: Option<Vec<u8>>,
}

/// Statements circulated among peers.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
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
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
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

struct PeerInfo;

/// Polkadot protocol attachment for substrate.
pub struct PolkadotProtocol {
	peers: HashMap<PeerId, PeerInfo>,
	collators: HashMap<ParaId, PeerId>,
	collating_for: Option<ParaId>,
}

impl Specialization for PolkadotProtocol {
	fn status(&self) -> Vec<u8> {

	}

	fn on_peer_connected(&mut self, ctx: &mut HandlerContext, peer_id: PeerId, status: ::message::Status);

	fn on_peer_disconnected(&mut self, ctx: &mut HandlerContext, peer_id: PeerId);

	fn on_message(&mut self, ctx: &mut HandlerContext, peer_id: PeerId, message: Vec<u8>);
}
