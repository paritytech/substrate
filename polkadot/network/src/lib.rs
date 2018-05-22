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
	pub parent_hash: HeaderHash,
	/// The statement.
	pub statement: UnsignedStatement,
	/// The signature.
	pub signature: ed25519::Signature,
	/// The sender.
	pub sender: AuthorityId,
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
