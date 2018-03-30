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

//! Network packet message types. These get serialized and put into the lower level protocol payload.

use primitives::{AuthorityId, Hash};
use primitives::block::{Number as BlockNumber, HeaderHash, Header, Body, Block};
use primitives::bft::Justification;
use service::Role as RoleFlags;
use ed25519;

pub type RequestId = u64;
type Bytes = Vec<u8>;

/// Configured node role.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Role {
	/// Full relay chain client with no additional responsibilities.
	Full,
	/// Relay chain light client.
	Light,
	/// Parachain validator.
	Validator,
	/// Parachain collator.
	Collator,
}

impl Role {
	/// Convert enum to service flags.
	pub fn as_flags(roles: &[Role]) -> RoleFlags {
		let mut flags = RoleFlags::NONE;
		for r in roles {
			match *r {
				Role::Full => flags = flags | RoleFlags::FULL,
				Role::Light => flags = flags | RoleFlags::LIGHT,
				Role::Validator => flags = flags | RoleFlags::VALIDATOR,
				Role::Collator => flags = flags | RoleFlags::COLLATOR,
			}
		}
		flags
	}
}

impl From<RoleFlags> for Vec<Role> where {
	fn from(flags: RoleFlags) -> Vec<Role> {
		let mut roles = Vec::new();
		if !(flags & RoleFlags::FULL).is_empty() {
			roles.push(Role::Full);
		}
		if !(flags & RoleFlags::LIGHT).is_empty() {
			roles.push(Role::Light);
		}
		if !(flags & RoleFlags::VALIDATOR).is_empty() {
			roles.push(Role::Validator);
		}
		if !(flags & RoleFlags::COLLATOR).is_empty() {
			roles.push(Role::Collator);
		}
		roles
	}
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize, Copy, Clone)]
/// Bits of block data and associated artefacts to request.
pub enum BlockAttribute {
	/// Include block header.
	Header,
	/// Include block body.
	Body,
	/// Include block receipt.
	Receipt,
	/// Include block message queue.
	MessageQueue,
	/// Include a justification for the block.
	Justification,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Block data sent in the response.
pub struct BlockData {
	/// Block header hash.
	pub hash: HeaderHash,
	/// Block header if requested.
	pub header: Option<Header>,
	/// Block body if requested.
	pub body: Option<Body>,
	/// Block receipt if requested.
	pub receipt: Option<Bytes>,
	/// Block message queue if requested.
	pub message_queue: Option<Bytes>,
	/// Justification if requested.
	pub justification: Option<Justification>,
}

#[serde(untagged)]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Identifies starting point of a block sequence.
pub enum FromBlock {
	/// Start with given hash.
	Hash(HeaderHash),
	/// Start with given block number.
	Number(BlockNumber),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Block enumeration direction.
pub enum Direction {
	/// Enumerate in ascending order (from child to parent).
	Ascending,
	/// Enumerate in descendfing order (from parent to canonical child).
	Descending,
}

/// A set of transactions.
pub type Transactions = Vec<Vec<u8>>;

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
	/// The statement.
	pub statement: UnsignedStatement,
	/// The signature.
	pub signature: ed25519::Signature,
	/// The sender.
	pub sender: AuthorityId,
}

/// Communication that can occur between participants in consensus.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum BftMessage {
	/// A consensus message (proposal or vote)
	Consensus(SignedConsensusMessage),
	/// Auxiliary communication (just proof-of-lock for now).
	Auxiliary(Justification),
}

/// A localized proposal message. Contains two signed pieces of data.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct SignedConsensusProposal {
	/// The round number.
	pub round_number: u32,
	/// The proposal sent.
	pub proposal: Block,
	/// The digest of the proposal.
	pub digest: Hash,
	/// The sender of the proposal
	pub sender: AuthorityId,
	/// The signature on the message (propose, round number, digest)
	pub digest_signature: ed25519::Signature,
	/// The signature on the message (propose, round number, proposal)
	pub full_signature: ed25519::Signature,
}

/// A localized vote message, including the sender.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct SignedConsensusVote {
	/// The message sent.
	pub vote: ConsensusVote,
	/// The sender of the message
	pub sender: AuthorityId,
	/// The signature of the message.
	pub signature: ed25519::Signature,
}

/// Votes during a consensus round.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum ConsensusVote {
	/// Prepare to vote for proposal with digest D.
	Prepare(u32, Hash),
	/// Commit to proposal with digest D..
	Commit(u32, Hash),
	/// Propose advancement to a new round.
	AdvanceRound(u32),
}

/// A localized message.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum SignedConsensusMessage {
	/// A proposal.
	Propose(SignedConsensusProposal),
	/// A vote.
	Vote(SignedConsensusVote),
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// A network message.
pub enum Message {
	/// Status packet.
	Status(Status),
	/// Block request.
	BlockRequest(BlockRequest),
	/// Block response.
	BlockResponse(BlockResponse),
	/// Block announce.
	BlockAnnounce(BlockAnnounce),
	/// Transactions.
	Transactions(Transactions),
	/// Consensus statement.
	Statement(Statement),
	/// Candidate data request.
	CandidateRequest(CandidateRequest),
	/// Candidate response.
	CandidateResponse(CandidateResponse),
	/// BFT Consensus statement.
	BftMessage(BftMessage),
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Status {
	/// Protocol version.
	pub version: u32,
	/// Supported roles.
	pub roles: Vec<Role>,
	/// Best block number.
	pub best_number: BlockNumber,
	/// Best block hash.
	pub best_hash: HeaderHash,
	/// Genesis block hash.
	pub genesis_hash: HeaderHash,
	/// Signatue of `best_hash` made with validator address. Required for the validator role.
	pub validator_signature: Option<ed25519::Signature>,
	/// Validator address. Required for the validator role.
	pub validator_id: Option<AuthorityId>,
	/// Parachain id. Required for the collator role.
	pub parachain_id: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Request block data from a peer.
pub struct BlockRequest {
	/// Unique request id.
	pub id: RequestId,
	/// Bits of block data to request.
	pub fields: Vec<BlockAttribute>,
	/// Start from this block.
	pub from: FromBlock,
	/// End at this block. An implementation defined maximum is used when unspecified.
	pub to: Option<HeaderHash>,
	/// Sequence direction.
	pub direction: Direction,
	/// Maximum number of blocks to return. An implementation defined maximum is used when unspecified.
	pub max: Option<u32>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Request candidate block data from a peer.
pub struct CandidateRequest {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate receipt hash.
	pub hash: Hash,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Candidate block data response.
pub struct CandidateResponse {
	/// Unique request id.
	pub id: RequestId,
	/// Candidate data. Empty if the peer does not have the candidate anymore.
	pub data: Option<Vec<u8>>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// Response to `BlockRequest`
pub struct BlockResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Block data for the requested sequence.
	pub blocks: Vec<BlockData>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// Announce a new complete relay chain block on the network.
pub struct BlockAnnounce {
	/// New block header.
	pub header: Header,
}
