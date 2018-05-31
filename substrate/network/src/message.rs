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

use primitives::AuthorityId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::bft::Justification;
use service::Role as RoleFlags;
use ed25519;

pub type RequestId = u64;
type Bytes = Vec<u8>;

/// Configured node role.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
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
pub struct BlockData<B: BlockT> {
	/// Block header hash.
	pub hash: B::Hash,
	/// Block header if requested.
	pub header: Option<B::Header>,
	/// Block body if requested.
	pub body: Option<Vec<B::Extrinsic>>,
	/// Block receipt if requested.
	pub receipt: Option<Bytes>,
	/// Block message queue if requested.
	pub message_queue: Option<Bytes>,
	/// Justification if requested.
	pub justification: Option<Justification<B::Hash>>,
}

#[serde(untagged)]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Identifies starting point of a block sequence.
pub enum FromBlock<B: BlockT> {
	/// Start with given hash.
	Hash(B::Hash),
	/// Start with given block number.
	Number(<B::Header as HeaderT>::Number),
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
pub type Transactions<B> = Vec<<B as BlockT>::Extrinsic>;

/// Communication that can occur between participants in consensus.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum BftMessage<B: BlockT> {
	/// A consensus message (proposal or vote)
	Consensus(SignedConsensusMessage<B>),
	/// Auxiliary communication (just proof-of-lock for now).
	Auxiliary(Justification<B::Hash>),
}

/// BFT Consensus message with parent header hash attached to it.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct LocalizedBftMessage<B: BlockT> {
	/// Consensus message.
	pub message: BftMessage<B>,
	/// Parent header hash.
	pub parent_hash: B::Hash,
}

/// A localized proposal message. Contains two signed pieces of data.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct SignedConsensusProposal<B: BlockT> {
	/// The round number.
	pub round_number: u32,
	/// The proposal sent.
	pub proposal: B,
	/// The digest of the proposal.
	pub digest: B::Hash,
	/// The sender of the proposal
	pub sender: AuthorityId,
	/// The signature on the message (propose, round number, digest)
	pub digest_signature: ed25519::Signature,
	/// The signature on the message (propose, round number, proposal)
	pub full_signature: ed25519::Signature,
}

/// A localized vote message, including the sender.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct SignedConsensusVote<H> {
	/// The message sent.
	pub vote: ConsensusVote<H>,
	/// The sender of the message
	pub sender: AuthorityId,
	/// The signature of the message.
	pub signature: ed25519::Signature,
}

/// Votes during a consensus round.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum ConsensusVote<H> {
	/// Prepare to vote for proposal with digest D.
	Prepare(u32, H),
	/// Commit to proposal with digest D..
	Commit(u32, H),
	/// Propose advancement to a new round.
	AdvanceRound(u32),
}

/// A localized message.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum SignedConsensusMessage<B: BlockT> {
	/// A proposal.
	Propose(SignedConsensusProposal<B>),
	/// A vote.
	Vote(SignedConsensusVote<B::Hash>),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// A network message.
pub enum Message<B: BlockT> {
	/// Status packet.
	Status(Status<B>),
	/// Block request.
	BlockRequest(BlockRequest<B>),
	/// Block response.
	BlockResponse(BlockResponse<B>),
	/// Block announce.
	BlockAnnounce(BlockAnnounce<B::Header>),
	/// Transactions.
	Transactions(Transactions<B>),
	/// BFT Consensus statement.
	BftMessage(LocalizedBftMessage<B>),
	/// Remote method call request.
	RemoteCallRequest(RemoteCallRequest<B::Hash>),
	/// Remote method call response.
	RemoteCallResponse(RemoteCallResponse),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Status<B: BlockT> {
	/// Protocol version.
	pub version: u32,
	/// Supported roles.
	pub roles: Vec<Role>,
	/// Best block number.
	pub best_number: <B::Header as HeaderT>::Number,
	/// Best block hash.
	pub best_hash: B::Hash,
	/// Genesis block hash.
	pub genesis_hash: B::Hash,
	/// Signatue of `best_hash` made with validator address. Required for the validator role.
	pub validator_signature: Option<ed25519::Signature>,
	/// Validator address. Required for the validator role.
	pub validator_id: Option<AuthorityId>,
	/// Parachain id. Required for the collator role.
	pub parachain_id: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Request block data from a peer.
pub struct BlockRequest<B: BlockT> {
	/// Unique request id.
	pub id: RequestId,
	/// Bits of block data to request.
	pub fields: Vec<BlockAttribute>,
	/// Start from this block.
	pub from: FromBlock<B>,
	/// End at this block. An implementation defined maximum is used when unspecified.
	pub to: Option<B::Hash>,
	/// Sequence direction.
	pub direction: Direction,
	/// Maximum number of blocks to return. An implementation defined maximum is used when unspecified.
	pub max: Option<u32>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Response to `BlockRequest`
pub struct BlockResponse<B: BlockT> {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Block data for the requested sequence.
	pub blocks: Vec<BlockData<B>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Announce a new complete relay chain block on the network.
pub struct BlockAnnounce<H> {
	/// New block header.
	pub header: H,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Remote call request.
pub struct RemoteCallRequest<H> {
	/// Unique request id.
	pub id: RequestId,
	/// Block at which to perform call.
	pub block: H,
	/// Method name.
	pub method: String,
	/// Call data.
	pub data: Vec<u8>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Remote call response.
pub struct RemoteCallResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Method return value.
	pub value: Vec<u8>,
	/// Execution proof.
	pub proof: Vec<Vec<u8>>,
}
