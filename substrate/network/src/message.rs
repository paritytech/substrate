// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Network packet message types. These get serialized and put into the lower level protocol payload.

use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use codec::{Encode, Decode, Input, Output};
pub use self::generic::{BlockAnnounce, RemoteCallRequest, ConsensusVote, SignedConsensusVote, FromBlock};

/// A unique ID of a request.
pub type RequestId = u64;

/// Type alias for using the message type using block type parameters.
pub type Message<B> = generic::Message<
	B,
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
	<B as BlockT>::Extrinsic,
>;

/// Type alias for using the status type using block type parameters.
pub type Status<B> = generic::Status<
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
>;

/// Type alias for using the block request type using block type parameters.
pub type BlockRequest<B> = generic::BlockRequest<
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
>;

/// Type alias for using the localized bft message type using block type parameters.
pub type LocalizedBftMessage<B> = generic::LocalizedBftMessage<
	B,
	<B as BlockT>::Hash,
>;

/// Type alias for using the BlockData type using block type parameters.
pub type BlockData<B> = generic::BlockData<
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<B as BlockT>::Extrinsic,
>;

/// Type alias for using the BlockResponse type using block type parameters.
pub type BlockResponse<B> = generic::BlockResponse<
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<B as BlockT>::Extrinsic,
>;

/// Type alias for using the BftMessage type using block type parameters.
pub type BftMessage<B> = generic::BftMessage<
	B,
	<B as BlockT>::Hash,
>;

/// Type alias for using the SignedConsensusProposal type using block type parameters.
pub type SignedConsensusProposal<B> = generic::SignedConsensusProposal<
	B,
	<B as BlockT>::Hash,
>;

/// Type alias for using the SignedConsensusProposal type using block type parameters.
pub type SignedConsensusMessage<B> = generic::SignedConsensusProposal<
	B,
	<B as BlockT>::Hash,
>;

/// A set of transactions.
pub type Transactions<E> = Vec<E>;

/// Bits of block data and associated artefacts to request.
bitflags! {
	/// Node roles bitmask.
	pub struct BlockAttributes: u8 {
		/// Include block header.
		const HEADER = 0b00000001;
		/// Include block body.
		const BODY = 0b00000010;
		/// Include block receipt.
		const RECEIPT = 0b00000100;
		/// Include block message queue.
		const MESSAGE_QUEUE = 0b00001000;
		/// Include a justification for the block.
		const JUSTIFICATION = 0b00010000;
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
/// Block enumeration direction.
pub enum Direction {
	/// Enumerate in ascending order (from child to parent).
	Ascending = 0,
	/// Enumerate in descendfing order (from parent to canonical child).
	Descending = 1,
}

/// Remote call response.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RemoteCallResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Execution proof.
	pub proof: Vec<Vec<u8>>,
}

impl Encode for RemoteCallResponse {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.id);
		dest.push(&self.proof);
	}
}

impl Decode for RemoteCallResponse {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(RemoteCallResponse {
			id: Decode::decode(input)?,
			proof: Decode::decode(input)?,
		})
	}
}
	
/// Generic types.
pub mod generic {
	use primitives::AuthorityId;
	use codec::{Decode, Encode, Input, Output};
	use runtime_primitives::bft::Justification;
	use ed25519;
	use service::Roles;
	use super::{BlockAttributes, RemoteCallResponse, RequestId, Transactions, Direction};


	/// Block data sent in the response.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct BlockData<Header, Hash, Extrinsic> {
		/// Block header hash.
		pub hash: Hash,
		/// Block header if requested.
		pub header: Option<Header>,
		/// Block body if requested.
		pub body: Option<Vec<Extrinsic>>,
		/// Block receipt if requested.
		pub receipt: Option<Vec<u8>>,
		/// Block message queue if requested.
		pub message_queue: Option<Vec<u8>>,
		/// Justification if requested.
		pub justification: Option<Justification<Hash>>,
	}

	impl<Header: Encode, Hash: Encode, Extrinsic: Encode> Encode for BlockData<Header, Hash, Extrinsic> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.hash);
			dest.push(&self.header);
			dest.push(&self.body);
			dest.push(&self.receipt);
			dest.push(&self.message_queue);
			dest.push(&self.justification);
		}
	}

	impl<Header: Decode, Hash: Decode, Extrinsic: Decode> Decode for BlockData<Header, Hash, Extrinsic> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(BlockData {
				hash: Decode::decode(input)?,
				header: Decode::decode(input)?,
				body: Decode::decode(input)?,
				receipt: Decode::decode(input)?,
				message_queue: Decode::decode(input)?,
				justification: Decode::decode(input)?,
			})
		}
	}

	/// Identifies starting point of a block sequence.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum FromBlock<Hash, Number> {
		/// Start with given hash.
		Hash(Hash),
		/// Start with given block number.
		Number(Number),
	}

	impl<Hash: Encode, Number: Encode> Encode for FromBlock<Hash, Number> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			match *self {
				FromBlock::Hash(ref h) => {
					dest.push_byte(0);
					dest.push(h);
				}
				FromBlock::Number(ref n) => {
					dest.push_byte(1);
					dest.push(n);
				}
			}
		}
	}

	impl<Hash: Decode, Number: Decode> Decode for FromBlock<Hash, Number> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				0 => Some(FromBlock::Hash(Decode::decode(input)?)),
				1 => Some(FromBlock::Number(Decode::decode(input)?)),
				_ => None,
			}
		}
	}

	/// Communication that can occur between participants in consensus.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum BftMessage<Block, Hash> {
		/// A consensus message (proposal or vote)
		Consensus(SignedConsensusMessage<Block, Hash>),
		/// Auxiliary communication (just proof-of-lock for now).
		Auxiliary(Justification<Hash>),
	}

	impl<Block: Encode, Hash: Encode> Encode for BftMessage<Block, Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			match *self {
				BftMessage::Consensus(ref h) => {
					dest.push_byte(0);
					dest.push(h);
				}
				BftMessage::Auxiliary(ref n) => {
					dest.push_byte(1);
					dest.push(n);
				}
			}
		}
	}

	impl<Block: Decode, Hash: Decode> Decode for BftMessage<Block, Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				0 => Some(BftMessage::Consensus(Decode::decode(input)?)),
				1 => Some(BftMessage::Auxiliary(Decode::decode(input)?)),
				_ => None,
			}
		}
	}

	/// BFT Consensus message with parent header hash attached to it.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct LocalizedBftMessage<Block, Hash> {
		/// Consensus message.
		pub message: BftMessage<Block, Hash>,
		/// Parent header hash.
		pub parent_hash: Hash,
	}

	impl<Block: Encode, Hash: Encode> Encode for LocalizedBftMessage<Block, Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.message);
			dest.push(&self.parent_hash);
		}
	}

	impl<Block: Decode, Hash: Decode> Decode for LocalizedBftMessage<Block, Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(LocalizedBftMessage {
				message: Decode::decode(input)?,
				parent_hash: Decode::decode(input)?,
			})
		}
	}
	
	/// A localized proposal message. Contains two signed pieces of data.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct SignedConsensusProposal<Block, Hash> {
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

	impl<Block: Encode, Hash: Encode> Encode for SignedConsensusProposal<Block, Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.round_number);
			dest.push(&self.proposal);
			dest.push(&self.digest);
			dest.push(&self.sender);
			dest.push(&self.digest_signature);
			dest.push(&self.full_signature);
		}
	}

	impl<Block: Decode, Hash: Decode> Decode for SignedConsensusProposal<Block, Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(SignedConsensusProposal {
				round_number: Decode::decode(input)?,
				proposal: Decode::decode(input)?,
				digest: Decode::decode(input)?,
				sender: Decode::decode(input)?,
				digest_signature: Decode::decode(input)?,
				full_signature: Decode::decode(input)?,
			})
		}
	}

	/// A localized vote message, including the sender.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct SignedConsensusVote<H> {
		/// The message sent.
		pub vote: ConsensusVote<H>,
		/// The sender of the message
		pub sender: AuthorityId,
		/// The signature of the message.
		pub signature: ed25519::Signature,
	}

	impl<Hash: Encode> Encode for SignedConsensusVote<Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.vote);
			dest.push(&self.sender);
			dest.push(&self.signature);
		}
	}

	impl<Hash: Decode> Decode for SignedConsensusVote<Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(SignedConsensusVote {
				vote: Decode::decode(input)?,
				sender: Decode::decode(input)?,
				signature: Decode::decode(input)?,
			})
		}
	}
	
	/// Votes during a consensus round.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum ConsensusVote<H> {
		/// Prepare to vote for proposal with digest D.
		Prepare(u32, H),
		/// Commit to proposal with digest D..
		Commit(u32, H),
		/// Propose advancement to a new round.
		AdvanceRound(u32),
	}

	impl<Hash: Encode> Encode for ConsensusVote<Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			match *self {
				ConsensusVote::Prepare(ref r, ref h) => {
					dest.push_byte(0);
					dest.push(r);
					dest.push(h);
				}
				ConsensusVote::Commit(ref r, ref h) => {
					dest.push_byte(1);
					dest.push(r);
					dest.push(h);
				}
				ConsensusVote::AdvanceRound(ref r) => {
					dest.push_byte(2);
					dest.push(r);
				}
			}
		}
	}

	impl<Hash: Decode> Decode for ConsensusVote<Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				0 => Some(ConsensusVote::Prepare(Decode::decode(input)?, Decode::decode(input)?)),
				1 => Some(ConsensusVote::Commit(Decode::decode(input)?, Decode::decode(input)?)),
				2 => Some(ConsensusVote::AdvanceRound(Decode::decode(input)?)),
				_ => None,
			}
		}
	}

	/// A localized message.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum SignedConsensusMessage<Block, Hash> {
		/// A proposal.
		Propose(SignedConsensusProposal<Block, Hash>),
		/// A vote.
		Vote(SignedConsensusVote<Hash>),
	}

	impl<Block: Encode, Hash: Encode> Encode for SignedConsensusMessage<Block, Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			match *self {
				SignedConsensusMessage::Propose(ref m) => {
					dest.push_byte(0);
					dest.push(m);
				}
				SignedConsensusMessage::Vote(ref m) => {
					dest.push_byte(1);
					dest.push(m);
				}
			}
		}
	}

	impl<Block: Decode, Hash: Decode> Decode for SignedConsensusMessage<Block, Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				0 => Some(SignedConsensusMessage::Propose(Decode::decode(input)?)),
				1 => Some(SignedConsensusMessage::Vote(Decode::decode(input)?)),
				_ => None,
			}
		}
	}
	
	/// A network message.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum Message<Block, Header, Hash, Number, Extrinsic> {
		/// Status packet.
		Status(Status<Hash, Number>),
		/// Block request.
		BlockRequest(BlockRequest<Hash, Number>),
		/// Block response.
		BlockResponse(BlockResponse<Header, Hash, Extrinsic>),
		/// Block announce.
		BlockAnnounce(BlockAnnounce<Header>),
		/// Transactions.
		Transactions(Transactions<Extrinsic>),
		/// BFT Consensus statement.
		BftMessage(LocalizedBftMessage<Block, Hash>),
		/// Remote method call request.
		RemoteCallRequest(RemoteCallRequest<Hash>),
		/// Remote method call response.
		RemoteCallResponse(RemoteCallResponse),
		/// Chain-specific message
		ChainSpecific(Vec<u8>),
	}

	impl<Block: Encode, Header: Encode, Hash: Encode, Number: Encode, Extrinsic: Encode> Encode
		for Message<Block, Header, Hash, Number, Extrinsic>
	{
		fn encode_to<T: Output>(&self, dest: &mut T) {
			match *self {
				Message::Status(ref m) => {
					dest.push_byte(0);
					dest.push(m);
				}
				Message::BlockRequest(ref m) => {
					dest.push_byte(1);
					dest.push(m);
				}
				Message::BlockResponse(ref m) => {
					dest.push_byte(2);
					dest.push(m);
				}
				Message::BlockAnnounce(ref m) => {
					dest.push_byte(3);
					dest.push(m);
				}
				Message::Transactions(ref m) => {
					dest.push_byte(4);
					dest.push(m);
				}
				Message::BftMessage(ref m) => {
					dest.push_byte(5);
					dest.push(m);
				}
				Message::RemoteCallRequest(ref m) => {
					dest.push_byte(6);
					dest.push(m);
				}
				Message::RemoteCallResponse(ref m) => {
					dest.push_byte(7);
					dest.push(m);
				}
				Message::ChainSpecific(ref m) => {
					dest.push_byte(255);
					dest.push(m);
				}
			}
		}
	}

	impl<Block: Decode, Header: Decode, Hash: Decode, Number: Decode, Extrinsic: Decode> Decode
		for Message<Block, Header, Hash, Number, Extrinsic>
	{
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				0 => Some(Message::Status(Decode::decode(input)?)),
				1 => Some(Message::BlockRequest(Decode::decode(input)?)),
				2 => Some(Message::BlockResponse(Decode::decode(input)?)),
				3 => Some(Message::BlockAnnounce(Decode::decode(input)?)),
				4 => Some(Message::Transactions(Decode::decode(input)?)),
				5 => Some(Message::BftMessage(Decode::decode(input)?)),
				6 => Some(Message::RemoteCallResponse(Decode::decode(input)?)),
				7 => Some(Message::RemoteCallResponse(Decode::decode(input)?)),
				255 => Some(Message::ChainSpecific(Decode::decode(input)?)),
				_ => None,
			}
		}
	}

	/// Status sent on connection.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct Status<Hash, Number> {
		/// Protocol version.
		pub version: u32,
		/// Supported roles.
		pub roles: Roles,
		/// Best block number.
		pub best_number: Number,
		/// Best block hash.
		pub best_hash: Hash,
		/// Genesis block hash.
		pub genesis_hash: Hash,
		/// Chain-specific status.
		pub chain_status: Vec<u8>,
	}

	impl<Hash: Encode, Number: Encode> Encode for Status<Hash, Number> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.version);
			dest.push_byte(self.roles.bits());
			dest.push(&self.best_number);
			dest.push(&self.best_hash);
			dest.push(&self.genesis_hash);
			dest.push(&self.chain_status);
		}
	}

	impl<Hash: Decode, Number: Decode> Decode for Status<Hash, Number> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(Status {
				version: Decode::decode(input)?,
				roles: Roles::from_bits(input.read_byte()?)?,
				best_number: Decode::decode(input)?,
				best_hash: Decode::decode(input)?,
				genesis_hash: Decode::decode(input)?,
				chain_status: Decode::decode(input)?,
			})
		}
	}
	
	/// Request block data from a peer.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct BlockRequest<Hash, Number> {
		/// Unique request id.
		pub id: RequestId,
		/// Bits of block data to request.
		pub fields: BlockAttributes,
		/// Start from this block.
		pub from: FromBlock<Hash, Number>,
		/// End at this block. An implementation defined maximum is used when unspecified.
		pub to: Option<Hash>,
		/// Sequence direction.
		pub direction: Direction,
		/// Maximum number of blocks to return. An implementation defined maximum is used when unspecified.
		pub max: Option<u32>,
	}

	impl<Hash: Encode, Number: Encode> Encode for BlockRequest<Hash, Number> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.id);
			dest.push_byte(self.fields.bits());
			dest.push(&self.from);
			dest.push(&self.to);
			dest.push_byte(self.direction as u8);
			dest.push(&self.max);
		}
	}

	impl<Hash: Decode, Number: Decode> Decode for BlockRequest<Hash, Number> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(BlockRequest {
				id: Decode::decode(input)?,
				fields: BlockAttributes::from_bits(input.read_byte()?)?,
				from: Decode::decode(input)?,
				to: Decode::decode(input)?,
				direction: match input.read_byte()? {
					x if x == Direction::Ascending as u8 => Some(Direction::Ascending),
					x if x == Direction::Descending as u8 => Some(Direction::Descending),
					_ => None,
				}?,
				max: Decode::decode(input)?,
			})
		}
	}

	/// Response to `BlockRequest`
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct BlockResponse<Header, Hash, Extrinsic> {
		/// Id of a request this response was made for.
		pub id: RequestId,
		/// Block data for the requested sequence.
		pub blocks: Vec<BlockData<Header, Hash, Extrinsic>>,
	}

	impl<Header: Encode, Hash: Encode, Extrinsic: Encode> Encode for BlockResponse<Header, Hash, Extrinsic> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.id);
			dest.push(&self.blocks)
		}
	}

	impl<Header: Decode, Hash: Decode, Extrinsic: Decode> Decode for BlockResponse<Header, Hash, Extrinsic> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(BlockResponse {
				id: Decode::decode(input)?,
				blocks: Decode::decode(input)?,
			})
		}
	}

	/// Announce a new complete relay chain block on the network.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct BlockAnnounce<H> {
		/// New block header.
		pub header: H,
	}

	impl<Header: Encode> Encode for BlockAnnounce<Header> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.header);
		}
	}

	impl<Header: Decode> Decode for BlockAnnounce<Header> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(BlockAnnounce {
				header: Decode::decode(input)?,
			})
		}
	}

	#[derive(Debug, PartialEq, Eq, Clone)]
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

	impl<Hash: Encode> Encode for RemoteCallRequest<Hash> {
		fn encode_to<T: Output>(&self, dest: &mut T) {
			dest.push(&self.id);
			dest.push(&self.block);
			dest.push(self.method.as_bytes());
			dest.push(&self.data);
		}
	}

	impl<Hash: Decode> Decode for RemoteCallRequest<Hash> {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(RemoteCallRequest {
				id: Decode::decode(input)?,
				block: Decode::decode(input)?,
				method: String::from_utf8_lossy(&Vec::decode(input)?).into(),
				data: Decode::decode(input)?,
			})
		}
	}
}
