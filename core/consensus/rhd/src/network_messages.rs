
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};


/// Type alias for using the localized bft message type using block type parameters.
pub type LocalizedBftMessage<B> = generic::LocalizedBftMessage<
	B,
	<B as BlockT>::Hash,
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


mod generic {
	/// Communication that can occur between participants in consensus.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum BftMessage<Block, Hash> {
		/// A consensus message (proposal or vote)
		Consensus(SignedConsensusMessage<Block, Hash>),
		/// Auxiliary communication (just proof-of-lock for now).
		Auxiliary(Justification<Hash>),
	}

	/// BFT Consensus message with parent header hash attached to it.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct LocalizedBftMessage<Block, Hash> {
		/// Consensus message.
		pub message: BftMessage<Block, Hash>,
		/// Parent header hash.
		pub parent_hash: Hash,
	}

	/// A localized proposal message. Contains two signed pieces of data.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
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

	/// A localized vote message, including the sender.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct SignedConsensusVote<H> {
		/// The message sent.
		pub vote: ConsensusVote<H>,
		/// The sender of the message
		pub sender: AuthorityId,
		/// The signature of the message.
		pub signature: ed25519::Signature,
	}

	/// Votes during a consensus round.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum ConsensusVote<H> {
		/// Prepare to vote for proposal with digest D.
		Prepare(u32, H),
		/// Commit to proposal with digest D..
		Commit(u32, H),
		/// Propose advancement to a new round.
		AdvanceRound(u32),
	}

	/// A localized message.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum SignedConsensusMessage<Block, Hash> {
		/// A proposal.
		Propose(SignedConsensusProposal<Block, Hash>),
		/// A vote.
		Vote(SignedConsensusVote<Hash>),
	}
}

