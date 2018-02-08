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

//! BFT Agreement based on a rotating proposer in different rounds.

mod accumulator;
pub mod generic;

#[cfg_attr(test, macro_use)]
extern crate futures;
extern crate substrate_primitives as primitives;
extern crate ed25519;

use ed25519::Signature;
use primitives::block::HeaderHash;
use primitives::{Block, AuthorityId};

use futures::{Stream, Sink, Future};

pub use generic::InputStreamConcluded;

/// Messages over the proposal.
/// Each message carries an associated round number.
pub type Message = generic::Message<Block, HeaderHash>;

/// Localized message type.
pub type LocalizedMessage = generic::LocalizedMessage<
	Block,
	HeaderHash,
	AuthorityId,
	Signature
>;

/// Justification of some hash.
pub type Justification = generic::Justification<HeaderHash, Signature>;

/// Justification of a prepare message.
pub type PrepareJustification = generic::PrepareJustification<HeaderHash, Signature>;

/// Result of a committed round of BFT
pub type Committed = generic::Committed<Block, HeaderHash, Signature>;

/// Communication between BFT participants.
pub type Communication = generic::Communication<Block, HeaderHash, AuthorityId, Signature>;

/// Context necessary for agreement.
pub trait Context {
	/// A future that resolves when a round timeout is concluded.
	type RoundTimeout: Future<Item=()>;
	/// A future that resolves when a proposal is ready.
	type CreateProposal: Future<Item=Block>;

	/// Get the local authority ID.
	fn local_id(&self) -> AuthorityId;

	/// Get the best proposal.
	fn proposal(&self) -> Self::CreateProposal;

	/// Get the digest of a candidate.
	fn candidate_digest(&self, candidate: &Block) -> HeaderHash;

	/// Sign a message using the local authority ID.
	fn sign_local(&self, message: Message) -> LocalizedMessage;

	/// Get the proposer for a given round of consensus.
	fn round_proposer(&self, round: usize) -> AuthorityId;

	/// Whether the candidate is valid.
	fn candidate_valid(&self, candidate: &Block) -> bool;

	/// Create a round timeout. The context will determine the correct timeout
	/// length, and create a future that will resolve when the timeout is
	/// concluded.
	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout;
}

impl<T: Context> generic::Context for T {
	type Candidate = Block;
	type Digest = HeaderHash;
	type AuthorityId = AuthorityId;
	type Signature = Signature;
	type RoundTimeout = <Self as Context>::RoundTimeout;
	type CreateProposal = <Self as Context>::CreateProposal;

	fn local_id(&self) -> AuthorityId { Context::local_id(self) }

	fn proposal(&self) -> Self::CreateProposal { Context::proposal(self) }

	fn candidate_digest(&self, candidate: &Block) -> HeaderHash {
		Context::candidate_digest(self, candidate)
	}

	fn sign_local(&self, message: Message) -> LocalizedMessage {
		Context::sign_local(self, message)
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		Context::round_proposer(self, round)
	}

	fn candidate_valid(&self, candidate: &Block) -> bool {
		Context::candidate_valid(self, candidate)
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		Context::begin_round_timeout(self, round)
	}
}

/// Attempt to reach BFT agreement on a candidate.
///
/// `nodes` is the number of nodes in the system.
/// `max_faulty` is the maximum number of faulty nodes. Should be less than
/// 1/3 of `nodes`, otherwise agreement may never be reached.
///
/// The input stream should never logically conclude. The logic here assumes
/// that messages flushed to the output stream will eventually reach other nodes.
///
/// Note that it is possible to witness agreement being reached without ever
/// seeing the candidate. Any candidates seen will be checked for validity.
///
/// Although technically the agreement will always complete (given the eventual
/// delivery of messages), in practice it is possible for this future to
/// conclude without having witnessed the conclusion.
/// In general, this future should be pre-empted by the import of a justification
/// set for this block height.
pub fn agree<C: Context, I, O, E>(context: C, nodes: usize, max_faulty: usize, input: I, output: O)
	-> generic::Agreement<C, I, O>
	where
		C: Context,
		C::RoundTimeout: Future<Error=E>,
		C::CreateProposal: Future<Error=E>,
		I: Stream<Item=Communication,Error=E>,
		O: Sink<SinkItem=Communication,SinkError=E>,
		E: From<InputStreamConcluded>,
{
	generic::agree(context, nodes, max_faulty, input, output)
}
