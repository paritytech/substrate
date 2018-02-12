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

extern crate substrate_codec as codec;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate ed25519;
extern crate tokio_timer;

#[cfg_attr(test, macro_use)]
extern crate futures;

use client::Client;
use codec::Slicable;
use ed25519::Signature;
use primitives::block::{Block, Header, HeaderHash};
use primitives::AuthorityId;

use futures::{Stream, Future};
use tokio_timer::Timer;

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

/// Errors that can occur during agreement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error {
	/// Io streams terminated.
	IoTerminated,
	/// Timer failed to fire.
	FaultyTimer,
	/// Unable to propose for some reason.
	CannotPropose,
}

impl From<InputStreamConcluded> for Error {
	fn from(_: InputStreamConcluded) -> Error {
		Error::IoTerminated
	}
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
pub trait Proposer: Sized {
    type CreateProposal: Future<Item=Block,Error=Error>;

    /// Initialize the proposal logic on top of a specific header.
    // TODO: provide state context explicitly?
    fn init(parent_header: &Header, sign_with: ed25519::Pair) -> Self;

    /// Create a proposal.
    fn propose(&self) -> Self::CreateProposal;
    /// Evaluate proposal. True means valid.
	// TODO: change this to a future.
    fn evaluate(&self, proposal: &Block) -> bool;
}

/// Instance of BFT agreement.
pub struct BftInstance<P> {
	key: ed25519::Pair, // TODO (now): key changing over time.
	authorities: Vec<AuthorityId>,
	parent_hash: HeaderHash,
	timer: Timer,
	round_timeout_multiplier: u64,
	proposer: P,
}

impl<P: Proposer> generic::Context for BftInstance<P> {
	type AuthorityId = AuthorityId;
	type Digest = HeaderHash;
	type Signature = Signature;
	type Candidate = Block;
	type RoundTimeout = Box<Future<Item=(),Error=Error>>;
	type CreateProposal = P::CreateProposal;

	fn local_id(&self) -> AuthorityId {
		self.key.public().0
	}

	fn proposal(&self) -> P::CreateProposal {
		self.proposer.propose()
	}

	fn candidate_digest(&self, proposal: &Block) -> HeaderHash {
		proposal.header.hash()
	}

	fn sign_local(&self, message: Message) -> LocalizedMessage {
		use primitives::bft::{Message as PrimitiveMessage, Action as PrimitiveAction};

		let action = match message.clone() {
			::generic::Message::Propose(r, p) => PrimitiveAction::Propose(r as u32, p),
			::generic::Message::Prepare(r, h) => PrimitiveAction::Prepare(r as u32, h),
			::generic::Message::Commit(r, h) => PrimitiveAction::Commit(r as u32, h),
			::generic::Message::AdvanceRound(r) => PrimitiveAction::AdvanceRound(r as u32),
		};

		let primitive = PrimitiveMessage {
			parent: self.parent_hash,
			action,
		};

		let to_sign = Slicable::encode(&primitive);
		let signature = self.key.sign(&to_sign);

		LocalizedMessage {
			message,
			signature,
			sender: self.key.public().0
		}
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		use primitives::hashing::blake2_256;

		// repeat blake2_256 on parent hash round + 1 times.
		// use as index into authorities vec.
		// TODO: parent hash is really insecure as a randomness beacon as
		// the prior can easily influence the block hash.
		let hashed = (0..round + 1).fold(self.parent_hash.0, |a, _| {
			blake2_256(&a[..])
		});

		let index = u32::decode(&mut &hashed[..])
			.expect("there are more than 4 bytes in a 32 byte hash; qed");

		self.authorities[(index as usize) % self.authorities.len()]
	}

	fn candidate_valid(&self, proposal: &Block) -> bool {
		self.proposer.evaluate(proposal)
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		use std::time::Duration;

		let round = ::std::cmp::min(63, round) as u32;
		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		Box::new(self.timer.sleep(Duration::from_secs(timeout))
			.map_err(|_| Error::FaultyTimer))
	}
}
