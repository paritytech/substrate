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

//! BFT Agreement based on a rotating proposer in different rounds.

mod accumulator;

/// Messages over the proposal.
/// Each message carries an associated round number.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message<P, D> {
	/// Send a full proposal.
	Propose(usize, P),
	/// Prepare to vote for proposal with digest D.
	Prepare(usize, D),
	/// Commit to proposal with digest D..
	Commit(usize, D),
	/// Propose advancement to a new round.
	AdvanceRound(usize),
}

impl<P, D> Message<P, D> {
	fn round_number(&self) -> usize {
		match *self {
			Message::Propose(round, _) => round,
			Message::Prepare(round, _) => round,
			Message::Commit(round, _) => round,
			Message::AdvanceRound(round) => round,
		}
	}
}

/// A localized message, including the sender.
#[derive(Debug, Clone)]
pub struct LocalizedMessage<T, P, V, S> {
	/// The message received.
	pub message: Message<T, P>,
	/// The sender of the message
	pub sender: V,
	/// The signature of the message.
	pub signature: S,
}

/// The agreed-upon data.
#[derive(Debug, Clone)]
pub struct Agreed<T, P, V, S> {
	/// The agreed-upon proposal.
	pub proposal: P,
	/// The justification for the proposal.
	pub justification: Vec<LocalizedMessage<T, P, V, S>>,
}

/// Parameters to agreement.
pub struct Params<
	Validator,
	SignLocal,
	Timeout,
	CanInclude,
	MessagesIn,
	MessagesOut,
> {
	/// The ID of the current view's primary.
	pub primary: Validator,
	/// The local ID.
	pub local_id: Validator,
	/// A closure for signing local messages.
	pub sign_local: SignLocal,
	/// A timeout that fires when the view change should begin.
	pub begin_view_change: Timeout,
	/// A function for checking if a proposal can be voted for.
	pub can_include: CanInclude,
	/// The input stream. Should never conclude, and should yield only messages
	/// sent by validators and which have been authenticated properly.
	pub input: MessagesIn,
	/// The output message sink. This assumes that messages will eventually
	/// be delivered to all honest participants, either by repropagation, gossip,
	/// or some reliable broadcast mechanism.
	pub output: MessagesOut,
	/// The maximum number of faulty nodes.
	pub max_faulty: usize,
}
