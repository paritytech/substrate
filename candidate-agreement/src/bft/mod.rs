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

use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

use futures::{future, Future, Stream, Sink, Poll, Async, AsyncSink};

use self::accumulator::State;

pub use self::accumulator::{Accumulator, Justification, PrepareJustification};

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

/// Context necessary for agreement.
pub trait Context {
	/// Candidate proposed.
	type Candidate: Eq + Clone;
	/// Candidate digest.
	type Digest: Hash + Eq + Clone;
	/// Validator ID.
	type ValidatorId: Hash + Eq + Clone;
	/// Signature.
	type Signature: Eq + Clone;
	/// A future that resolves when a round timeout is concluded.
	type RoundTimeout: Future<Item=()>;
	/// A future that resolves when a proposal is ready.
	type Proposal: Future<Item=Self::Candidate>;

	/// Get the local validator ID.
	fn local_id(&self) -> Self::ValidatorId;

	/// Get the best proposal.
	fn proposal(&self) -> Self::Proposal;

	/// Get the digest of a candidate.
	fn candidate_digest(&self, candidate: &Self::Candidate) -> Self::Digest;

	/// Sign a message using the local validator ID.
	fn sign_local(&self, message: Message<Self::Candidate, Self::Digest>)
		-> LocalizedMessage<Self::Candidate, Self::Digest, Self::ValidatorId, Self::Signature>;

	/// Get the proposer for a given round of consensus.
	fn round_proposer(&self, round: usize) -> Self::ValidatorId;

	/// Whether the candidate is valid.
	fn candidate_valid(&self, candidate: &Self::Candidate) -> bool;

	/// Create a round timeout. The context will determine the correct timeout
	/// length, and create a future that will resolve when the timeout is
	/// concluded.
	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout;
}

/// Communication that can occur between participants in consensus.
#[derive(Debug, Clone)]
pub enum Communication<C, D, V, S> {
	/// A consensus message (proposal or vote)
	Message(LocalizedMessage<C, D, V, S>),
	/// A proof-of-lock.
	Locked(PrepareJustification<D, S>),
}

/// Type alias for a localized message using only type parameters from `Context`.
// TODO: actual type alias when it's no longer a warning.
pub struct ContextCommunication<C: Context + ?Sized>(pub Communication<C::Candidate, C::Digest, C::ValidatorId, C::Signature>);

impl<C: Context + ?Sized> Clone for ContextCommunication<C>
	where
		LocalizedMessage<C::Candidate, C::Digest, C::ValidatorId, C::Signature>: Clone,
		PrepareJustification<C::Digest, C::Signature>: Clone,
{
	fn clone(&self) -> Self {
		ContextCommunication(self.0.clone())
	}
}

#[derive(Debug)]
struct Sending<T> {
	items: VecDeque<T>,
	flushing: bool,
}

impl<T> Sending<T> {
	fn with_capacity(n: usize) -> Self {
		Sending {
			items: VecDeque::with_capacity(n),
			flushing: false,
		}
	}

	fn push(&mut self, item: T) {
		self.items.push_back(item);
		self.flushing = false;
	}

	// process all the sends into the sink.
	fn process_all<S: Sink<SinkItem=T>>(&mut self, sink: &mut S) -> Poll<(), S::SinkError> {
		while let Some(item) = self.items.pop_front() {
			match sink.start_send(item) {
				Err(e) => return Err(e),
				Ok(AsyncSink::NotReady(item)) => {
					self.items.push_front(item);
					return Ok(Async::NotReady);
				}
				Ok(AsyncSink::Ready) => { self.flushing = true; }
			}
		}

		while self.flushing {
			match sink.poll_complete() {
				Err(e) => return Err(e),
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(())) => { self.flushing = false; }
			}
		}

		Ok(Async::Ready(()))
	}
}

/// Error returned when the input stream concludes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InputStreamConcluded;

impl ::std::fmt::Display for InputStreamConcluded {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", ::std::error::Error::description(self))
	}
}

impl ::std::error::Error for InputStreamConcluded {
	fn description(&self) -> &str {
		"input stream of messages concluded prematurely"
	}
}

// get the "full BFT" threshold based on an amount of nodes and
// a maximum faulty. if nodes == 3f + 1, then threshold == 2f + 1.
fn bft_threshold(nodes: usize, max_faulty: usize) -> usize {
	nodes - max_faulty
}

/// Committed successfully.
pub struct Committed<C, D, S> {
	/// The candidate committed for. This will be unknown if
	/// we never witnessed the proposal of the last round.
	pub candidate: Option<C>,
	/// A justification for the candidate.
	pub justification: Justification<D, S>,
}

struct Locked<D, S> {
	justification: PrepareJustification<D, S>,
}

impl<D, S> Locked<D, S> {
	fn digest(&self) -> &D {
		&self.justification.digest
	}
}

// the state of the local node during the current state of consensus.
//
// behavior is different when locked on a proposal.
#[derive(Clone, Copy)]
enum LocalState {
	Start,
	Proposed,
	Prepared,
	Committed,
	VoteAdvance,
}

// This structure manages a single "view" of consensus.
//
// We maintain two message accumulators: one for the round we are currently in,
// and one for a future round.
//
// We also store notable candidates: any proposed or prepared for, as well as any
// with witnessed threshold-prepares.
// This ensures that threshold-prepares witnessed by even one honest participant
// will still have the candidate available for proposal.
//
// We advance the round accumulators when one of two conditions is met:
//   - we witness consensus of advancement in the current round. in this case we
//     advance by one.
//   - a higher threshold-prepare is broadcast to us. in this case we can
//     advance to the round of the threshold-prepare. this is an indication
//     that we have experienced severe asynchrony/clock drift with the remainder
//     of the other validators, and it is unlikely that we can assist in
//     consensus meaningfully. nevertheless we make an attempt.
struct Strategy<C: Context> {
	nodes: usize,
	max_faulty: usize,
	fetching_proposal: Option<C::Proposal>,
	round_timeout: future::Fuse<C::RoundTimeout>,
	local_state: LocalState,
	locked: Option<Locked<C::Digest, C::Signature>>,
	notable_candidates: HashMap<C::Digest, C::Candidate>,
	current_accumulator: Accumulator<C::Candidate, C::Digest, C::ValidatorId, C::Signature>,
	future_accumulator: Accumulator<C::Candidate, C::Digest, C::ValidatorId, C::Signature>,
	local_id: C::ValidatorId,
}

impl<C: Context> Strategy<C> {
	fn create(context: &C, nodes: usize, max_faulty: usize) -> Self {
		let timeout = context.begin_round_timeout(0);
		let threshold = bft_threshold(nodes, max_faulty);

		let current_accumulator = Accumulator::new(
			0,
			threshold,
			context.round_proposer(0),
		);

		let future_accumulator = Accumulator::new(
			1,
			threshold,
			context.round_proposer(1),
		);

		Strategy {
			nodes,
			max_faulty,
			current_accumulator,
			future_accumulator,
			fetching_proposal: None,
			local_state: LocalState::Start,
			locked: None,
			notable_candidates: HashMap::new(),
			round_timeout: timeout.fuse(),
			local_id: context.local_id(),
		}
	}

	fn import_message(
		&mut self,
		msg: LocalizedMessage<C::Candidate, C::Digest, C::ValidatorId, C::Signature>
	) {
		let round_number = msg.message.round_number();

		if round_number == self.current_accumulator.round_number() {
			self.current_accumulator.import_message(msg);
		} else if round_number == self.future_accumulator.round_number() {
			self.future_accumulator.import_message(msg);
		}
	}

	fn import_lock_proof(
		&mut self,
		context: &C,
		justification: PrepareJustification<C::Digest, C::Signature>,
	) {
		// TODO: find a way to avoid processing of the signatures if the sender is
		// not the primary or the round number is low.
		let current_round_number = self.current_accumulator.round_number();
		if justification.round_number < current_round_number {
			return
		} else if justification.round_number == current_round_number {
			self.locked = Some(Locked { justification });
		} else {
			// jump ahead to the prior round as this is an indication of a supermajority
			// good nodes being at least on that round.
			self.advance_to_round(context, justification.round_number);
			self.locked = Some(Locked { justification });
		}
	}

	// poll the strategy: this will queue messages to be sent and advance
	// rounds if necessary.
	//
	// only call within the context of a `Task`.
	fn poll<E>(&mut self, context: &C, sending: &mut Sending<ContextCommunication<C>>)
		-> Poll<Committed<C::Candidate, C::Digest, C::Signature>, E>
		where
			C::RoundTimeout: Future<Error=E>,
			C::Proposal: Future<Error=E>,
	{
		self.propose(context, sending)?;
		self.prepare(context, sending);
		self.commit(context, sending);
		self.vote_advance(context, sending)?;

		let advance = match self.current_accumulator.state() {
			&State::Advanced(ref p_just) => {
				// lock to any witnessed prepare justification.
				if let Some(p_just) = p_just.as_ref() {
					self.locked = Some(Locked { justification: p_just.clone() });
				}

				let round_number = self.current_accumulator.round_number();
				Some(round_number + 1)
			}
			&State::Committed(ref just) => {
				// fetch the agreed-upon candidate:
				//   - we may not have received the proposal in the first place
				//   - there is no guarantee that the proposal we got was agreed upon
				//     (can happen if faulty primary)
				//   - look in the candidates of prior rounds just in case.
				let candidate = self.current_accumulator
					.proposal()
					.and_then(|c| if context.candidate_digest(c) == just.digest {
						Some(c.clone())
					} else {
						None
					})
					.or_else(|| self.notable_candidates.get(&just.digest).cloned());

				let committed = Committed {
					candidate,
					justification: just.clone()
				};

				return Ok(Async::Ready(committed))
			}
			_ => None,
		};

		if let Some(new_round) = advance {
			self.advance_to_round(context, new_round);
		}

		Ok(Async::NotReady)
	}

	fn propose(&mut self, context: &C, sending: &mut Sending<ContextCommunication<C>>)
		-> Result<(), <C::Proposal as Future>::Error>
	{
		if let LocalState::Start = self.local_state {
			let mut propose = false;
			if let &State::Begin = self.current_accumulator.state() {
				let round_number = self.current_accumulator.round_number();
				let primary = context.round_proposer(round_number);
				propose = self.local_id == primary;
			};

			if !propose { return Ok(()) }

			// obtain the proposal to broadcast.
			let proposal = match self.locked {
				Some(ref locked) => {
					// TODO: it's possible but very unlikely that we don't have the
					// corresponding proposal for what we are locked to.
					//
					// since this is an edge case on an edge case, it is fine
					// to eat the round timeout for now, but it can be optimized by
					// broadcasting an advance vote.
					self.notable_candidates.get(locked.digest()).cloned()
				}
				None => {
					let res = self.fetching_proposal
						.get_or_insert_with(|| context.proposal())
						.poll()?;

					match res {
						Async::Ready(p) => Some(p),
						Async::NotReady => None,
					}
				}
			};

			if let Some(proposal) = proposal {
				self.fetching_proposal = None;

				let message = Message::Propose(
					self.current_accumulator.round_number(),
					proposal
				);

				self.import_and_send_message(message, context, sending);

				// broadcast the justification along with the proposal if we are locked.
				if let Some(ref locked) = self.locked {
					sending.push(
						ContextCommunication(Communication::Locked(locked.justification.clone()))
					);
				}

				self.local_state = LocalState::Proposed;
			}
		}

		Ok(())
	}

	fn prepare(&mut self, context: &C, sending: &mut Sending<ContextCommunication<C>>) {
		// prepare only upon start or having proposed.
		match self.local_state {
			LocalState::Start | LocalState::Proposed => {},
			_ => return
		};

		let mut prepare_for = None;

		// we can't prepare until something was proposed.
		if let &State::Proposed(ref candidate) = self.current_accumulator.state() {
			let digest = context.candidate_digest(candidate);

			// vote to prepare only if we believe the candidate to be valid and
			// we are not locked on some other candidate.
			match self.locked {
				Some(ref locked) if locked.digest() != &digest => {}
				Some(_) | None => {
					if context.candidate_valid(candidate) {
						prepare_for = Some(digest);
					}
				}
			}
		}

		if let Some(digest) = prepare_for {
			let message = Message::Prepare(
				self.current_accumulator.round_number(),
				digest
			);

			self.import_and_send_message(message, context, sending);
			self.local_state = LocalState::Prepared;
		}
	}

	fn commit(&mut self, context: &C, sending: &mut Sending<ContextCommunication<C>>) {
		// commit only if we haven't voted to advance or committed already
		match self.local_state {
			LocalState::Committed | LocalState::VoteAdvance => return,
			_ => {}
		}

		let mut commit_for = None;

		if let &State::Prepared(ref p_just) = self.current_accumulator.state() {
			// we are now locked to this prepare justification.
			let digest = p_just.digest.clone();
			self.locked = Some(Locked { justification: p_just.clone() });
			commit_for = Some(digest);
		}

		if let Some(digest) = commit_for {
			let message = Message::Commit(
				self.current_accumulator.round_number(),
				digest
			);

			self.import_and_send_message(message, context, sending);
			self.local_state = LocalState::Committed;
		}
	}

	fn vote_advance(&mut self, context: &C, sending: &mut Sending<ContextCommunication<C>>)
		-> Result<(), <C::RoundTimeout as Future>::Error>
	{
		// we can vote for advancement under all circumstances unless we have already.
		if let LocalState::VoteAdvance = self.local_state { return Ok(()) }

		// if we got f + 1 advance votes, or the timeout has fired, and we haven't
		// sent an AdvanceRound message yet, do so.
		let mut attempt_advance = self.current_accumulator.advance_votes() > self.max_faulty;

		if let Async::Ready(_) = self.round_timeout.poll()? {
			attempt_advance = true;
		}

		// the other situation we attempt to advance is if there is a proposal
		// that is not equal to the one we are locked to.
		match (self.local_state, self.current_accumulator.state(), &self.locked) {
			(LocalState::Start, &State::Proposed(ref candidate), &Some(ref locked)) => {
				let candidate_digest = context.candidate_digest(candidate);
				if &candidate_digest != locked.digest() {
					attempt_advance = true;
				}
			}
			_ => {}
		}

		if attempt_advance {
			let message = Message::AdvanceRound(
				self.current_accumulator.round_number(),
			);

			self.import_and_send_message(message, context, sending);
			self.local_state = LocalState::VoteAdvance;
		}

		Ok(())
	}

	fn advance_to_round(&mut self, context: &C, round: usize) {
		assert!(round > self.current_accumulator.round_number());

		let threshold = self.nodes - self.max_faulty;

		self.fetching_proposal = None;
		self.round_timeout = context.begin_round_timeout(round).fuse();
		self.local_state = LocalState::Start;

		let new_future = Accumulator::new(
			round + 1,
			threshold,
			context.round_proposer(round + 1),
		);

		// when advancing from a round, store away the witnessed proposal.
		//
		// if we or other participants end up locked on that candidate,
		// we will have it.
		if let Some(proposal) = self.current_accumulator.proposal() {
			let digest = context.candidate_digest(proposal);
			self.notable_candidates.entry(digest).or_insert_with(|| proposal.clone());
		}

		// special case when advancing by a single round.
		if self.future_accumulator.round_number() == round {
			self.current_accumulator
				= ::std::mem::replace(&mut self.future_accumulator, new_future);
		} else {
			self.future_accumulator = new_future;
			self.current_accumulator = Accumulator::new(
				round,
				threshold,
				context.round_proposer(round),
			);
		}
	}

	fn import_and_send_message(
		&mut self,
		message: Message<C::Candidate, C::Digest>,
		context: &C,
		sending: &mut Sending<ContextCommunication<C>>
	) {
		let signed_message = context.sign_local(message);
		self.import_message(signed_message.clone());
		sending.push(ContextCommunication(Communication::Message(signed_message)));
	}
}

/// Future that resolves upon BFT agreement for a candidate.
#[must_use = "futures do nothing unless polled"]
pub struct Agreement<C: Context, I, O> {
	context: C,
	input: I,
	output: O,
	concluded: Option<Committed<C::Candidate, C::Digest, C::Signature>>,
	sending: Sending<ContextCommunication<C>>,
	strategy: Strategy<C>,
}

impl<C, I, O, E> Future for Agreement<C, I, O>
	where
		C: Context,
		C::RoundTimeout: Future<Error=E>,
		C::Proposal: Future<Error=E>,
		I: Stream<Item=ContextCommunication<C>,Error=E>,
		O: Sink<SinkItem=ContextCommunication<C>,SinkError=E>,
		E: From<InputStreamConcluded>,
{
	type Item = Committed<C::Candidate, C::Digest, C::Signature>;
	type Error = E;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// even if we've observed the conclusion, wait until all
		// pending outgoing messages are flushed.
		if let Some(just) = self.concluded.take() {
			return Ok(match self.sending.process_all(&mut self.output)? {
				Async::Ready(()) => Async::Ready(just),
				Async::NotReady => {
					self.concluded = Some(just);
					Async::NotReady
				}
			})
		}

		// make progress on flushing all pending messages.
		let _ = self.sending.process_all(&mut self.output)?;

		// try to process timeouts.
		if let Async::Ready(just) = self.strategy.poll(&self.context, &mut self.sending)? {
			self.concluded = Some(just);
			return self.poll();
		}

		let message = try_ready!(self.input.poll()).ok_or(InputStreamConcluded)?;

		match message.0 {
			Communication::Message(message) => self.strategy.import_message(message),
			Communication::Locked(proof) => self.strategy.import_lock_proof(&self.context, proof),
		}

		self.poll()
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
pub fn agree<C: Context, I, O>(context: C, nodes: usize, max_faulty: usize, input: I, output: O)
	-> Agreement<C, I, O>
{
	let strategy = Strategy::create(&context, nodes, max_faulty);
	Agreement {
		context,
		input,
		output,
		concluded: None,
		sending: Sending::with_capacity(4),
		strategy: strategy,
	}
}
