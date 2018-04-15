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
//! Very general implementation.

use std::collections::{HashMap, VecDeque};
use std::collections::hash_map;
use std::fmt::Debug;
use std::hash::Hash;

use futures::{future, Future, Stream, Sink, Poll, Async, AsyncSink};

use self::accumulator::State;

pub use self::accumulator::{Accumulator, Justification, PrepareJustification, UncheckedJustification, Misbehavior};

mod accumulator;

#[cfg(test)]
mod tests;

/// Votes during a round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Vote<D> {
	/// Prepare to vote for proposal with digest D.
	Prepare(usize, D),
	/// Commit to proposal with digest D..
	Commit(usize, D),
	/// Propose advancement to a new round.
	AdvanceRound(usize),
}

impl<D> Vote<D> {
	/// Extract the round number.
	pub fn round_number(&self) -> usize {
		match *self {
			Vote::Prepare(round, _) => round,
			Vote::Commit(round, _) => round,
			Vote::AdvanceRound(round) => round,
		}
	}
}

/// Messages over the proposal.
/// Each message carries an associated round number.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message<C, D> {
	/// A proposal itself.
	Propose(usize, C),
	/// A vote of some kind, localized to a round number.
	Vote(Vote<D>),
}

impl<C, D> From<Vote<D>> for Message<C, D> {
	fn from(vote: Vote<D>) -> Self {
		Message::Vote(vote)
	}
}

/// A localized proposal message. Contains two signed pieces of data.
#[derive(Debug, Clone)]
pub struct LocalizedProposal<C, D, V, S> {
	/// The round number.
	pub round_number: usize,
	/// The proposal sent.
	pub proposal: C,
	/// The digest of the proposal.
	pub digest: D,
	/// The sender of the proposal
	pub sender: V,
	/// The signature on the message (propose, round number, digest)
	pub digest_signature: S,
	/// The signature on the message (propose, round number, proposal)
	pub full_signature: S,
}

/// A localized vote message, including the sender.
#[derive(Debug, Clone)]
pub struct LocalizedVote<D, V, S> {
	/// The message sent.
	pub vote: Vote<D>,
	/// The sender of the message
	pub sender: V,
	/// The signature of the message.
	pub signature: S,
}

/// A localized message.
#[derive(Debug, Clone)]
pub enum LocalizedMessage<C, D, V, S> {
	/// A proposal.
	Propose(LocalizedProposal<C, D, V, S>),
	/// A vote.
	Vote(LocalizedVote<D, V, S>),
}

impl<C, D, V, S> LocalizedMessage<C, D, V, S> {
	/// Extract the sender.
	pub fn sender(&self) -> &V {
		match *self {
			LocalizedMessage::Propose(ref proposal) => &proposal.sender,
			LocalizedMessage::Vote(ref vote) => &vote.sender,
		}
	}

	/// Extract the round number.
	pub fn round_number(&self) -> usize {
		match *self {
			LocalizedMessage::Propose(ref proposal) => proposal.round_number,
			LocalizedMessage::Vote(ref vote) => vote.vote.round_number(),
		}
	}
}

impl<C, D, V, S> From<LocalizedVote<D, V, S>> for LocalizedMessage<C, D, V, S> {
	fn from(vote: LocalizedVote<D, V, S>) -> Self {
		LocalizedMessage::Vote(vote)
	}
}

/// Context necessary for agreement.
///
/// Provides necessary types for protocol messages, and functions necessary for a
/// participant to evaluate and create those messages.
pub trait Context {
	/// Errors which can occur from the futures in this context.
	type Error: From<InputStreamConcluded>;
	/// Candidate proposed.
	type Candidate: Debug + Eq + Clone;
	/// Candidate digest.
	type Digest: Debug + Hash + Eq + Clone;
	/// Authority ID.
	type AuthorityId: Debug + Hash + Eq + Clone;
	/// Signature.
	type Signature: Debug + Eq + Clone;
	/// A future that resolves when a round timeout is concluded.
	type RoundTimeout: Future<Item=(), Error=Self::Error>;
	/// A future that resolves when a proposal is ready.
	type CreateProposal: Future<Item=Self::Candidate, Error=Self::Error>;
	/// A future that resolves when a proposal has been evaluated.
	type EvaluateProposal: Future<Item=bool, Error=Self::Error>;

	/// Get the local authority ID.
	fn local_id(&self) -> Self::AuthorityId;

	/// Get the best proposal.
	fn proposal(&self) -> Self::CreateProposal;

	/// Get the digest of a candidate.
	fn candidate_digest(&self, candidate: &Self::Candidate) -> Self::Digest;

	/// Sign a message using the local authority ID.
	/// In the case of a proposal message, it should sign on the hash and
	/// the bytes of the proposal.
	fn sign_local(&self, message: Message<Self::Candidate, Self::Digest>)
		-> LocalizedMessage<Self::Candidate, Self::Digest, Self::AuthorityId, Self::Signature>;

	/// Get the proposer for a given round of consensus.
	fn round_proposer(&self, round: usize) -> Self::AuthorityId;

	/// Whether the proposal is valid.
	fn proposal_valid(&self, proposal: &Self::Candidate) -> Self::EvaluateProposal;

	/// Create a round timeout. The context will determine the correct timeout
	/// length, and create a future that will resolve when the timeout is
	/// concluded.
	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout;
}

/// Communication that can occur between participants in consensus.
#[derive(Debug, Clone)]
pub enum Communication<C, D, V, S> {
	/// A consensus message (proposal or vote)
	Consensus(LocalizedMessage<C, D, V, S>),
	/// Auxiliary communication (just proof-of-lock for now).
	Auxiliary(PrepareJustification<D, S>),
}

/// Hack to get around type alias warning.
pub trait TypeResolve {
	/// Communication type.
	type Communication;
}

impl<C: Context> TypeResolve for C {
	type Communication = Communication<C::Candidate, C::Digest, C::AuthorityId, C::Signature>;
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

		if self.flushing {
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalState {
	Start,
	Proposed,
	Prepared(bool), // whether we thought it valid.
	Committed,
	VoteAdvance,
}

// This structure manages a single "view" of consensus.
//
// We maintain two message accumulators: one for the round we are currently in,
// and one for a future round.
//
// We advance the round accumulators when one of two conditions is met:
//   - we witness consensus of advancement in the current round. in this case we
//     advance by one.
//   - a higher threshold-prepare is broadcast to us. in this case we can
//     advance to the round of the threshold-prepare. this is an indication
//     that we have experienced severe asynchrony/clock drift with the remainder
//     of the other authorities, and it is unlikely that we can assist in
//     consensus meaningfully. nevertheless we make an attempt.
struct Strategy<C: Context> {
	nodes: usize,
	max_faulty: usize,
	fetching_proposal: Option<C::CreateProposal>,
	evaluating_proposal: Option<C::EvaluateProposal>,
	round_timeout: future::Fuse<C::RoundTimeout>,
	local_state: LocalState,
	locked: Option<Locked<C::Digest, C::Signature>>,
	notable_candidates: HashMap<C::Digest, C::Candidate>,
	current_accumulator: Accumulator<C::Candidate, C::Digest, C::AuthorityId, C::Signature>,
	future_accumulator: Accumulator<C::Candidate, C::Digest, C::AuthorityId, C::Signature>,
	local_id: C::AuthorityId,
	misbehavior: HashMap<C::AuthorityId, Misbehavior<C::Digest, C::Signature>>,
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
			evaluating_proposal: None,
			local_state: LocalState::Start,
			locked: None,
			notable_candidates: HashMap::new(),
			round_timeout: timeout.fuse(),
			local_id: context.local_id(),
			misbehavior: HashMap::new(),
		}
	}

	fn import_message(
		&mut self,
		msg: LocalizedMessage<C::Candidate, C::Digest, C::AuthorityId, C::Signature>
	) {
		let round_number = msg.round_number();

		let sender = msg.sender().clone();
		let misbehavior = if round_number == self.current_accumulator.round_number() {
			self.current_accumulator.import_message(msg)
		} else if round_number == self.future_accumulator.round_number() {
			self.future_accumulator.import_message(msg)
		} else {
			Ok(())
		};

		if let Err(misbehavior) = misbehavior {
			self.misbehavior.insert(sender, misbehavior);
		}
	}

	fn import_lock_proof(
		&mut self,
		context: &C,
		justification: PrepareJustification<C::Digest, C::Signature>,
	) {
		// TODO: find a way to avoid processing of the signatures if the sender is
		// not the primary or the round number is low.
		if justification.round_number > self.current_accumulator.round_number() {
			// jump ahead to the prior round as this is an indication of a supermajority
			// good nodes being at least on that round.
			self.advance_to_round(context, justification.round_number);
		}

		let lock_to_new = self.locked.as_ref()
			.map_or(true, |l| l.justification.round_number < justification.round_number);

		if lock_to_new {
			self.locked = Some(Locked { justification })
		}
	}

	// poll the strategy: this will queue messages to be sent and advance
	// rounds if necessary.
	//
	// only call within the context of a `Task`.
	fn poll(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	)
		-> Poll<Committed<C::Candidate, C::Digest, C::Signature>, C::Error>
	{
		let mut last_watermark = (
			self.current_accumulator.round_number(),
			self.local_state
		);

		// poll until either completion or state doesn't change.
		loop {
			match self.poll_once(context, sending)? {
				Async::Ready(x) => return Ok(Async::Ready(x)),
				Async::NotReady => {
					let new_watermark = (
						self.current_accumulator.round_number(),
						self.local_state
					);

					if new_watermark == last_watermark {
						return Ok(Async::NotReady)
					} else {
						last_watermark = new_watermark;
					}
				}
			}
		}
	}

	// perform one round of polling: attempt to broadcast messages and change the state.
	// if the round or internal round-state changes, this should be called again.
	fn poll_once(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	)
		-> Poll<Committed<C::Candidate, C::Digest, C::Signature>, C::Error>
	{
		self.propose(context, sending)?;
		self.prepare(context, sending)?;
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

	fn propose(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	)
		-> Result<(), C::Error>
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
						Communication::Auxiliary(locked.justification.clone())
					);
				}

				self.local_state = LocalState::Proposed;
			}
		}

		Ok(())
	}

	fn prepare(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	)
		-> Result<(), C::Error>
	{
		// prepare only upon start or having proposed.
		match self.local_state {
			LocalState::Start | LocalState::Proposed => {},
			_ => return Ok(())
		};

		let mut prepare_for = None;

		// we can't prepare until something was proposed.
		if let &State::Proposed(ref candidate) = self.current_accumulator.state() {
			let digest = context.candidate_digest(candidate);

			// vote to prepare only if we believe the candidate to be valid and
			// we are not locked on some other candidate.
			match self.locked {
				Some(ref locked) if locked.digest() != &digest => {}
				Some(_) => {
					// don't check validity if we are locked.
					// this is necessary to preserve the liveness property.
					self.local_state = LocalState::Prepared(true);
					prepare_for = Some(digest);
				}
				None => {
					let res = self.evaluating_proposal
						.get_or_insert_with(|| context.proposal_valid(candidate))
						.poll()?;

					if let Async::Ready(valid) = res {
						self.evaluating_proposal = None;
						self.local_state = LocalState::Prepared(valid);

						if valid {
							prepare_for = Some(digest);
						}
					}
				}
			}
		}

		if let Some(digest) = prepare_for {
			let message = Vote::Prepare(
				self.current_accumulator.round_number(),
				digest
			).into();

			self.import_and_send_message(message, context, sending);
		}

		Ok(())
	}

	fn commit(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	) {
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
			let message = Vote::Commit(
				self.current_accumulator.round_number(),
				digest
			).into();

			self.import_and_send_message(message, context, sending);
			self.local_state = LocalState::Committed;
		}
	}

	fn vote_advance(
		&mut self,
		context: &C,
		sending: &mut Sending<<C as TypeResolve>::Communication>
	)
		-> Result<(), C::Error>
	{
		// we can vote for advancement under all circumstances unless we have already.
		if let LocalState::VoteAdvance = self.local_state { return Ok(()) }

		// if we got f + 1 advance votes, or the timeout has fired, and we haven't
		// sent an AdvanceRound message yet, do so.
		let mut attempt_advance = self.current_accumulator.advance_votes() > self.max_faulty;

		// if we evaluated the proposal and it was bad, vote to advance round.
		if let LocalState::Prepared(false) = self.local_state {
			attempt_advance = true;
		}

		// if the timeout has fired, vote to advance round.
		if let Async::Ready(_) = self.round_timeout.poll()? {
			attempt_advance = true;
		}

		if attempt_advance {
			let message = Vote::AdvanceRound(
				self.current_accumulator.round_number(),
			).into();

			self.import_and_send_message(message, context, sending);
			self.local_state = LocalState::VoteAdvance;
		}

		Ok(())
	}

	fn advance_to_round(&mut self, context: &C, round: usize) {
		assert!(round > self.current_accumulator.round_number());

		let threshold = self.nodes - self.max_faulty;

		self.fetching_proposal = None;
		self.evaluating_proposal = None;
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
		sending: &mut Sending<<C as TypeResolve>::Communication>
	) {
		let signed_message = context.sign_local(message);
		self.import_message(signed_message.clone());
		sending.push(Communication::Consensus(signed_message));
	}
}

/// Future that resolves upon BFT agreement for a candidate.
#[must_use = "futures do nothing unless polled"]
pub struct Agreement<C: Context, I, O> {
	context: C,
	input: I,
	output: O,
	concluded: Option<Committed<C::Candidate, C::Digest, C::Signature>>,
	sending: Sending<<C as TypeResolve>::Communication>,
	strategy: Strategy<C>,
}

impl<C, I, O> Future for Agreement<C, I, O>
	where
		C: Context,
		I: Stream<Item=<C as TypeResolve>::Communication,Error=C::Error>,
		O: Sink<SinkItem=<C as TypeResolve>::Communication,SinkError=C::Error>,
{
	type Item = Committed<C::Candidate, C::Digest, C::Signature>;
	type Error = C::Error;

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

		loop {
			let message = match self.input.poll()? {
				Async::Ready(msg) => msg.ok_or(InputStreamConcluded)?,
				Async::NotReady => break,
			};

			match message {
				Communication::Consensus(message) => self.strategy.import_message(message),
				Communication::Auxiliary(lock_proof)
					=> self.strategy.import_lock_proof(&self.context, lock_proof),
			}
		}

		// try to process timeouts.
		let state_machine_res = self.strategy.poll(&self.context, &mut self.sending)?;

		// make progress on flushing all pending messages.
		let _ = self.sending.process_all(&mut self.output)?;

		match state_machine_res {
			Async::Ready(just) => {
				self.concluded = Some(just);
				self.poll()
			}
			Async::NotReady => {

				Ok(Async::NotReady)
			}
		}
	}
}

impl<C: Context, I, O> Agreement<C, I, O> {
	/// Get a reference to the underlying context.
	pub fn context(&self) -> &C {
		&self.context
	}

	/// Drain the misbehavior vector.
	pub fn drain_misbehavior(&mut self) -> hash_map::Drain<C::AuthorityId, Misbehavior<C::Digest, C::Signature>> {
		self.strategy.misbehavior.drain()
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
	where
		C: Context,
		I: Stream<Item=<C as TypeResolve>::Communication,Error=C::Error>,
		O: Sink<SinkItem=<C as TypeResolve>::Communication,SinkError=C::Error>,
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
