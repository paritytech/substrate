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

//! Propagation and agreement of candidates.
//!
//! Authorities are split into groups by parachain, and each authority might come
//! up its own candidate for their parachain. Within groups, authorities pass around
//! their candidates and produce statements of validity.
//!
//! Any candidate that receives majority approval by the authorities in a group
//! may be subject to inclusion, unless any authorities flag that candidate as invalid.
//!
//! Wrongly flagging as invalid should be strongly disincentivized, so that in the
//! equilibrium state it is not expected to happen. Likewise with the submission
//! of invalid blocks.
//!
//! Groups themselves may be compromised by malicious authorities.

#[macro_use]
extern crate futures;
extern crate parking_lot;
extern crate tokio_timer;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;
use std::time::Duration;

use futures::prelude::*;
use futures::sync::{mpsc, oneshot};
use parking_lot::Mutex;
use tokio_timer::Timer;

use table::Table;

mod bft;
mod handle_incoming;
mod round_robin;
mod table;

#[cfg(test)]
pub mod tests;

/// Context necessary for agreement.
pub trait Context: Send + Clone {
	/// A authority ID
	type AuthorityId: Debug + Hash + Eq + Clone + Ord;
	/// The digest (hash or other unique attribute) of a candidate.
	type Digest: Debug + Hash + Eq + Clone;
	/// The group ID type
	type GroupId: Debug + Hash + Ord + Eq + Clone;
	/// A signature type.
	type Signature: Debug + Eq + Clone;
	/// Candidate type. In practice this will be a candidate receipt.
	type ParachainCandidate: Debug + Ord + Eq + Clone;
	/// The actual block proposal type. This is what is agreed upon, and
	/// is composed of multiple candidates.
	type Proposal: Debug + Eq + Clone;

	/// A future that resolves when a candidate is checked for validity.
	///
	/// In Polkadot, this will involve fetching the corresponding block data,
	/// producing the necessary ingress, and running the parachain validity function.
	type CheckCandidate: IntoFuture<Item=bool>;

	/// A future that resolves when availability of a candidate's external
	/// data is checked.
	type CheckAvailability: IntoFuture<Item=bool>;

	/// The statement batch type.
	type StatementBatch: StatementBatch<
		Self::AuthorityId,
		table::SignedStatement<Self::ParachainCandidate, Self::Digest, Self::AuthorityId, Self::Signature>,
	>;

	/// Get the digest of a candidate.
	fn candidate_digest(candidate: &Self::ParachainCandidate) -> Self::Digest;

	/// Get the digest of a proposal.
	fn proposal_digest(proposal: &Self::Proposal) -> Self::Digest;

	/// Get the group of a candidate.
	fn candidate_group(candidate: &Self::ParachainCandidate) -> Self::GroupId;

	/// Get the primary for a given round.
	fn round_proposer(&self, round: usize) -> Self::AuthorityId;

	/// Check a candidate for validity.
	fn check_validity(&self, candidate: &Self::ParachainCandidate) -> Self::CheckCandidate;

	/// Check availability of candidate data.
	fn check_availability(&self, candidate: &Self::ParachainCandidate) -> Self::CheckAvailability;

	/// Attempt to combine a set of parachain candidates into a proposal.
	///
	/// This may arbitrarily return `None`, but the intent is for `Some`
	/// to only be returned when candidates from enough groups are known.
	///
	/// "enough" may be subjective as well.
	fn create_proposal(&self, candidates: Vec<&Self::ParachainCandidate>)
		-> Option<Self::Proposal>;

	/// Check validity of a proposal. This should call out to the `check_candidate`
	/// function for all parachain candidates contained within it, as well as
	/// checking other validity constraints of the proposal.
	fn proposal_valid<F>(&self, proposal: &Self::Proposal, check_candidate: F) -> bool
		where F: FnMut(&Self::ParachainCandidate) -> bool;

	/// Get the local authority ID.
	fn local_id(&self) -> Self::AuthorityId;

	/// Sign a table validity statement with the local key.
	fn sign_table_statement(
		&self,
		statement: &table::Statement<Self::ParachainCandidate, Self::Digest>
	) -> Self::Signature;

	/// Sign a BFT agreement message.
	fn sign_bft_message(&self, &bft::Message<Self::Proposal, Self::Digest>) -> Self::Signature;
}

/// Helper for type resolution for contexts until type aliases apply bounds.
pub trait TypeResolve {
	type SignedTableStatement;
	type BftCommunication;
	type BftCommitted;
	type Misbehavior;
}

impl<C: Context> TypeResolve for C {
	type SignedTableStatement = table::SignedStatement<C::ParachainCandidate, C::Digest, C::AuthorityId, C::Signature>;
	type BftCommunication = bft::Communication<C::Proposal, C::Digest, C::AuthorityId, C::Signature>;
	type BftCommitted = bft::Committed<C::Proposal,C::Digest,C::Signature>;
	type Misbehavior = table::Misbehavior<C::ParachainCandidate, C::Digest, C::AuthorityId, C::Signature>;
}

/// Information about a specific group.
#[derive(Debug, Clone)]
pub struct GroupInfo<V: Hash + Eq> {
	/// Authorities meant to check validity of candidates.
	pub validity_guarantors: HashSet<V>,
	/// Authorities meant to check availability of candidate data.
	pub availability_guarantors: HashSet<V>,
	/// Number of votes needed for validity.
	pub needed_validity: usize,
	/// Number of votes needed for availability.
	pub needed_availability: usize,
}

struct TableContext<C: Context> {
	context: C,
	groups: HashMap<C::GroupId, GroupInfo<C::AuthorityId>>,
}

impl<C: Context> ::std::ops::Deref for TableContext<C> {
	type Target = C;

	fn deref(&self) -> &C {
		&self.context
	}
}

impl<C: Context> table::Context for TableContext<C> {
	type AuthorityId = C::AuthorityId;
	type Digest = C::Digest;
	type GroupId = C::GroupId;
	type Signature = C::Signature;
	type Candidate = C::ParachainCandidate;

	fn candidate_digest(candidate: &Self::Candidate) -> Self::Digest {
		C::candidate_digest(candidate)
	}

	fn candidate_group(candidate: &Self::Candidate) -> Self::GroupId {
		C::candidate_group(candidate)
	}

	fn is_member_of(&self, authority: &Self::AuthorityId, group: &Self::GroupId) -> bool {
		self.groups.get(group).map_or(false, |g| g.validity_guarantors.contains(authority))
	}

	fn is_availability_guarantor_of(&self, authority: &Self::AuthorityId, group: &Self::GroupId) -> bool {
		self.groups.get(group).map_or(false, |g| g.availability_guarantors.contains(authority))
	}

	fn requisite_votes(&self, group: &Self::GroupId) -> (usize, usize) {
		self.groups.get(group).map_or(
			(usize::max_value(), usize::max_value()),
			|g| (g.needed_validity, g.needed_availability),
		)
	}
}

// A shared table object.
struct SharedTableInner<C: Context> {
	table: Table<TableContext<C>>,
	proposed_digest: Option<C::Digest>,
	awaiting_proposal: Vec<oneshot::Sender<C::Proposal>>,
}

impl<C: Context> SharedTableInner<C> {
	fn import_statement(
		&mut self,
		context: &TableContext<C>,
		statement: <C as TypeResolve>::SignedTableStatement,
		received_from: Option<C::AuthorityId>
	) -> Option<table::Summary<C::Digest, C::GroupId>> {
		self.table.import_statement(context, statement, received_from)
	}

	fn update_proposal(&mut self, context: &TableContext<C>) {
		if self.awaiting_proposal.is_empty() { return }
		let proposal_candidates = self.table.proposed_candidates(context);
		if let Some(proposal) = context.context.create_proposal(proposal_candidates) {
			for sender in self.awaiting_proposal.drain(..) {
				let _ = sender.send(proposal.clone());
			}
		}
	}

	fn get_proposal(&mut self, context: &TableContext<C>) -> oneshot::Receiver<C::Proposal> {
		let (tx, rx) = oneshot::channel();
		self.awaiting_proposal.push(tx);
		self.update_proposal(context);
		rx
	}

	fn proposal_valid(&mut self, context: &TableContext<C>, proposal: &C::Proposal) -> bool {
		context.context.proposal_valid(proposal, |contained_candidate| {
			// check that the candidate is valid (has enough votes)
			let digest = C::candidate_digest(contained_candidate);
			self.table.candidate_includable(&digest, context)
		})
	}
}

/// A shared table object.
pub struct SharedTable<C: Context> {
	context: Arc<TableContext<C>>,
	inner: Arc<Mutex<SharedTableInner<C>>>,
}

impl<C: Context> Clone for SharedTable<C> {
	fn clone(&self) -> Self {
		SharedTable {
			context: self.context.clone(),
			inner: self.inner.clone()
		}
	}
}

impl<C: Context> SharedTable<C> {
	/// Create a new shared table.
	pub fn new(context: C, groups: HashMap<C::GroupId, GroupInfo<C::AuthorityId>>) -> Self {
		SharedTable {
			context: Arc::new(TableContext { context, groups }),
			inner: Arc::new(Mutex::new(SharedTableInner {
				table: Table::default(),
				awaiting_proposal: Vec::new(),
				proposed_digest: None,
			}))
		}
	}

	/// Import a single statement.
	pub fn import_statement(
		&self,
		statement: <C as TypeResolve>::SignedTableStatement,
		received_from: Option<C::AuthorityId>,
	) -> Option<table::Summary<C::Digest, C::GroupId>> {
		self.inner.lock().import_statement(&*self.context, statement, received_from)
	}

	/// Sign and import a local statement.
	pub fn sign_and_import(
		&self,
		statement: table::Statement<C::ParachainCandidate, C::Digest>,
	) -> Option<table::Summary<C::Digest, C::GroupId>> {
		let proposed_digest = match statement {
			table::Statement::Candidate(ref c) => Some(C::candidate_digest(c)),
			_ => None,
		};

		let signed_statement = table::SignedStatement {
			signature: self.context.sign_table_statement(&statement),
			sender: self.context.local_id(),
			statement,
		};

		let mut inner = self.inner.lock();
		if proposed_digest.is_some() {
			inner.proposed_digest = proposed_digest;
		}

		inner.import_statement(&*self.context, signed_statement, None)
	}

	/// Import many statements at once.
	///
	/// Provide an iterator yielding pairs of (statement, received_from).
	pub fn import_statements<I, U>(&self, iterable: I) -> U
		where
			I: IntoIterator<Item=(<C as TypeResolve>::SignedTableStatement, Option<C::AuthorityId>)>,
			U: ::std::iter::FromIterator<table::Summary<C::Digest, C::GroupId>>,
	{
		let mut inner = self.inner.lock();

		iterable.into_iter().filter_map(move |(statement, received_from)| {
			inner.import_statement(&*self.context, statement, received_from)
		}).collect()
	}

	/// Update the proposal sealing.
	pub fn update_proposal(&self) {
		self.inner.lock().update_proposal(&*self.context)
	}

	/// Register interest in receiving a proposal when ready.
	/// If one is ready immediately, it will be provided.
	pub fn get_proposal(&self) -> oneshot::Receiver<C::Proposal> {
		self.inner.lock().get_proposal(&*self.context)
	}

	/// Check if a proposal is valid.
	pub fn proposal_valid(&self, proposal: &C::Proposal) -> bool {
		self.inner.lock().proposal_valid(&*self.context, proposal)
	}

	/// Execute a closure using a specific candidate.
	///
	/// Deadlocks if called recursively.
	pub fn with_candidate<F, U>(&self, digest: &C::Digest, f: F) -> U
		where F: FnOnce(Option<&C::ParachainCandidate>) -> U
	{
		let inner = self.inner.lock();
		f(inner.table.get_candidate(digest))
	}

	/// Get all witnessed misbehavior.
	pub fn get_misbehavior(&self) -> HashMap<C::AuthorityId, <C as TypeResolve>::Misbehavior> {
		self.inner.lock().table.get_misbehavior().clone()
	}

	/// Fill a statement batch.
	pub fn fill_batch(&self, batch: &mut C::StatementBatch) {
		self.inner.lock().table.fill_batch(batch);
	}

	/// Get the local proposed candidate digest.
	pub fn proposed_digest(&self) -> Option<C::Digest> {
		self.inner.lock().proposed_digest.clone()
	}

	// Get a handle to the table context.
	fn context(&self) -> &TableContext<C> {
		&*self.context
	}
}

/// Errors that can occur during agreement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error {
	IoTerminated,
	FaultyTimer,
	CannotPropose,
}

impl From<bft::InputStreamConcluded> for Error {
	fn from(_: bft::InputStreamConcluded) -> Error {
		Error::IoTerminated
	}
}

/// Context owned by the BFT future necessary to execute the logic.
pub struct BftContext<C: Context> {
	context: C,
	table: SharedTable<C>,
	timer: Timer,
	round_timeout_multiplier: u64,
}

impl<C: Context> bft::Context for BftContext<C>
	where C::Proposal: 'static,
{
	type AuthorityId = C::AuthorityId;
	type Digest = C::Digest;
	type Signature = C::Signature;
	type Candidate = C::Proposal;
	type RoundTimeout = Box<Future<Item=(),Error=Error>>;
	type CreateProposal = Box<Future<Item=Self::Candidate,Error=Error>>;

	fn local_id(&self) -> Self::AuthorityId {
		self.context.local_id()
	}

	fn proposal(&self) -> Self::CreateProposal {
		Box::new(self.table.get_proposal().map_err(|_| Error::CannotPropose))
	}

	fn candidate_digest(&self, candidate: &Self::Candidate) -> Self::Digest {
		C::proposal_digest(candidate)
	}

	fn sign_local(&self, message: bft::Message<Self::Candidate, Self::Digest>)
		-> bft::LocalizedMessage<Self::Candidate, Self::Digest, Self::AuthorityId, Self::Signature>
	{
		let sender = self.local_id();
		let signature = self.context.sign_bft_message(&message);
		bft::LocalizedMessage {
			message,
			sender,
			signature,
		}
	}

	fn round_proposer(&self, round: usize) -> Self::AuthorityId {
		self.context.round_proposer(round)
	}

	fn candidate_valid(&self, proposal: &Self::Candidate) -> bool {
		self.table.proposal_valid(proposal)
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		let round = ::std::cmp::min(63, round) as u32;
		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		Box::new(self.timer.sleep(Duration::from_secs(timeout))
			.map_err(|_| Error::FaultyTimer))
	}
}


/// Parameters necessary for agreement.
pub struct AgreementParams<C: Context> {
	/// The context itself.
	pub context: C,
	/// For scheduling timeouts.
	pub timer: Timer,
	/// The statement table.
	pub table: SharedTable<C>,
	/// The number of nodes.
	pub nodes: usize,
	/// The maximum number of faulty nodes.
	pub max_faulty: usize,
	/// The round timeout multiplier: 2^round_number is multiplied by this.
	pub round_timeout_multiplier: u64,
	/// The maximum amount of messages to queue.
	pub message_buffer_size: usize,
	/// Interval to attempt forming proposals over.
	pub form_proposal_interval: Duration,
}

/// Recovery for messages
pub trait MessageRecovery<C: Context> {
	/// The unchecked message type. This implies that work hasn't been done
	/// to decode the payload and check and authenticate a signature.
	type UncheckedMessage;

	/// Attempt to transform a checked message into an unchecked.
	fn check_message(&self, Self::UncheckedMessage) -> Option<CheckedMessage<C>>;
}

/// A batch of statements to send out.
pub trait StatementBatch<V, T> {
	/// Get the target authorities of these statements.
	fn targets(&self) -> &[V];

	/// If the batch is empty.
	fn is_empty(&self) -> bool;

	/// Push a statement onto the batch. Returns false when the batch is full.
	///
	/// This is meant to do work like incrementally serializing the statements
	/// into a vector of bytes while making sure the length is below a certain
	/// amount.
	fn push(&mut self, statement: T) -> bool;
}

/// Recovered and fully checked messages.
pub enum CheckedMessage<C: Context> {
	/// Messages meant for the BFT agreement logic.
	Bft(<C as TypeResolve>::BftCommunication),
	/// Statements circulating about the table.
	Table(Vec<<C as TypeResolve>::SignedTableStatement>),
}

/// Outgoing messages to the network.
#[derive(Debug, Clone)]
pub enum OutgoingMessage<C: Context> {
	/// Messages meant for BFT agreement peers.
	Bft(<C as TypeResolve>::BftCommunication),
	/// Batches of table statements.
	Table(C::StatementBatch),
}

/// Create an agreement future, and I/O streams.
// TODO: kill 'static bounds and use impl Future.
pub fn agree<
	Context,
	NetIn,
	NetOut,
	Recovery,
	PropagateStatements,
	LocalCandidate,
	Err,
>(
	params: AgreementParams<Context>,
	net_in: NetIn,
	net_out: NetOut,
	recovery: Recovery,
	propagate_statements: PropagateStatements,
	local_candidate: LocalCandidate,
)
	-> Box<Future<Item=<Context as TypeResolve>::BftCommitted,Error=Error>>
	where
		Context: ::Context + 'static,
		Context::CheckCandidate: IntoFuture<Error=Err>,
		Context::CheckAvailability: IntoFuture<Error=Err>,
		NetIn: Stream<Item=(Context::AuthorityId, Vec<Recovery::UncheckedMessage>),Error=Err> + 'static,
		NetOut: Sink<SinkItem=OutgoingMessage<Context>> + 'static,
		Recovery: MessageRecovery<Context> + 'static,
		PropagateStatements: Stream<Item=Context::StatementBatch,Error=Err> + 'static,
		LocalCandidate: IntoFuture<Item=Context::ParachainCandidate> + 'static
{
	let (bft_in_in, bft_in_out) = mpsc::unbounded();
	let (bft_out_in, bft_out_out) = mpsc::unbounded();

	let agreement = {
		let bft_context = BftContext {
			context: params.context,
			table: params.table.clone(),
			timer: params.timer.clone(),
			round_timeout_multiplier: params.round_timeout_multiplier,
		};

		bft::agree(
			bft_context,
			params.nodes,
			params.max_faulty,
			bft_in_out.map(bft::ContextCommunication).map_err(|_| Error::IoTerminated),
			bft_out_in.sink_map_err(|_| Error::IoTerminated),
		)
	};

	let route_messages_in = {
		let round_robin = round_robin::RoundRobinBuffer::new(net_in, params.message_buffer_size);

		let round_robin_recovered = round_robin
			.filter_map(move |(sender, msg)| recovery.check_message(msg).map(move |x| (sender, x)));

		handle_incoming::HandleIncoming::new(
			params.table.clone(),
			round_robin_recovered,
			bft_in_in,
		).map_err(|_| Error::IoTerminated)
	};

	let route_messages_out = {
		let table = params.table.clone();
		let periodic_table_statements = propagate_statements
			.or_else(|_| ::futures::future::empty()) // halt the stream instead of error.
			.map(move |mut batch| { table.fill_batch(&mut batch); batch })
			.filter(|b| !b.is_empty())
			.map(OutgoingMessage::Table);

		let complete_out_stream = bft_out_out
			.map_err(|_| Error::IoTerminated)
			.map(|bft::ContextCommunication(x)| x)
			.map(OutgoingMessage::Bft)
			.select(periodic_table_statements);

		net_out.sink_map_err(|_| Error::IoTerminated).send_all(complete_out_stream)
	};

	let import_local_candidate = {
		let table = params.table.clone();
		local_candidate
			.into_future()
			.map(table::Statement::Candidate)
			.map(Some)
			.or_else(|_| Ok(None))
			.map(move |s| if let Some(s) = s {
				table.sign_and_import(s);
			})
	};

	let create_proposal_on_interval = {
		let table = params.table;
		params.timer.interval(params.form_proposal_interval)
			.map_err(|_| Error::FaultyTimer)
			.for_each(move |_| { table.update_proposal(); Ok(()) })
	};

	// if these auxiliary futures terminate before the agreement, then
	// that is an error.
	let auxiliary_futures = route_messages_in.join4(
		create_proposal_on_interval,
		route_messages_out,
		import_local_candidate,
	).and_then(|_| Err(Error::IoTerminated));

	let future = agreement
		.select(auxiliary_futures)
		.map(|(committed, _)| committed)
		.map_err(|(e, _)| e);

	Box::new(future)
}
