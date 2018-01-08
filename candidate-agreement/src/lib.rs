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
//! Validators are split into groups by parachain, and each validator might come
//! up its own candidate for their parachain. Within groups, validators pass around
//! their candidates and produce statements of validity.
//!
//! Any candidate that receives majority approval by the validators in a group
//! may be subject to inclusion, unless any validators flag that candidate as invalid.
//!
//! Wrongly flagging as invalid should be strongly disincentivized, so that in the
//! equilibrium state it is not expected to happen. Likewise with the submission
//! of invalid blocks.
//!
//! Groups themselves may be compromised by malicious validators.

extern crate futures;
extern crate parking_lot;
extern crate tokio_timer;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;

use futures::prelude::*;
use futures::sync::{mpsc, oneshot};
use parking_lot::Mutex;
use tokio_timer::Timer;

use table::Table;

pub mod bft;
pub mod table;

/// Context necessary for agreement.
pub trait Context: Send + Clone {
	/// A validator ID
	type ValidatorId: Debug + Hash + Eq + Clone;
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

	/// Get the digest of a candidate.
	fn candidate_digest(candidate: &Self::ParachainCandidate) -> Self::Digest;

	/// Get the digest of a proposal.
	fn proposal_digest(proposal: &Self::Proposal) -> Self::Digest;

	/// Get the group of a candidate.
	fn candidate_group(candidate: &Self::ParachainCandidate) -> Self::GroupId;

	/// Get the primary for a given round.
	fn round_proposer(&self, round: usize) -> Self::ValidatorId;

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

	/// Get the local validator ID.
	fn local_id(&self) -> Self::ValidatorId;

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
}

impl<C: Context> TypeResolve for C {
	type SignedTableStatement = table::SignedStatement<C::ParachainCandidate, C::Digest, C::ValidatorId, C::Signature>;
	type BftCommunication = bft::Communication<C::Proposal, C::Digest, C::ValidatorId, C::Signature>;
}

/// Information about a specific group.
#[derive(Debug, Clone)]
pub struct GroupInfo<V: Hash + Eq> {
	/// Validators meant to check validity of candidates.
	pub validity_guarantors: HashSet<V>,
	/// Validators meant to check availability of candidate data.
	pub availability_guarantors: HashSet<V>,
	/// Number of votes needed for validity.
	pub needed_validity: usize,
	/// Number of votes needed for availability.
	pub needed_availability: usize,
}

struct TableContext<C: Context> {
	context: C,
	groups: HashMap<C::GroupId, GroupInfo<C::ValidatorId>>,
}

impl<C: Context> table::Context for TableContext<C> {
	type ValidatorId = C::ValidatorId;
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

	fn is_member_of(&self, validator: &Self::ValidatorId, group: &Self::GroupId) -> bool {
		self.groups.get(group).map_or(false, |g| g.validity_guarantors.contains(validator))
	}

	fn is_availability_guarantor_of(&self, validator: &Self::ValidatorId, group: &Self::GroupId) -> bool {
		self.groups.get(group).map_or(false, |g| g.availability_guarantors.contains(validator))
	}

	fn requisite_votes(&self, group: &Self::GroupId) -> (usize, usize) {
		self.groups.get(group).map_or(
			(usize::max_value(), usize::max_value()),
			|g| (g.needed_validity, g.needed_availability),
		)
	}
}

// A shared table object.
struct SharedTableInner<C: Context + Clone> {
	context: TableContext<C>,
	table: Table<TableContext<C>>,
	awaiting_proposal: Vec<oneshot::Sender<C::Proposal>>,
}

impl<C: Context + Clone> SharedTableInner<C> {
	fn import_statement(
		&mut self,
		statement: <C as TypeResolve>::SignedTableStatement,
		received_from: Option<C::ValidatorId>
	) -> Option<table::Summary<C::Digest, C::GroupId>> {
		self.table.import_statement(&self.context, statement, received_from)
	}

	fn update_proposal(&mut self) {
		if self.awaiting_proposal.is_empty() { return }
		let proposal_candidates = self.table.proposed_candidates(&self.context);
		if let Some(proposal) = self.context.context.create_proposal(proposal_candidates) {
			for sender in self.awaiting_proposal.drain(..) {
				let _ = sender.send(proposal.clone());
			}
		}
	}

	fn get_proposal(&mut self) -> oneshot::Receiver<C::Proposal> {
		let (tx, rx) = oneshot::channel();
		self.awaiting_proposal.push(tx);
		self.update_proposal();
		rx
	}

	fn proposal_valid(&mut self, proposal: &C::Proposal) -> bool {
		self.context.context.proposal_valid(proposal, |contained_candidate| {
			// check that the candidate is valid (has enough votes)
			let digest = C::candidate_digest(contained_candidate);
			self.table.candidate_includable(&digest, &self.context)
		})
	}
}

/// A shared table object.
pub struct SharedTable<C: Context> {
	inner: Arc<Mutex<SharedTableInner<C>>>,
}

impl<C: Context> Clone for SharedTable<C> {
	fn clone(&self) -> Self {
		SharedTable { inner: self.inner.clone() }
	}
}

impl<C: Context> SharedTable<C> {
	/// Create a new shared table.
	pub fn new(context: C, groups: HashMap<C::GroupId, GroupInfo<C::ValidatorId>>) -> Self {
		SharedTable {
			inner: Arc::new(Mutex::new(SharedTableInner {
				table: Table::default(),
				context: TableContext { context, groups },
				awaiting_proposal: Vec::new(),
			}))
		}
	}

	/// Import a single statement.
	pub fn import_statement(
		&self,
		statement: <C as TypeResolve>::SignedTableStatement,
		received_from: Option<C::ValidatorId>,
	) -> Option<table::Summary<C::Digest, C::GroupId>> {
		self.inner.lock().import_statement(statement, received_from)
	}

	/// Import many statements at once.
	///
	/// Provide an iterator yielding pairs of (statement, received_from).
	pub fn import_statements<I, U>(&self, iterable: I) -> U
		where
			I: IntoIterator<Item=(<C as TypeResolve>::SignedTableStatement, Option<C::ValidatorId>)>,
			U: ::std::iter::FromIterator<table::Summary<C::Digest, C::GroupId>>,
	{
		let mut inner = self.inner.lock();

		iterable.into_iter().filter_map(move |(statement, received_from)| {
			inner.import_statement(statement, received_from)
		}).collect()
	}

	/// Update the proposal sealing.
	pub fn update_proposal(&self) {
		self.inner.lock().update_proposal()
	}

	/// Register interest in receiving a proposal when ready.
	/// If one is ready immediately, it will be provided.
	pub fn get_proposal(&self) -> oneshot::Receiver<C::Proposal> {
		self.inner.lock().get_proposal()
	}

	/// Check if a proposal is valid.
	pub fn proposal_valid(&self, proposal: &C::Proposal) -> bool {
		self.inner.lock().proposal_valid(proposal)
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
	where
		C::Proposal: 'static,
{
	type ValidatorId = C::ValidatorId;
	type Digest = C::Digest;
	type Signature = C::Signature;
	type Candidate = C::Proposal;
	type RoundTimeout = Box<Future<Item=(),Error=Error>>;
	type CreateProposal = Box<Future<Item=Self::Candidate,Error=Error>>;

	fn local_id(&self) -> Self::ValidatorId {
		self.context.local_id()
	}

	fn proposal(&self) -> Self::CreateProposal {
		Box::new(self.table.get_proposal().map_err(|_| Error::CannotPropose))
	}

	fn candidate_digest(&self, candidate: &Self::Candidate) -> Self::Digest {
		C::proposal_digest(candidate)
	}

	fn sign_local(&self, message: bft::Message<Self::Candidate, Self::Digest>)
		-> bft::LocalizedMessage<Self::Candidate, Self::Digest, Self::ValidatorId, Self::Signature>
	{
		let sender = self.local_id();
		let signature = self.context.sign_bft_message(&message);
		bft::LocalizedMessage {
			message,
			sender,
			signature,
		}
	}

	fn round_proposer(&self, round: usize) -> Self::ValidatorId {
		self.context.round_proposer(round)
	}

	fn candidate_valid(&self, proposal: &Self::Candidate) -> bool {
		self.table.proposal_valid(proposal)
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		let round = ::std::cmp::max(63, round) as u32;
		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		Box::new(self.timer.sleep(::std::time::Duration::from_secs(timeout))
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
}

/// Future and I/O to reach agreement.
pub struct Agreement<C: bft::Context + 'static> {
	/// The future holding the actual BFT logic.
	pub bft: Box<Future<
		Item=bft::Committed<C::Candidate, C::Digest, C::Signature>,
		Error=Error,
	>>,
	/// The input sink.
	pub input: mpsc::UnboundedSender<bft::ContextCommunication<C>>,
	/// The output stream.
	pub output: mpsc::UnboundedReceiver<bft::ContextCommunication<C>>,
}

/// Create an agreement future, and I/O streams.
pub fn agree<C: Context + 'static>(params: AgreementParams<C>)
	-> Agreement<BftContext<C>>
{
	let (in_in, in_out) = mpsc::unbounded();
	let (out_in, out_out) = mpsc::unbounded();

	let bft_context = BftContext {
		context: params.context,
		table: params.table,
		timer: params.timer,
		round_timeout_multiplier: params.round_timeout_multiplier,
	};

	let agreement = bft::agree(
		bft_context,
		params.nodes,
		params.max_faulty,
		in_out.map_err(|_| Error::IoTerminated),
		out_in.sink_map_err(|_| Error::IoTerminated),
	);
	Agreement {
		bft: Box::new(agreement),
		input: in_in,
		output: out_out,
	}
}
