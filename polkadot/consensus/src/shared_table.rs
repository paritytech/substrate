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

//! Parachain statement table meant to to shared with a message router
//! and a consensus proposer.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use table::{self, Table, Context as TableContextTrait};
use table::generic::Statement as GenericStatement;
use polkadot_primitives::Hash;
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic, CandidateReceipt};
use primitives::AuthorityId;

use parking_lot::Mutex;
use futures::{future, prelude::*};

use super::{GroupInfo, TableRouter};

struct TableContext {
	parent_hash: Hash,
	key: Arc<::ed25519::Pair>,
	groups: HashMap<ParaId, GroupInfo>,
}

impl table::Context for TableContext {
	fn is_member_of(&self, authority: &AuthorityId, group: &ParaId) -> bool {
		self.groups.get(group).map_or(false, |g| g.validity_guarantors.contains(authority))
	}

	fn is_availability_guarantor_of(&self, authority: &AuthorityId, group: &ParaId) -> bool {
		self.groups.get(group).map_or(false, |g| g.availability_guarantors.contains(authority))
	}

	fn requisite_votes(&self, group: &ParaId) -> (usize, usize) {
		self.groups.get(group).map_or(
			(usize::max_value(), usize::max_value()),
			|g| (g.needed_validity, g.needed_availability),
		)
	}
}

impl TableContext {
	fn local_id(&self) -> AuthorityId {
		self.key.public().0
	}

	fn sign_statement(&self, statement: table::Statement) -> table::SignedStatement {
		let signature = ::sign_table_statement(&statement, &self.key, &self.parent_hash).into();
		let local_id = self.key.public().0;

		table::SignedStatement {
			statement,
			signature,
			sender: local_id,
		}
	}
}

/// Source of statements
pub enum StatementSource {
	/// Locally produced statement.
	Local,
	/// Received statement from remote source, with optional sender.
	Remote(Option<AuthorityId>),
}

// A shared table object.
struct SharedTableInner {
	table: Table<TableContext>,
	proposed_digest: Option<Hash>,
	checked_validity: HashSet<Hash>,
	checked_availability: HashSet<Hash>,
}

impl SharedTableInner {
	// Import a single statement. Provide a handle to a table router.
	fn import_statement<R: TableRouter>(
		&mut self,
		context: &TableContext,
		router: &R,
		statement: table::SignedStatement,
		statement_source: StatementSource,
	) -> StatementProducer<<R::FetchCandidate as IntoFuture>::Future, <R::FetchExtrinsic as IntoFuture>::Future> {
		// this blank producer does nothing until we attach some futures
		// and set a candidate digest.
		let mut producer = Default::default();

		let received_from = match statement_source {
			StatementSource::Local => return producer,
			StatementSource::Remote(from) => from,
		};

		let summary = match self.table.import_statement(context, statement, received_from) {
			Some(summary) => summary,
			None => return producer,
		};

		producer.candidate_digest = Some(summary.candidate);

		let local_id = context.local_id();

		let is_validity_member = context.is_member_of(&local_id, &summary.group_id);
		let is_availability_member =
			context.is_availability_guarantor_of(&local_id, &summary.group_id);

		let digest = &summary.candidate;

		// TODO: consider a strategy based on the number of candidate votes as well.
		// only check validity if this wasn't locally proposed.
		let checking_validity = is_validity_member
			&& self.proposed_digest.as_ref().map_or(true, |d| d != digest)
			&& self.checked_validity.insert(digest.clone());

		let checking_availability = is_availability_member
			&& self.checked_availability.insert(digest.clone());

		if checking_validity || checking_availability {
			match self.table.get_candidate(&digest) {
				None => {} // TODO: handle table inconsistency somehow?
				Some(candidate) => {
					if checking_validity {
						producer.fetch_block_data = Some(
							router.fetch_block_data(candidate).into_future().fuse()
						);
					}

					if checking_availability {
						producer.fetch_extrinsic = Some(
							router.fetch_extrinsic_data(candidate).into_future().fuse()
						);
					}
				}
			}
		}

		producer
	}
}

/// Produced statements about a specific candidate.
/// Both may be `None`.
#[derive(Default)]
pub struct ProducedStatements {
	/// A statement about the validity of the candidate.
	pub validity: Option<table::Statement>,
	/// A statement about availability of data. If this is `Some`,
	/// then `block_data` and `extrinsic` should be `Some` as well.
	pub availability: Option<table::Statement>,
	/// Block data to ensure availability of.
	pub block_data: Option<BlockData>,
	/// Extrinsic data to ensure availability of.
	pub extrinsic: Option<Extrinsic>,
}

/// Future that produces statements about a specific candidate.
pub struct StatementProducer<D: Future, E: Future> {
	fetch_block_data: Option<future::Fuse<D>>,
	fetch_extrinsic: Option<future::Fuse<E>>,
	produced_statements: ProducedStatements,
	candidate_digest: Option<Hash>,
}

impl<D: Future, E: Future> Default for StatementProducer<D, E> {
	fn default() -> Self {
		StatementProducer {
			fetch_block_data: None,
			fetch_extrinsic: None,
			produced_statements: Default::default(),
			candidate_digest: Default::default(),
		}
	}
}

impl<D, E, Err> Future for StatementProducer<D, E>
	where
		D: Future<Item=BlockData,Error=Err>,
		E: Future<Item=Extrinsic,Error=Err>,
{
	type Item = ProducedStatements;
	type Error = Err;

	fn poll(&mut self) -> Poll<ProducedStatements, Err> {
		let candidate_digest = match self.candidate_digest.as_ref() {
			Some(x) => x,
			None => return Ok(Async::Ready(::std::mem::replace(&mut self.produced_statements, Default::default()))),
		};

		let mut done = true;
		if let Some(ref mut fetch_block_data) = self.fetch_block_data {
			match fetch_block_data.poll()? {
				Async::Ready(block_data) => {
					// TODO [PoC-2]: validate block data here and make statement.
					self.produced_statements.block_data = Some(block_data);
				},
				Async::NotReady => {
					done = false;
				}
			}
		}

		if let Some(ref mut fetch_extrinsic) = self.fetch_extrinsic {
			match fetch_extrinsic.poll()? {
				Async::Ready(extrinsic) => {
					self.produced_statements.extrinsic = Some(extrinsic);
				}
				Async::NotReady => {
					done = false;
				}
			}
		}

		if done {
			let mut produced = ::std::mem::replace(&mut self.produced_statements, Default::default());
			if produced.block_data.is_some() && produced.extrinsic.is_some() {
				// produce a statement about availability.
				produced.availability = Some(GenericStatement::Available(candidate_digest.clone()));
			}
			Ok(Async::Ready(produced))
		} else {
			Ok(Async::NotReady)
		}
	}
}

/// A shared table object.
pub struct SharedTable {
	context: Arc<TableContext>,
	inner: Arc<Mutex<SharedTableInner>>,
}

impl Clone for SharedTable {
	fn clone(&self) -> Self {
		SharedTable {
			context: self.context.clone(),
			inner: self.inner.clone(),
		}
	}
}

impl SharedTable {
	/// Create a new shared table.
	///
	/// Provide the key to sign with, and the parent hash of the relay chain
	/// block being built.
	pub fn new(groups: HashMap<ParaId, GroupInfo>, key: Arc<::ed25519::Pair>, parent_hash: Hash) -> Self {
		SharedTable {
			context: Arc::new(TableContext { groups, key, parent_hash }),
			inner: Arc::new(Mutex::new(SharedTableInner {
				table: Table::default(),
				proposed_digest: None,
				checked_validity: HashSet::new(),
				checked_availability: HashSet::new(),
			}))
		}
	}

	/// Get group info.
	pub fn group_info(&self) -> &HashMap<ParaId, GroupInfo> {
		&self.context.groups
	}

	/// Import a single statement. Provide a handle to a table router
	/// for dispatching any other requests which come up.
	pub fn import_statement<R: TableRouter>(
		&self,
		router: &R,
		statement: table::SignedStatement,
		received_from: StatementSource,
	) -> StatementProducer<<R::FetchCandidate as IntoFuture>::Future, <R::FetchExtrinsic as IntoFuture>::Future> {
		self.inner.lock().import_statement(&*self.context, router, statement, received_from)
	}

	/// Sign and import a local statement.
	pub fn sign_and_import<R: TableRouter>(
		&self,
		router: &R,
		statement: table::Statement,
	) {
		let proposed_digest = match statement {
			GenericStatement::Candidate(ref c) => Some(c.hash()),
			_ => None,
		};

		let signed_statement = self.context.sign_statement(statement);

		let mut inner = self.inner.lock();
		if proposed_digest.is_some() {
			inner.proposed_digest = proposed_digest;
		}

		inner.import_statement(&*self.context, router, signed_statement, StatementSource::Local);
	}

	/// Import many statements at once.
	///
	/// Provide an iterator yielding pairs of (statement, statement_source).
	pub fn import_statements<R, I, U>(&self, router: &R, iterable: I) -> U
		where
			R: TableRouter,
			I: IntoIterator<Item=(table::SignedStatement, StatementSource)>,
			U: ::std::iter::FromIterator<StatementProducer<
				<R::FetchCandidate as IntoFuture>::Future,
				<R::FetchExtrinsic as IntoFuture>::Future>
			>,
	{
		let mut inner = self.inner.lock();

		iterable.into_iter().map(move |(statement, statement_source)| {
			inner.import_statement(&*self.context, router, statement, statement_source)
		}).collect()
	}

	/// Execute a closure using a specific candidate.
	///
	/// Deadlocks if called recursively.
	pub fn with_candidate<F, U>(&self, digest: &Hash, f: F) -> U
		where F: FnOnce(Option<&CandidateReceipt>) -> U
	{
		let inner = self.inner.lock();
		f(inner.table.get_candidate(digest))
	}

	/// Execute a closure using the current proposed set.
	///
	/// Deadlocks if called recursively.
	pub fn with_proposal<F, U>(&self, f: F) -> U
		where F: FnOnce(Vec<&CandidateReceipt>) -> U
	{
		let inner = self.inner.lock();
		f(inner.table.proposed_candidates(&*self.context))
	}

	/// Get the number of parachains which have available candidates.
	pub fn includable_count(&self) -> usize {
		self.inner.lock().table.includable_count()
	}

	/// Get all witnessed misbehavior.
	pub fn get_misbehavior(&self) -> HashMap<AuthorityId, table::Misbehavior> {
		self.inner.lock().table.get_misbehavior().clone()
	}

	/// Fill a statement batch.
	pub fn fill_batch<B: table::StatementBatch>(&self, batch: &mut B) {
		self.inner.lock().table.fill_batch(batch);
	}

	/// Get the local proposed block's hash.
	pub fn proposed_hash(&self) -> Option<Hash> {
		self.inner.lock().proposed_digest.clone()
	}
}
