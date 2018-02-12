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

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use codec::Slicable;
use table::Table;
use table::generic::Statement as GenericStatement;
use polkadot_primitives::Hash;
use polkadot_primitives::parachain::{Id as ParaId, CandidateReceipt};
use primitives::block::Block as SubstrateBlock;
use primitives::AuthorityId;

use parking_lot::Mutex;

extern crate futures;
extern crate ed25519;
extern crate parking_lot;
extern crate tokio_timer;
extern crate polkadot_statement_table as table;
extern crate polkadot_primitives;
extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

/// Information about a specific group.
#[derive(Debug, Clone)]
pub struct GroupInfo {
	/// Authorities meant to check validity of candidates.
	pub validity_guarantors: HashSet<AuthorityId>,
	/// Authorities meant to check availability of candidate data.
	pub availability_guarantors: HashSet<AuthorityId>,
	/// Number of votes needed for validity.
	pub needed_validity: usize,
	/// Number of votes needed for availability.
	pub needed_availability: usize,
}

struct TableContext {
	parent_hash: Hash,
	key: Arc<ed25519::Pair>,
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
	fn sign_statement(&self, statement: table::Statement) -> table::SignedStatement {
		let signature = sign_table_statement(&statement, &self.key, &self.parent_hash);
		let local_id = self.key.public().0;

		table::SignedStatement {
			statement,
			signature,
			sender: local_id,
		}
	}
}

/// Sign a table statement against a parent hash.
/// The actual message signed is the encoded statement concatenated with the
/// parent hash.
pub fn sign_table_statement(statement: &table::Statement, key: &ed25519::Pair, parent_hash: &Hash) -> ed25519::Signature {
	use polkadot_primitives::parachain::Statement as RawStatement;

	let raw = match *statement {
		GenericStatement::Candidate(ref c) => RawStatement::Candidate(c.clone()),
		GenericStatement::Valid(h) => RawStatement::Valid(h),
		GenericStatement::Invalid(h) => RawStatement::Invalid(h),
		GenericStatement::Available(h) => RawStatement::Available(h),
	};

	let mut encoded = raw.encode();
	encoded.extend(&parent_hash.0);

	key.sign(&encoded)
}

// A shared table object.
struct SharedTableInner {
	table: Table<TableContext>,
	proposed_digest: Option<Hash>,
}

impl SharedTableInner {
	fn import_statement(
		&mut self,
		context: &TableContext,
		statement: ::table::SignedStatement,
		received_from: Option<AuthorityId>,
	) -> Option<table::Summary> {
		self.table.import_statement(context, statement, received_from)
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
			inner: self.inner.clone()
		}
	}
}

impl SharedTable {
	/// Create a new shared table.
	///
	/// Provide the key to sign with, and the parent hash of the relay chain
	/// block being built.
	pub fn new(groups: HashMap<ParaId, GroupInfo>, key: Arc<ed25519::Pair>, parent_hash: Hash) -> Self {
		SharedTable {
			context: Arc::new(TableContext { groups, key, parent_hash }),
			inner: Arc::new(Mutex::new(SharedTableInner {
				table: Table::default(),
				proposed_digest: None,
			}))
		}
	}

	/// Import a single statement.
	pub fn import_statement(
		&self,
		statement: table::SignedStatement,
		received_from: Option<AuthorityId>,
	) -> Option<table::Summary> {
		self.inner.lock().import_statement(&*self.context, statement, received_from)
	}

	/// Sign and import a local statement.
	pub fn sign_and_import(
		&self,
		statement: table::Statement,
	) -> Option<table::Summary> {
		let proposed_digest = match statement {
			GenericStatement::Candidate(ref c) => Some(c.hash()),
			_ => None,
		};

		let signed_statement = self.context.sign_statement(statement);

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
			I: IntoIterator<Item=(table::SignedStatement, Option<AuthorityId>)>,
			U: ::std::iter::FromIterator<table::Summary>,
	{
		let mut inner = self.inner.lock();

		iterable.into_iter().filter_map(move |(statement, received_from)| {
			inner.import_statement(&*self.context, statement, received_from)
		}).collect()
	}

	/// Check if a proposal is valid.
	pub fn proposal_valid(&self, _proposal: &SubstrateBlock) -> bool {
		false // TODO
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
