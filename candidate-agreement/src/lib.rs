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

pub mod bft;
pub mod table;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use futures::prelude::*;
use tokio_timer::Timer;

use table::Table;

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

	/// Check validity of a proposal. This may also be somewhat subjective
	/// based on a monotonic-decreasing curve.
	fn proposal_valid(&self, proposal: &Self::Proposal) -> bool;

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

/// Parameters necessary for agreement.
pub struct AgreementParams<C: Context> {
	/// The context itself.
	pub context: C,
	/// For scheduling timeouts.
	pub timer: Timer,
	/// Group assignments.
	pub groups: HashMap<C::GroupId, GroupInfo<C::ValidatorId>>,
	/// The local candidate proposal.
	// TODO: replace with future.
	pub local_proposal: Option<C::ParachainCandidate>,
}

pub fn agree<C: Context + Clone>(params: AgreementParams<C>) {
	let context = params.context;
	let local_id = context.local_id();
	let mut table = Table::<TableContext<C>>::default();

	let table_context = TableContext {
		context: context.clone(),
		groups: params.groups,
	};

	if let Some(candidate) = params.local_proposal {
		let statement = table::Statement::Candidate(candidate);
		let signed_statement = table::SignedStatement {
			signature: context.sign_table_statement(&statement),
			sender: local_id.clone(),
			statement: statement,
		};

		table.import_statement(&table_context, signed_statement, None);
	}
}
