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

//! The statement table.
//!
//! This stores messages other validators issue about candidates.
//!
//! These messages are used to create a proposal submitted to a BFT consensus process.
//!
//! Proposals are formed of sets of candidates which have the requisite number of
//! validity and availability votes.
//!
//! Each parachain is associated with two sets of validators: those which can
//! propose and attest to validity of candidates, and those who can only attest
//! to availability.

use std::collections::HashSet;
use std::collections::hash_map::{HashMap, Entry};
use std::hash::Hash;
use std::fmt::Debug;

/// Context for the statement table.
pub trait Context {
	/// A validator ID
	type ValidatorId: Hash + Eq + Clone + Debug;
	/// The digest (hash or other unique attribute) of a candidate.
	type Digest: Hash + Eq + Clone + Debug;
    /// Candidate type.
	type Candidate: Ord + Eq + Clone + Debug;
	/// The group ID type
	type GroupId: Hash + Ord + Eq + Clone + Debug;
	/// A signature type.
	type Signature: Eq + Clone +  Debug;

	/// get the digest of a candidate.
	fn candidate_digest(&self, candidate: &Self::Candidate) -> Self::Digest;

	/// get the group of a candidate.
	fn candidate_group(&self, candidate: &Self::Candidate) -> Self::GroupId;

	/// Whether a validator is a member of a group.
	/// Members are meant to submit candidates and vote on validity.
	fn is_member_of(&self, validator: &Self::ValidatorId, group: &Self::GroupId) -> bool;

	/// Whether a validator is an availability guarantor of a group.
	/// Guarantors are meant to vote on availability for candidates submitted
	/// in a group.
	fn is_availability_guarantor_of(
		&self,
		validator: &Self::ValidatorId,
		group: &Self::GroupId,
	) -> bool;

	// requisite number of votes for validity and availability respectively from a group.
	fn requisite_votes(&self, group: &Self::GroupId) -> (usize, usize);
}

/// Statements circulated among peers.
#[derive(PartialEq, Eq, Debug)]
pub enum Statement<C, D> {
	/// Broadcast by a validator to indicate that this is his candidate for
	/// inclusion.
	///
	/// Broadcasting two different candidate messages per round is not allowed.
	Candidate(C),
	/// Broadcast by a validator to attest that the candidate with given digest
	/// is valid.
	Valid(D),
	/// Broadcast by a validator to attest that the auxiliary data for a candidate
	/// with given digest is available.
	Available(D),
	/// Broadcast by a validator to attest that the candidate with given digest
	/// is invalid.
	Invalid(D),
}

/// A signed statement.
#[derive(PartialEq, Eq, Debug)]
pub struct SignedStatement<C, D, V, S> {
	/// The statement.
	pub statement: Statement<C, D>,
	/// The signature.
	pub signature: S,
	/// The sender.
	pub sender: V,
}

// A unique trace for a class of valid statements issued by a validator.
//
// We keep track of which statements we have received or sent to other validators
// in order to prevent relaying the same data multiple times.
//
// The signature of the statement is replaced by the validator because the validator
// is unique while signatures are not (at least under common schemes like
// Schnorr or ECDSA).
#[derive(Hash, PartialEq, Eq, Clone)]
enum StatementTrace<V, D> {
	/// The candidate proposed by the validator.
	Candidate(V),
	/// A validity statement from that validator about the given digest.
	Valid(V, D),
	/// An invalidity statement from that validator about the given digest.
	Invalid(V, D),
	/// An availability statement from that validator about the given digest.
	Available(V, D),
}

/// Misbehavior: voting more than one way on candidate validity.
///
/// Since there are three possible ways to vote, a double vote is possible in
/// three possible combinations (unordered)
#[derive(PartialEq, Eq, Debug)]
pub enum ValidityDoubleVote<C, D, S> {
	/// Implicit vote by issuing and explicity voting validity.
	IssuedAndValidity((C, S), (D, S)),
	/// Implicit vote by issuing and explicitly voting invalidity
	IssuedAndInvalidity((C, S), (D, S)),
	/// Direct votes for validity and invalidity
	ValidityAndInvalidity(D, S, S),
}

/// Misbehavior: declaring multiple candidates.
#[derive(PartialEq, Eq, Debug)]
pub struct MultipleCandidates<C, S> {
	/// The first candidate seen.
	pub first: (C, S),
	/// The second candidate seen.
	pub second: (C, S),
}

/// Misbehavior: submitted statement for wrong group.
#[derive(PartialEq, Eq, Debug)]
pub struct UnauthorizedStatement<C, D, V, S> {
	/// A signed statement which was submitted without proper authority.
	pub statement: SignedStatement<C, D, V, S>,
}

/// Different kinds of misbehavior. All of these kinds of malicious misbehavior
/// are easily provable and extremely disincentivized.
#[derive(PartialEq, Eq, Debug)]
pub enum Misbehavior<C, D, V, S> {
	/// Voted invalid and valid on validity.
	ValidityDoubleVote(ValidityDoubleVote<C, D, S>),
	/// Submitted multiple candidates.
	MultipleCandidates(MultipleCandidates<C, S>),
	/// Submitted a message withou
	UnauthorizedStatement(UnauthorizedStatement<C, D, V, S>),
}

/// Fancy work-around for a type alias of context-based misbehavior
/// without producing compiler warnings.
pub trait ResolveMisbehavior {
	/// The misbehavior type.
	type Misbehavior;
}

impl<C: Context + ?Sized> ResolveMisbehavior for C {
	type Misbehavior = Misbehavior<C::Candidate, C::Digest, C::ValidatorId, C::Signature>;
}

// kinds of votes for validity
#[derive(Clone, PartialEq, Eq)]
enum ValidityVote<S: Eq + Clone> {
	// implicit validity vote by issuing
	Issued(S),
	// direct validity vote
	Valid(S),
	// direct invalidity vote
	Invalid(S),
}

/// A summary of import of a statement.
#[derive(Clone, PartialEq, Eq)]
pub struct Summary<D, G> {
	/// The digest of the candidate referenced.
	pub candidate: D,
	/// The group that candidate is in.
	pub group_id: G,
	/// How many validity votes are currently witnessed.
	pub validity_votes: usize,
	/// How many availability votes are currently witnessed.
	pub availability_votes: usize,
	/// Whether this has been signalled bad by at least one participant.
	pub signalled_bad: bool,
}

/// Stores votes and data about a candidate.
pub struct CandidateData<C: Context> {
	group_id: C::GroupId,
	candidate: C::Candidate,
	validity_votes: HashMap<C::ValidatorId, ValidityVote<C::Signature>>,
	availability_votes: HashMap<C::ValidatorId, C::Signature>,
	indicated_bad_by: Vec<C::ValidatorId>,
}

impl<C: Context> CandidateData<C> {
	/// whether this has been indicated bad by anyone.
	pub fn indicated_bad(&self) -> bool {
		!self.indicated_bad_by.is_empty()
	}

	/// Get an iterator over those who have indicated this candidate valid.
	// TODO: impl trait
	pub fn voted_valid_by<'a>(&'a self) -> Box<Iterator<Item=C::ValidatorId> + 'a> {
		Box::new(self.validity_votes.iter().filter_map(|(v, vote)| {
			match *vote {
				ValidityVote::Issued(_) | ValidityVote::Valid(_) => Some(v.clone()),
				ValidityVote::Invalid(_) => None,
			}
		}))
	}

	// Candidate data can be included in a proposal
	// if it has enough validity and availability votes
	// and no validators have called it bad.
	fn can_be_included(&self, validity_threshold: usize, availability_threshold: usize) -> bool {
		self.indicated_bad_by.is_empty()
			&& self.validity_votes.len() >= validity_threshold
			&& self.availability_votes.len() >= availability_threshold
	}

	fn summary(&self, digest: C::Digest) -> Summary<C::Digest, C::GroupId> {
		Summary {
			candidate: digest,
			group_id: self.group_id.clone(),
			validity_votes: self.validity_votes.len() - self.indicated_bad_by.len(),
			availability_votes: self.availability_votes.len(),
			signalled_bad: self.indicated_bad(),
		}
	}
}

// validator metadata
struct ValidatorData<C: Context> {
	proposal: Option<(C::Digest, C::Signature)>,
	known_statements: HashSet<StatementTrace<C::ValidatorId, C::Digest>>,
}

/// Create a new, empty statement table.
pub fn create<C: Context>() -> Table<C> {
	Table {
		validator_data: HashMap::default(),
		detected_misbehavior: HashMap::default(),
		candidate_votes: HashMap::default(),
	}
}

/// Stores votes
#[derive(Default)]
pub struct Table<C: Context> {
	validator_data: HashMap<C::ValidatorId, ValidatorData<C>>,
	detected_misbehavior: HashMap<C::ValidatorId, <C as ResolveMisbehavior>::Misbehavior>,
	candidate_votes: HashMap<C::Digest, CandidateData<C>>,
}

impl<C: Context> Table<C> {
	/// Produce a set of proposed candidates.
	///
	/// This will be at most one per group, consisting of the
	/// best candidate for each group with requisite votes for inclusion.
	pub fn proposed_candidates(&self, context: &C) -> Vec<C::Candidate> {
		use std::collections::BTreeMap;
		use std::collections::btree_map::Entry as BTreeEntry;

		let mut best_candidates = BTreeMap::new();
		for candidate_data in self.candidate_votes.values() {
			let group_id = &candidate_data.group_id;
			let (validity_t, availability_t) = context.requisite_votes(group_id);

			if !candidate_data.can_be_included(validity_t, availability_t) { continue }
			let candidate = &candidate_data.candidate;
			match best_candidates.entry(group_id.clone()) {
				BTreeEntry::Occupied(mut occ) => {
					let candidate_ref = occ.get_mut();
					if *candidate_ref < candidate {
						*candidate_ref = candidate;
					}
				}
				BTreeEntry::Vacant(vacant) => { vacant.insert(candidate); },
			}
		}

		best_candidates.values().map(|v| C::Candidate::clone(v)).collect::<Vec<_>>()
	}

	/// Get an iterator of all candidates with a given group.
	// TODO: impl iterator
	pub fn candidates_in_group<'a>(&'a self, group_id: C::GroupId)
		-> Box<Iterator<Item=&'a CandidateData<C>> + 'a>
	{
		Box::new(self.candidate_votes.values().filter(move |c| c.group_id == group_id))
	}

	/// Drain all misbehavior observed up to this point.
	pub fn drain_misbehavior(&mut self) -> HashMap<C::ValidatorId, <C as ResolveMisbehavior>::Misbehavior> {
		::std::mem::replace(&mut self.detected_misbehavior, HashMap::new())
	}

	/// Import a signed statement. Signatures should be checked for validity, and the
	/// sender should be checked to actually be a validator.
	///
	/// This can note the origin of the statement to indicate that he has
	/// seen it already.
	pub fn import_statement(
		&mut self,
		context: &C,
		statement: SignedStatement<C::Candidate, C::Digest, C::ValidatorId, C::Signature>,
		from: Option<C::ValidatorId>
	) -> Option<Summary<C::Digest, C::GroupId>> {
		let SignedStatement { statement, signature, sender: signer } = statement;

		let trace = match statement {
			Statement::Candidate(_) => StatementTrace::Candidate(signer.clone()),
			Statement::Valid(ref d) => StatementTrace::Valid(signer.clone(), d.clone()),
			Statement::Invalid(ref d) => StatementTrace::Invalid(signer.clone(), d.clone()),
			Statement::Available(ref d) => StatementTrace::Available(signer.clone(), d.clone()),
		};

		let (maybe_misbehavior, maybe_summary) = match statement {
			Statement::Candidate(candidate) => self.import_candidate(
				context,
				signer.clone(),
				candidate,
				signature
			),
			Statement::Valid(digest) => self.validity_vote(
				context,
				signer.clone(),
				digest,
				ValidityVote::Valid(signature),
			),
			Statement::Invalid(digest) => self.validity_vote(
				context,
				signer.clone(),
				digest,
				ValidityVote::Invalid(signature),
			),
			Statement::Available(digest) => self.availability_vote(
				context,
				signer.clone(),
				digest,
				signature,
			)
		};

		if let Some(misbehavior) = maybe_misbehavior {
			// all misbehavior in agreement is provable and actively malicious.
			// punishments are not cumulative.
			self.detected_misbehavior.insert(signer, misbehavior);
		} else {
			if let Some(from) = from {
				self.note_trace_seen(trace.clone(), from);
			}

			self.note_trace_seen(trace, signer);
		}

		maybe_summary
	}

	fn note_trace_seen(&mut self, trace: StatementTrace<C::ValidatorId, C::Digest>, known_by: C::ValidatorId) {
		self.validator_data.entry(known_by).or_insert_with(|| ValidatorData {
			proposal: None,
			known_statements: HashSet::default(),
		}).known_statements.insert(trace);
	}

	fn import_candidate(
		&mut self,
		context: &C,
		from: C::ValidatorId,
		candidate: C::Candidate,
		signature: C::Signature,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let group = context.candidate_group(&candidate);
		if !context.is_member_of(&from, &group) {
			return (
				Some(Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
					statement: SignedStatement {
						signature,
						statement: Statement::Candidate(candidate),
						sender: from,
					},
				})),
				None,
			);
		}

		// check that validator hasn't already specified another candidate.
		let digest = context.candidate_digest(&candidate);

		match self.validator_data.entry(from.clone()) {
			Entry::Occupied(mut occ) => {
				// if digest is different, fetch candidate and
				// note misbehavior.
				let existing = occ.get_mut();

				if let Some((ref old_digest, ref old_sig)) = existing.proposal {
					if old_digest != &digest {
						let old_candidate = self.candidate_votes.get(old_digest)
							.expect("proposed digest implies existence of votes entry; qed")
							.candidate
							.clone();

						return (
							Some(Misbehavior::MultipleCandidates(MultipleCandidates {
								first: (old_candidate, old_sig.clone()),
								second: (candidate, signature.clone()),
							})),
							None,
						);
					}
				} else {
					existing.proposal = Some((digest.clone(), signature.clone()));
				}
			}
			Entry::Vacant(vacant) => {
				vacant.insert(ValidatorData {
					proposal: Some((digest.clone(), signature.clone())),
					known_statements: HashSet::new(),
				});

				// TODO: seed validity votes with issuer here?
				self.candidate_votes.entry(digest.clone()).or_insert_with(move || CandidateData {
					group_id: group,
					candidate: candidate,
					validity_votes: HashMap::new(),
					availability_votes: HashMap::new(),
					indicated_bad_by: Vec::new(),
				});
			}
		}

		self.validity_vote(
			context,
			from,
			digest,
			ValidityVote::Issued(signature),
		)
	}

	fn validity_vote(
		&mut self,
		context: &C,
		from: C::ValidatorId,
		digest: C::Digest,
		vote: ValidityVote<C::Signature>,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let votes = match self.candidate_votes.get_mut(&digest) {
			None => return (None, None), // TODO: queue up but don't get DoS'ed
			Some(votes) => votes,
		};

		// check that this validator actually can vote in this group.
		if !context.is_member_of(&from, &votes.group_id) {
			let (sig, valid) = match vote {
				ValidityVote::Valid(s) => (s, true),
				ValidityVote::Invalid(s) => (s, false),
				ValidityVote::Issued(_) =>
					panic!("implicit issuance vote only cast if the candidate entry already created successfully; qed"),
			};

			return (
				Some(Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
					statement: SignedStatement {
						signature: sig,
						sender: from,
						statement: if valid {
							Statement::Valid(digest)
						} else {
							Statement::Invalid(digest)
						}
					}
				})),
				None,
			);
		}

		// check for double votes.
		match votes.validity_votes.entry(from.clone()) {
			Entry::Occupied(occ) => {
				if occ.get() != &vote {
					let double_vote_proof = match (occ.get().clone(), vote) {
						(ValidityVote::Issued(iss), ValidityVote::Valid(good)) |
						(ValidityVote::Valid(good), ValidityVote::Issued(iss)) =>
							ValidityDoubleVote::IssuedAndValidity((votes.candidate.clone(), iss), (digest, good)),
						(ValidityVote::Issued(iss), ValidityVote::Invalid(bad)) |
						(ValidityVote::Invalid(bad), ValidityVote::Issued(iss)) =>
							ValidityDoubleVote::IssuedAndInvalidity((votes.candidate.clone(), iss), (digest, bad)),
						(ValidityVote::Valid(good), ValidityVote::Invalid(bad)) |
						(ValidityVote::Invalid(bad), ValidityVote::Valid(good)) =>
							ValidityDoubleVote::ValidityAndInvalidity(digest, good, bad),
						_ => {
							// this would occur if two different but valid signatures
							// on the same kind of vote occurred.
							return (None, None);
						}
					};

					return (
						Some(Misbehavior::ValidityDoubleVote(double_vote_proof)),
						None,
					)
				}

				return (None, None);
			}
			Entry::Vacant(vacant) => {
				if let ValidityVote::Invalid(_) = vote {
					votes.indicated_bad_by.push(from);
				}

				vacant.insert(vote);
			}
		}

		(None, Some(votes.summary(digest)))
	}

	fn availability_vote(
		&mut self,
		context: &C,
		from: C::ValidatorId,
		digest: C::Digest,
		signature: C::Signature,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let votes = match self.candidate_votes.get_mut(&digest) {
			None => return (None, None), // TODO: queue up but don't get DoS'ed
			Some(votes) => votes,
		};

		// check that this validator actually can vote in this group.
		if !context.is_availability_guarantor_of(&from, &votes.group_id) {
			return (
				Some(Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
					statement: SignedStatement {
						signature: signature.clone(),
						statement: Statement::Available(digest),
						sender: from,
					}
				})),
				None
			);
		}

		votes.availability_votes.insert(from, signature);
		(None, Some(votes.summary(digest)))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;

	#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
	struct ValidatorId(usize);

	#[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
	struct GroupId(usize);

	// group, body
	#[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
	struct Candidate(usize, usize);

	#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
	struct Signature(usize);

	#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
	struct Digest(usize);

	#[derive(Debug, PartialEq, Eq)]
	struct TestContext {
		// v -> (validity, availability)
		validators: HashMap<ValidatorId, (GroupId, GroupId)>
	}

	impl Context for TestContext {
		type ValidatorId = ValidatorId;
		type Digest = Digest;
		type Candidate = Candidate;
		type GroupId = GroupId;
		type Signature = Signature;

		fn candidate_digest(&self, candidate: &Candidate) -> Digest {
			Digest(candidate.1)
		}

		fn candidate_group(&self, candidate: &Candidate) -> GroupId {
			GroupId(candidate.0)
		}

		fn is_member_of(
			&self,
			validator: &ValidatorId,
			group: &GroupId
		) -> bool {
			self.validators.get(validator).map(|v| &v.0 == group).unwrap_or(false)
		}

		fn is_availability_guarantor_of(
			&self,
			validator: &ValidatorId,
			group: &GroupId
		) -> bool {
			self.validators.get(validator).map(|v| &v.1 == group).unwrap_or(false)
		}

		fn requisite_votes(&self, _id: &GroupId) -> (usize, usize) {
			(6, 34)
		}
	}

	#[test]
	fn submitting_two_candidates_is_misbehavior() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement_a = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};

		let statement_b = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 999)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};

		table.import_statement(&context, statement_a, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));

		table.import_statement(&context, statement_b, None);
		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(1)).unwrap(),
			&Misbehavior::MultipleCandidates(MultipleCandidates {
				first: (Candidate(2, 100), Signature(1)),
				second: (Candidate(2, 999), Signature(1)),
			})
		);
	}

	#[test]
	fn submitting_candidate_from_wrong_group_is_misbehavior() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(3), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};

		table.import_statement(&context, statement, None);

		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(1)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Candidate(Candidate(2, 100)),
					signature: Signature(1),
					sender: ValidatorId(1),
				},
			})
		);
	}

	#[test]
	fn unauthorized_votes() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map.insert(ValidatorId(2), (GroupId(3), GroupId(222)));
				map
			}
		};

		let mut table = create();

		let candidate_a = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		let candidate_a_digest = Digest(100);

		let candidate_b = SignedStatement {
			statement: Statement::Candidate(Candidate(3, 987)),
			signature: Signature(2),
			sender: ValidatorId(2),
		};
		let candidate_b_digest = Digest(987);

		table.import_statement(&context, candidate_a, None);
		table.import_statement(&context, candidate_b, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(2)));

		// validator 1 votes for availability on 2's candidate.
		let bad_availability_vote = SignedStatement {
			statement: Statement::Available(candidate_b_digest.clone()),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		table.import_statement(&context, bad_availability_vote, None);

		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(1)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Available(candidate_b_digest),
					signature: Signature(1),
					sender: ValidatorId(1),
				},
			})
		);

		// validator 2 votes for validity on 1's candidate.
		let bad_validity_vote = SignedStatement {
			statement: Statement::Valid(candidate_a_digest.clone()),
			signature: Signature(2),
			sender: ValidatorId(2),
		};
		table.import_statement(&context, bad_validity_vote, None);

		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(2)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Valid(candidate_a_digest),
					signature: Signature(2),
					sender: ValidatorId(2),
				},
			})
		);
	}

	#[test]
	fn validity_double_vote_is_misbehavior() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map.insert(ValidatorId(2), (GroupId(2), GroupId(246)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));

		let valid_statement = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(2),
			sender: ValidatorId(2),
		};

		let invalid_statement = SignedStatement {
			statement: Statement::Invalid(candidate_digest.clone()),
			signature: Signature(2),
			sender: ValidatorId(2),
		};

		table.import_statement(&context, valid_statement, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(2)));

		table.import_statement(&context, invalid_statement, None);

		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(2)).unwrap(),
			&Misbehavior::ValidityDoubleVote(ValidityDoubleVote::ValidityAndInvalidity(
				candidate_digest,
				Signature(2),
				Signature(2),
			))
		);
	}

	#[test]
	fn issue_and_vote_is_misbehavior() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));

		let extra_vote = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(1),
			sender: ValidatorId(1),
		};

		table.import_statement(&context, extra_vote, None);
		assert_eq!(
			table.detected_misbehavior.get(&ValidatorId(1)).unwrap(),
			&Misbehavior::ValidityDoubleVote(ValidityDoubleVote::IssuedAndValidity(
				(Candidate(2, 100), Signature(1)),
				(Digest(100), Signature(1)),
			))
		);
	}

	#[test]
	fn candidate_can_be_included() {
		let validity_threshold = 6;
		let availability_threshold = 34;

		let mut candidate = CandidateData::<TestContext> {
			group_id: GroupId(4),
			candidate: Candidate(4, 12345),
			validity_votes: HashMap::new(),
			availability_votes: HashMap::new(),
			indicated_bad_by: Vec::new(),
		};

		assert!(!candidate.can_be_included(validity_threshold, availability_threshold));

		for i in 0..validity_threshold {
			candidate.validity_votes.insert(ValidatorId(i + 100), ValidityVote::Valid(Signature(i + 100)));
		}

		assert!(!candidate.can_be_included(validity_threshold, availability_threshold));

		for i in 0..availability_threshold {
			candidate.availability_votes.insert(ValidatorId(i + 255), Signature(i + 255));
		}

		assert!(candidate.can_be_included(validity_threshold, availability_threshold));

		candidate.indicated_bad_by.push(ValidatorId(1024));

		assert!(!candidate.can_be_included(validity_threshold, availability_threshold));
	}

	#[test]
	fn candidate_import_gives_summary() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};

		let summary = table.import_statement(&context, statement, None)
			.expect("candidate import to give summary");

		assert_eq!(summary.candidate, Digest(100));
		assert_eq!(summary.group_id, GroupId(2));
		assert_eq!(summary.validity_votes, 1);
		assert_eq!(summary.availability_votes, 0);
	}

	#[test]
	fn candidate_vote_gives_summary() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map.insert(ValidatorId(2), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));

		let vote = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(2),
			sender: ValidatorId(2),
		};

		let summary = table.import_statement(&context, vote, None)
			.expect("candidate vote to give summary");

		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(2)));

		assert_eq!(summary.candidate, Digest(100));
		assert_eq!(summary.group_id, GroupId(2));
		assert_eq!(summary.validity_votes, 2);
		assert_eq!(summary.availability_votes, 0);
	}

	#[test]
	fn availability_vote_gives_summary() {
		let context = TestContext {
			validators: {
				let mut map = HashMap::new();
				map.insert(ValidatorId(1), (GroupId(2), GroupId(455)));
				map.insert(ValidatorId(2), (GroupId(5), GroupId(2)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: ValidatorId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(1)));

		let vote = SignedStatement {
			statement: Statement::Available(candidate_digest.clone()),
			signature: Signature(2),
			sender: ValidatorId(2),
		};

		let summary = table.import_statement(&context, vote, None)
			.expect("candidate vote to give summary");

		assert!(!table.detected_misbehavior.contains_key(&ValidatorId(2)));

		assert_eq!(summary.candidate, Digest(100));
		assert_eq!(summary.group_id, GroupId(2));
		assert_eq!(summary.validity_votes, 1);
		assert_eq!(summary.availability_votes, 1);
	}
}
