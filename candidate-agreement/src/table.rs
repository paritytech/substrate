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
//! This stores messages other authorities issue about candidates.
//!
//! These messages are used to create a proposal submitted to a BFT consensus process.
//!
//! Proposals are formed of sets of candidates which have the requisite number of
//! validity and availability votes.
//!
//! Each parachain is associated with two sets of authorities: those which can
//! propose and attest to validity of candidates, and those who can only attest
//! to availability.

use std::collections::HashSet;
use std::collections::hash_map::{HashMap, Entry};
use std::hash::Hash;
use std::fmt::Debug;

use super::StatementBatch;

/// Context for the statement table.
pub trait Context {
	/// A authority ID
	type AuthorityId: Debug + Hash + Eq + Clone;
	/// The digest (hash or other unique attribute) of a candidate.
	type Digest: Debug + Hash + Eq + Clone;
	/// The group ID type
	type GroupId: Debug + Hash + Ord + Eq + Clone;
	/// A signature type.
	type Signature: Debug + Eq + Clone;
	/// Candidate type. In practice this will be a candidate receipt.
	type Candidate: Debug + Ord + Eq + Clone;

	/// get the digest of a candidate.
	fn candidate_digest(candidate: &Self::Candidate) -> Self::Digest;

	/// get the group of a candidate.
	fn candidate_group(candidate: &Self::Candidate) -> Self::GroupId;

	/// Whether a authority is a member of a group.
	/// Members are meant to submit candidates and vote on validity.
	fn is_member_of(&self, authority: &Self::AuthorityId, group: &Self::GroupId) -> bool;

	/// Whether a authority is an availability guarantor of a group.
	/// Guarantors are meant to vote on availability for candidates submitted
	/// in a group.
	fn is_availability_guarantor_of(
		&self,
		authority: &Self::AuthorityId,
		group: &Self::GroupId,
	) -> bool;

	// requisite number of votes for validity and availability respectively from a group.
	fn requisite_votes(&self, group: &Self::GroupId) -> (usize, usize);
}

/// Statements circulated among peers.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Statement<C, D> {
	/// Broadcast by a authority to indicate that this is his candidate for
	/// inclusion.
	///
	/// Broadcasting two different candidate messages per round is not allowed.
	Candidate(C),
	/// Broadcast by a authority to attest that the candidate with given digest
	/// is valid.
	Valid(D),
	/// Broadcast by a authority to attest that the auxiliary data for a candidate
	/// with given digest is available.
	Available(D),
	/// Broadcast by a authority to attest that the candidate with given digest
	/// is invalid.
	Invalid(D),
}

/// A signed statement.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct SignedStatement<C, D, V, S> {
	/// The statement.
	pub statement: Statement<C, D>,
	/// The signature.
	pub signature: S,
	/// The sender.
	pub sender: V,
}

// A unique trace for a class of valid statements issued by a authority.
//
// We keep track of which statements we have received or sent to other authorities
// in order to prevent relaying the same data multiple times.
//
// The signature of the statement is replaced by the authority because the authority
// is unique while signatures are not (at least under common schemes like
// Schnorr or ECDSA).
#[derive(Hash, PartialEq, Eq, Clone)]
enum StatementTrace<V, D> {
	/// The candidate proposed by the authority.
	Candidate(V),
	/// A validity statement from that authority about the given digest.
	Valid(V, D),
	/// An invalidity statement from that authority about the given digest.
	Invalid(V, D),
	/// An availability statement from that authority about the given digest.
	Available(V, D),
}

/// Misbehavior: voting more than one way on candidate validity.
///
/// Since there are three possible ways to vote, a double vote is possible in
/// three possible combinations (unordered)
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ValidityDoubleVote<C, D, S> {
	/// Implicit vote by issuing and explicity voting validity.
	IssuedAndValidity((C, S), (D, S)),
	/// Implicit vote by issuing and explicitly voting invalidity
	IssuedAndInvalidity((C, S), (D, S)),
	/// Direct votes for validity and invalidity
	ValidityAndInvalidity(D, S, S),
}

/// Misbehavior: declaring multiple candidates.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct MultipleCandidates<C, S> {
	/// The first candidate seen.
	pub first: (C, S),
	/// The second candidate seen.
	pub second: (C, S),
}

/// Misbehavior: submitted statement for wrong group.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct UnauthorizedStatement<C, D, V, S> {
	/// A signed statement which was submitted without proper authority.
	pub statement: SignedStatement<C, D, V, S>,
}

/// Different kinds of misbehavior. All of these kinds of malicious misbehavior
/// are easily provable and extremely disincentivized.
#[derive(PartialEq, Eq, Debug, Clone)]
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
	type Misbehavior = Misbehavior<C::Candidate, C::Digest, C::AuthorityId, C::Signature>;
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
	validity_votes: HashMap<C::AuthorityId, ValidityVote<C::Signature>>,
	availability_votes: HashMap<C::AuthorityId, C::Signature>,
	indicated_bad_by: Vec<C::AuthorityId>,
}

impl<C: Context> CandidateData<C> {
	/// whether this has been indicated bad by anyone.
	pub fn indicated_bad(&self) -> bool {
		!self.indicated_bad_by.is_empty()
	}

	// Candidate data can be included in a proposal
	// if it has enough validity and availability votes
	// and no authorities have called it bad.
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

// authority metadata
struct AuthorityData<C: Context> {
	proposal: Option<(C::Digest, C::Signature)>,
	known_statements: HashSet<StatementTrace<C::AuthorityId, C::Digest>>,
}

impl<C: Context> Default for AuthorityData<C> {
	fn default() -> Self {
		AuthorityData {
			proposal: None,
			known_statements: HashSet::default(),
		}
	}
}

/// Stores votes
pub struct Table<C: Context> {
	authority_data: HashMap<C::AuthorityId, AuthorityData<C>>,
	detected_misbehavior: HashMap<C::AuthorityId, <C as ResolveMisbehavior>::Misbehavior>,
	candidate_votes: HashMap<C::Digest, CandidateData<C>>,
}

impl<C: Context> Default for Table<C> {
	fn default() -> Self {
		Table {
			authority_data: HashMap::new(),
			detected_misbehavior: HashMap::new(),
			candidate_votes: HashMap::new(),
		}
	}
}

impl<C: Context> Table<C> {
	/// Produce a set of proposed candidates.
	///
	/// This will be at most one per group, consisting of the
	/// best candidate for each group with requisite votes for inclusion.
	///
	/// The vector is sorted in ascending order by group id.
	pub fn proposed_candidates<'a>(&'a self, context: &C) -> Vec<&'a C::Candidate> {
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
					if *candidate_ref > candidate {
						*candidate_ref = candidate;
					}
				}
				BTreeEntry::Vacant(vacant) => { vacant.insert(candidate); },
			}
		}

		best_candidates.values().cloned().collect::<Vec<_>>()
	}

	/// Whether a candidate can be included.
	pub fn candidate_includable(&self, digest: &C::Digest, context: &C) -> bool {
		self.candidate_votes.get(digest).map_or(false, |data| {
			let (v_threshold, a_threshold) = context.requisite_votes(&data.group_id);
			data.can_be_included(v_threshold, a_threshold)
		})
	}

	/// Import a signed statement. Signatures should be checked for validity, and the
	/// sender should be checked to actually be a authority.
	///
	/// This can note the origin of the statement to indicate that he has
	/// seen it already.
	pub fn import_statement(
		&mut self,
		context: &C,
		statement: SignedStatement<C::Candidate, C::Digest, C::AuthorityId, C::Signature>,
		from: Option<C::AuthorityId>
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
			),
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

	/// Get a candidate by digest.
	pub fn get_candidate(&self, digest: &C::Digest) -> Option<&C::Candidate> {
		self.candidate_votes.get(digest).map(|d| &d.candidate)
	}

	/// Access all witnessed misbehavior.
	pub fn get_misbehavior(&self)
		-> &HashMap<C::AuthorityId, <C as ResolveMisbehavior>::Misbehavior>
	{
		&self.detected_misbehavior
	}

	/// Fill a statement batch and note messages seen by the targets.
	pub fn fill_batch<B>(&mut self, batch: &mut B)
		where B: StatementBatch<
			C::AuthorityId,
			SignedStatement<C::Candidate, C::Digest, C::AuthorityId, C::Signature>,
		>
	{
		// naively iterate all statements so far, taking any that
		// at least one of the targets has not seen.

		// workaround for the fact that it's inconvenient to borrow multiple
		// entries out of a hashmap mutably -- we just move them out and
		// replace them when we're done.
		struct SwappedTargetData<'a, C: 'a + Context> {
			authority_data: &'a mut HashMap<C::AuthorityId, AuthorityData<C>>,
			target_data: Vec<(C::AuthorityId, AuthorityData<C>)>,
		}

		impl<'a, C: 'a + Context> Drop for SwappedTargetData<'a, C> {
			fn drop(&mut self) {
				for (id, data) in self.target_data.drain(..) {
					self.authority_data.insert(id, data);
				}
			}
		}

		// pre-fetch authority data for all the targets.
		let mut target_data = {
			let authority_data = &mut self.authority_data;
			let mut target_data = Vec::with_capacity(batch.targets().len());
			for target in batch.targets() {
				let active_data = match authority_data.get_mut(target) {
					None => Default::default(),
					Some(x) => ::std::mem::replace(x, Default::default()),
				};

				target_data.push((target.clone(), active_data));
			}

			SwappedTargetData {
				authority_data,
				target_data
			}
		};

		let target_data = &mut target_data.target_data;

		macro_rules! attempt_send {
			($trace:expr, sender=$sender:expr, sig=$sig:expr, statement=$statement:expr) => {{
				let trace = $trace;
				let can_send = target_data.iter()
					.any(|t| !t.1.known_statements.contains(&trace));

				if can_send {
					let statement = SignedStatement {
						statement: $statement,
						signature: $sig,
						sender: $sender,
					};

					if batch.push(statement) {
						for target in target_data.iter_mut() {
							target.1.known_statements.insert(trace.clone());
						}
					} else {
						return;
					}
				}
			}}
		}

		// reconstruct statements for anything whose trace passes the filter.
		for (digest, candidate) in self.candidate_votes.iter() {
			let issuance_iter = candidate.validity_votes.iter()
				.filter(|&(_, x)| if let ValidityVote::Issued(_) = *x { true } else { false });

			let validity_iter = candidate.validity_votes.iter()
				.filter(|&(_, x)| if let ValidityVote::Issued(_) = *x { false } else { true });

			// send issuance statements before votes.
			for (sender, vote) in issuance_iter.chain(validity_iter) {
				match *vote {
					ValidityVote::Issued(ref sig) => {
						attempt_send!(
							StatementTrace::Candidate(sender.clone()),
							sender = sender.clone(),
							sig = sig.clone(),
							statement = Statement::Candidate(candidate.candidate.clone())
						)
					}
					ValidityVote::Valid(ref sig) => {
						attempt_send!(
							StatementTrace::Valid(sender.clone(), digest.clone()),
							sender = sender.clone(),
							sig = sig.clone(),
							statement = Statement::Valid(digest.clone())
						)
					}
					ValidityVote::Invalid(ref sig) => {
						attempt_send!(
							StatementTrace::Invalid(sender.clone(), digest.clone()),
							sender = sender.clone(),
							sig = sig.clone(),
							statement = Statement::Invalid(digest.clone())
						)
					}
				}
			};


			// and lastly send availability.
			for (sender, sig) in candidate.availability_votes.iter() {
				attempt_send!(
					StatementTrace::Available(sender.clone(), digest.clone()),
					sender = sender.clone(),
					sig = sig.clone(),
					statement = Statement::Available(digest.clone())
				)
			}
		}

	}

	fn note_trace_seen(&mut self, trace: StatementTrace<C::AuthorityId, C::Digest>, known_by: C::AuthorityId) {
		self.authority_data.entry(known_by).or_insert_with(|| AuthorityData {
			proposal: None,
			known_statements: HashSet::default(),
		}).known_statements.insert(trace);
	}

	fn import_candidate(
		&mut self,
		context: &C,
		from: C::AuthorityId,
		candidate: C::Candidate,
		signature: C::Signature,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let group = C::candidate_group(&candidate);
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

		// check that authority hasn't already specified another candidate.
		let digest = C::candidate_digest(&candidate);

		let new_proposal = match self.authority_data.entry(from.clone()) {
			Entry::Occupied(mut occ) => {
				// if digest is different, fetch candidate and
				// note misbehavior.
				let existing = occ.get_mut();

				if let Some((ref old_digest, ref old_sig)) = existing.proposal {
					if old_digest != &digest {
						const EXISTENCE_PROOF: &str =
							"when proposal first received from authority, candidate \
							votes entry is created. proposal here is `Some`, therefore \
							candidate votes entry exists; qed";

						let old_candidate = self.candidate_votes.get(old_digest)
							.expect(EXISTENCE_PROOF)
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

					false
				} else {
					existing.proposal = Some((digest.clone(), signature.clone()));
					true
				}
			}
			Entry::Vacant(vacant) => {
				vacant.insert(AuthorityData {
					proposal: Some((digest.clone(), signature.clone())),
					known_statements: HashSet::new(),
				});
				true
			}
		};

		// NOTE: altering this code may affect the existence proof above. ensure it remains
		// valid.
		if new_proposal {
			self.candidate_votes.entry(digest.clone()).or_insert_with(move || CandidateData {
				group_id: group,
				candidate: candidate,
				validity_votes: HashMap::new(),
				availability_votes: HashMap::new(),
				indicated_bad_by: Vec::new(),
			});
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
		from: C::AuthorityId,
		digest: C::Digest,
		vote: ValidityVote<C::Signature>,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let votes = match self.candidate_votes.get_mut(&digest) {
			None => return (None, None), // TODO: queue up but don't get DoS'ed
			Some(votes) => votes,
		};

		// check that this authority actually can vote in this group.
		if !context.is_member_of(&from, &votes.group_id) {
			let (sig, valid) = match vote {
				ValidityVote::Valid(s) => (s, true),
				ValidityVote::Invalid(s) => (s, false),
				ValidityVote::Issued(_) =>
					panic!("implicit issuance vote only cast from `import_candidate` after \
							checking group membership of issuer; qed"),
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
		from: C::AuthorityId,
		digest: C::Digest,
		signature: C::Signature,
	) -> (Option<<C as ResolveMisbehavior>::Misbehavior>, Option<Summary<C::Digest, C::GroupId>>) {
		let votes = match self.candidate_votes.get_mut(&digest) {
			None => return (None, None), // TODO: queue up but don't get DoS'ed
			Some(votes) => votes,
		};

		// check that this authority actually can vote in this group.
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
	use ::tests::VecBatch;
	use std::collections::HashMap;

	fn create<C: Context>() -> Table<C> {
		Table {
			authority_data: HashMap::default(),
			detected_misbehavior: HashMap::default(),
			candidate_votes: HashMap::default(),
		}
	}

	#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
	struct AuthorityId(usize);

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
		authorities: HashMap<AuthorityId, (GroupId, GroupId)>
	}

	impl Context for TestContext {
		type AuthorityId = AuthorityId;
		type Digest = Digest;
		type Candidate = Candidate;
		type GroupId = GroupId;
		type Signature = Signature;

		fn candidate_digest(candidate: &Candidate) -> Digest {
			Digest(candidate.1)
		}

		fn candidate_group(candidate: &Candidate) -> GroupId {
			GroupId(candidate.0)
		}

		fn is_member_of(
			&self,
			authority: &AuthorityId,
			group: &GroupId
		) -> bool {
			self.authorities.get(authority).map(|v| &v.0 == group).unwrap_or(false)
		}

		fn is_availability_guarantor_of(
			&self,
			authority: &AuthorityId,
			group: &GroupId
		) -> bool {
			self.authorities.get(authority).map(|v| &v.1 == group).unwrap_or(false)
		}

		fn requisite_votes(&self, _id: &GroupId) -> (usize, usize) {
			(6, 34)
		}
	}

	#[test]
	fn submitting_two_candidates_is_misbehavior() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement_a = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};

		let statement_b = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 999)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};

		table.import_statement(&context, statement_a, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));

		table.import_statement(&context, statement_b, None);
		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(1)).unwrap(),
			&Misbehavior::MultipleCandidates(MultipleCandidates {
				first: (Candidate(2, 100), Signature(1)),
				second: (Candidate(2, 999), Signature(1)),
			})
		);
	}

	#[test]
	fn submitting_candidate_from_wrong_group_is_misbehavior() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(3), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};

		table.import_statement(&context, statement, None);

		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(1)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Candidate(Candidate(2, 100)),
					signature: Signature(1),
					sender: AuthorityId(1),
				},
			})
		);
	}

	#[test]
	fn unauthorized_votes() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map.insert(AuthorityId(2), (GroupId(3), GroupId(222)));
				map
			}
		};

		let mut table = create();

		let candidate_a = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		let candidate_a_digest = Digest(100);

		let candidate_b = SignedStatement {
			statement: Statement::Candidate(Candidate(3, 987)),
			signature: Signature(2),
			sender: AuthorityId(2),
		};
		let candidate_b_digest = Digest(987);

		table.import_statement(&context, candidate_a, None);
		table.import_statement(&context, candidate_b, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(2)));

		// authority 1 votes for availability on 2's candidate.
		let bad_availability_vote = SignedStatement {
			statement: Statement::Available(candidate_b_digest.clone()),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		table.import_statement(&context, bad_availability_vote, None);

		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(1)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Available(candidate_b_digest),
					signature: Signature(1),
					sender: AuthorityId(1),
				},
			})
		);

		// authority 2 votes for validity on 1's candidate.
		let bad_validity_vote = SignedStatement {
			statement: Statement::Valid(candidate_a_digest.clone()),
			signature: Signature(2),
			sender: AuthorityId(2),
		};
		table.import_statement(&context, bad_validity_vote, None);

		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(2)).unwrap(),
			&Misbehavior::UnauthorizedStatement(UnauthorizedStatement {
				statement: SignedStatement {
					statement: Statement::Valid(candidate_a_digest),
					signature: Signature(2),
					sender: AuthorityId(2),
				},
			})
		);
	}

	#[test]
	fn validity_double_vote_is_misbehavior() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map.insert(AuthorityId(2), (GroupId(2), GroupId(246)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));

		let valid_statement = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(2),
			sender: AuthorityId(2),
		};

		let invalid_statement = SignedStatement {
			statement: Statement::Invalid(candidate_digest.clone()),
			signature: Signature(2),
			sender: AuthorityId(2),
		};

		table.import_statement(&context, valid_statement, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(2)));

		table.import_statement(&context, invalid_statement, None);

		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(2)).unwrap(),
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
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));

		let extra_vote = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(1),
			sender: AuthorityId(1),
		};

		table.import_statement(&context, extra_vote, None);
		assert_eq!(
			table.detected_misbehavior.get(&AuthorityId(1)).unwrap(),
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
			candidate.validity_votes.insert(AuthorityId(i + 100), ValidityVote::Valid(Signature(i + 100)));
		}

		assert!(!candidate.can_be_included(validity_threshold, availability_threshold));

		for i in 0..availability_threshold {
			candidate.availability_votes.insert(AuthorityId(i + 255), Signature(i + 255));
		}

		assert!(candidate.can_be_included(validity_threshold, availability_threshold));

		candidate.indicated_bad_by.push(AuthorityId(1024));

		assert!(!candidate.can_be_included(validity_threshold, availability_threshold));
	}

	#[test]
	fn candidate_import_gives_summary() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
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
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map.insert(AuthorityId(2), (GroupId(2), GroupId(455)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));

		let vote = SignedStatement {
			statement: Statement::Valid(candidate_digest.clone()),
			signature: Signature(2),
			sender: AuthorityId(2),
		};

		let summary = table.import_statement(&context, vote, None)
			.expect("candidate vote to give summary");

		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(2)));

		assert_eq!(summary.candidate, Digest(100));
		assert_eq!(summary.group_id, GroupId(2));
		assert_eq!(summary.validity_votes, 2);
		assert_eq!(summary.availability_votes, 0);
	}

	#[test]
	fn availability_vote_gives_summary() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				map.insert(AuthorityId(1), (GroupId(2), GroupId(455)));
				map.insert(AuthorityId(2), (GroupId(5), GroupId(2)));
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};
		let candidate_digest = Digest(100);

		table.import_statement(&context, statement, None);
		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(1)));

		let vote = SignedStatement {
			statement: Statement::Available(candidate_digest.clone()),
			signature: Signature(2),
			sender: AuthorityId(2),
		};

		let summary = table.import_statement(&context, vote, None)
			.expect("candidate vote to give summary");

		assert!(!table.detected_misbehavior.contains_key(&AuthorityId(2)));

		assert_eq!(summary.candidate, Digest(100));
		assert_eq!(summary.group_id, GroupId(2));
		assert_eq!(summary.validity_votes, 1);
		assert_eq!(summary.availability_votes, 1);
	}

	#[test]
	fn filling_batch_sets_known_flag() {
		let context = TestContext {
			authorities: {
				let mut map = HashMap::new();
				for i in 1..10 {
					map.insert(AuthorityId(i), (GroupId(2), GroupId(400 + i)));
				}
				map
			}
		};

		let mut table = create();
		let statement = SignedStatement {
			statement: Statement::Candidate(Candidate(2, 100)),
			signature: Signature(1),
			sender: AuthorityId(1),
		};

		table.import_statement(&context, statement, None);

		for i in 2..10 {
			let statement = SignedStatement {
				statement: Statement::Valid(Digest(100)),
				signature: Signature(i),
				sender: AuthorityId(i),
			};

			table.import_statement(&context, statement, None);
		}

		let mut batch = VecBatch {
			max_len: 5,
			targets: (1..10).map(AuthorityId).collect(),
			items: Vec::new(),
		};

		// 9 statements in the table, each seen by one.
		table.fill_batch(&mut batch);
		assert_eq!(batch.items.len(), 5);

		// 9 statements in the table, 5 of which seen by all targets.
		batch.items.clear();
		table.fill_batch(&mut batch);
		assert_eq!(batch.items.len(), 4);

		batch.items.clear();
		table.fill_batch(&mut batch);
		assert!(batch.items.is_empty());
	}
}
