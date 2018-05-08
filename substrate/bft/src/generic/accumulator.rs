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

//! Vote accumulator for each round of BFT consensus.

use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use generic::{Vote, LocalizedMessage, LocalizedProposal};

/// Justification for some state at a given round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncheckedJustification<D, S> {
	/// The round.
	pub round_number: usize,
	/// The digest prepared for.
	pub digest: D,
	/// Signatures for the prepare messages.
	pub signatures: Vec<S>,
}

impl<D, S> UncheckedJustification<D, S> {
	/// Fails if there are duplicate signatures or invalid.
	///
	/// Provide a closure for checking whether the signature is valid on a
	/// digest.
	///
	/// The closure should returns a checked justification iff the round number, digest, and signature
	/// represent a valid message and the signer was authorized to issue
	/// it.
	///
	/// The `check_message` closure may vary based on context.
	pub fn check<F, V>(self, threshold: usize, mut check_message: F)
		-> Result<Justification<D, S>, Self>
		where
			F: FnMut(usize, &D, &S) -> Option<V>,
			V: Hash + Eq,
	{
		let checks_out = {
			let mut checks_out = || {
				let mut voted = HashSet::new();

				for signature in &self.signatures {
					match check_message(self.round_number, &self.digest, signature) {
						None => return false,
						Some(v) => {
							if !voted.insert(v) {
								return false;
							}
						}
					}
				}

				voted.len() >= threshold
			};

			checks_out()
		};

		if checks_out {
			Ok(Justification(self))
		} else {
			Err(self)
		}
	}
}

/// A checked justification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Justification<D,S>(UncheckedJustification<D,S>);

impl<D, S> Justification<D, S> {
	/// Convert this justification back to unchecked.
	pub fn uncheck(self) -> UncheckedJustification<D, S> {
		self.0
	}
}

impl<D, S> ::std::ops::Deref for Justification<D, S> {
	type Target = UncheckedJustification<D, S>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

/// Type alias to represent a justification specifically for a prepare.
pub type PrepareJustification<D, S> = Justification<D, S>;

/// The round's state, based on imported messages.
#[derive(PartialEq, Eq, Debug)]
pub enum State<Candidate, Digest, Signature> {
	/// No proposal yet.
	Begin,
	/// Proposal received.
	Proposed(Candidate),
	/// Seen n - f prepares for this digest.
	Prepared(PrepareJustification<Digest, Signature>),
	/// Seen n - f commits for a digest.
	Committed(Justification<Digest, Signature>),
	/// Seen n - f round-advancement messages.
	Advanced(Option<PrepareJustification<Digest, Signature>>),
}

#[derive(Debug, Default)]
struct VoteCounts {
	prepared: usize,
	committed: usize,
}

#[derive(Debug)]
struct Proposal<Candidate, Digest, Signature> {
	proposal: Candidate,
	digest: Digest,
	digest_signature: Signature,
}

/// Misbehavior which can occur.
#[derive(Debug, Clone)]
pub enum Misbehavior<Digest, Signature> {
	/// Proposed out-of-turn.
	ProposeOutOfTurn(usize, Digest, Signature),
	/// Issued two conflicting proposals.
	DoublePropose(usize, (Digest, Signature), (Digest, Signature)),
	/// Issued two conflicting prepare messages.
	DoublePrepare(usize, (Digest, Signature), (Digest, Signature)),
	/// Issued two conflicting commit messages.
	DoubleCommit(usize, (Digest, Signature), (Digest, Signature)),
}

/// Accumulates messages for a given round of BFT consensus.
///
/// This isn't tied to the "view" of a single authority. It
/// keeps accurate track of the state of the BFT consensus based
/// on all messages imported.
#[derive(Debug)]
pub struct Accumulator<Candidate, Digest, AuthorityId, Signature>
	where
	Candidate: Eq + Clone,
	Digest: Hash + Eq + Clone,
	AuthorityId: Hash + Eq + Clone,
	Signature: Eq + Clone,
{
	round_number: usize,
	threshold: usize,
	round_proposer: AuthorityId,
	proposal: Option<Proposal<Candidate, Digest, Signature>>,
	prepares: HashMap<AuthorityId, (Digest, Signature)>,
	commits: HashMap<AuthorityId, (Digest, Signature)>,
	vote_counts: HashMap<Digest, VoteCounts>,
	advance_round: HashSet<AuthorityId>,
	state: State<Candidate, Digest, Signature>,
}

impl<Candidate, Digest, AuthorityId, Signature> Accumulator<Candidate, Digest, AuthorityId, Signature>
	where
	Candidate: Eq + Clone,
	Digest: Hash + Eq + Clone,
	AuthorityId: Hash + Eq + Clone,
	Signature: Eq + Clone,
{
	/// Create a new state accumulator.
	pub fn new(round_number: usize, threshold: usize, round_proposer: AuthorityId) -> Self {
		Accumulator {
			round_number,
			threshold,
			round_proposer,
			proposal: None,
			prepares: HashMap::new(),
			commits: HashMap::new(),
			vote_counts: HashMap::new(),
			advance_round: HashSet::new(),
			state: State::Begin,
		}
	}

	/// How advance votes we have seen.
	pub fn advance_votes(&self) -> usize {
		self.advance_round.len()
	}

	/// Get the round number.
	pub fn round_number(&self) -> usize {
		self.round_number.clone()
	}

	pub fn proposal(&self) -> Option<&Candidate> {
		self.proposal.as_ref().map(|p| &p.proposal)
	}

	/// Inspect the current consensus state.
	pub fn state(&self) -> &State<Candidate, Digest, Signature> {
		&self.state
	}

	/// Import a message. Importing duplicates is fine, but the signature
	/// and authorization should have already been checked.
	pub fn import_message(
		&mut self,
		message: LocalizedMessage<Candidate, Digest, AuthorityId, Signature>,
	) -> Result<(), Misbehavior<Digest, Signature>> {
		// message from different round.
		if message.round_number() != self.round_number {
			return Ok(());
		}

		match message {
			LocalizedMessage::Propose(proposal) => self.import_proposal(proposal),
			LocalizedMessage::Vote(vote) => {
				let (sender, signature) = (vote.sender, vote.signature);
				match vote.vote {
					Vote::Prepare(_, d) => self.import_prepare(d, sender, signature),
					Vote::Commit(_, d) => self.import_commit(d, sender, signature),
					Vote::AdvanceRound(_) => self.import_advance_round(sender),
				}
			}
		}
	}

	fn import_proposal(
		&mut self,
		proposal: LocalizedProposal<Candidate, Digest, AuthorityId, Signature>,
	) -> Result<(), Misbehavior<Digest, Signature>> {
		let sender = proposal.sender;

		if sender != self.round_proposer {
			return Err(Misbehavior::ProposeOutOfTurn(
				self.round_number,
				proposal.digest,
				proposal.digest_signature)
			);
		}

		match self.proposal {
			Some(ref p) if &p.digest != &proposal.digest => {
				return Err(Misbehavior::DoublePropose(
					self.round_number,
					{
						let old = self.proposal.as_ref().expect("just checked to be Some; qed");
						(old.digest.clone(), old.digest_signature.clone())
					},
					(proposal.digest.clone(), proposal.digest_signature.clone())
				))
			}
			_ => {},
		}

		self.proposal = Some(Proposal {
			proposal: proposal.proposal.clone(),
			digest: proposal.digest,
			digest_signature: proposal.digest_signature,
		});

		self.state = State::Proposed(proposal.proposal);
		Ok(())
	}

	fn import_prepare(
		&mut self,
		digest: Digest,
		sender: AuthorityId,
		signature: Signature,
	) -> Result<(), Misbehavior<Digest, Signature>> {
		// ignore any subsequent prepares by the same sender.
		let threshold_prepared = match self.prepares.entry(sender.clone()) {
			Entry::Vacant(vacant) => {
				vacant.insert((digest.clone(), signature));
				let count = self.vote_counts.entry(digest.clone()).or_insert_with(Default::default);
				count.prepared += 1;

				if count.prepared >= self.threshold {
					Some(digest)
				} else {
					None
				}
			}
			Entry::Occupied(occupied) => {
				// if digest is different, that's misbehavior.
				if occupied.get().0 != digest {
					return Err(Misbehavior::DoublePrepare(
						self.round_number,
						occupied.get().clone(),
						(digest, signature)
					));
				}

				None
			}
		};

		// only allow transition to prepare from begin or proposed state.
		let valid_transition = match self.state {
			State::Begin | State::Proposed(_) => true,
			_ => false,
		};

		if let (true, Some(threshold_prepared)) = (valid_transition, threshold_prepared) {
			let signatures = self.prepares
				.values()
				.filter(|&&(ref d, _)| d == &threshold_prepared)
				.map(|&(_, ref s)| s.clone())
				.collect();

			self.state = State::Prepared(Justification(UncheckedJustification {
				round_number: self.round_number,
				digest: threshold_prepared,
				signatures: signatures,
			}));
		}

		Ok(())
	}

	fn import_commit(
		&mut self,
		digest: Digest,
		sender: AuthorityId,
		signature: Signature,
	) -> Result<(), Misbehavior<Digest, Signature>> {
		// ignore any subsequent commits by the same sender.
		let threshold_committed = match self.commits.entry(sender.clone()) {
			Entry::Vacant(vacant) => {
				vacant.insert((digest.clone(), signature));
				let count = self.vote_counts.entry(digest.clone()).or_insert_with(Default::default);
				count.committed += 1;

				if count.committed >= self.threshold {
					trace!(target: "bft", "observed threshold-commit for round {} with {} commits", self.round_number, count.committed);
					Some(digest)
				} else {
					None
				}
			}
			Entry::Occupied(occupied) => {
				// if digest is different, that's misbehavior.
				if occupied.get().0 != digest {
					return Err(Misbehavior::DoubleCommit(
						self.round_number,
						occupied.get().clone(),
						(digest, signature)
					));
				}

				None
			}
		};

		// transition to concluded state always valid.
		// only weird case is if the prior state was "advanced",
		// but technically it's the same behavior as if the order of receiving
		// the last "advance round" and "commit" messages were reversed.
		if let Some(threshold_committed) = threshold_committed {
			let signatures = self.commits
				.values()
				.filter(|&&(ref d, _)| d == &threshold_committed)
				.map(|&(_, ref s)| s.clone())
				.collect();

			self.state = State::Committed(Justification(UncheckedJustification {
				round_number: self.round_number,
				digest: threshold_committed,
				signatures: signatures,
			}));
		}

		Ok(())
	}

	fn import_advance_round(
		&mut self,
		sender: AuthorityId,
	) -> Result<(), Misbehavior<Digest, Signature>> {
		self.advance_round.insert(sender);

		if self.advance_round.len() < self.threshold { return Ok(()) }

		// allow transition to new round only if we haven't produced a justification
		// yet.
		self.state = match ::std::mem::replace(&mut self.state, State::Begin) {
			State::Committed(j) => State::Committed(j),
			State::Prepared(j) => State::Advanced(Some(j)),
			State::Advanced(j) => State::Advanced(j),
			State::Begin | State::Proposed(_) => State::Advanced(None),
		};

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use generic::{LocalizedMessage, LocalizedProposal, LocalizedVote};

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Candidate(usize);

	#[derive(Hash, PartialEq, Eq, Clone, Debug)]
	pub struct Digest(usize);

	#[derive(Hash, PartialEq, Eq, Debug, Clone)]
	pub struct AuthorityId(usize);

	#[derive(PartialEq, Eq, Clone, Debug)]
	pub struct Signature(usize, usize);

	#[test]
	fn justification_checks_out() {
		let mut justification = UncheckedJustification {
			round_number: 2,
			digest: Digest(600),
			signatures: (0..10).map(|i| Signature(600, i)).collect(),
		};

		let check_message = |r, d: &Digest, s: &Signature| {
			if r == 2 && d.0 == 600 && s.0 == 600 {
				Some(AuthorityId(s.1))
			} else {
				None
			}
		};

		assert!(justification.clone().check(7, &check_message).is_ok());
		assert!(justification.clone().check(11, &check_message).is_err());

		{
			// one bad signature is enough to spoil it.
			justification.signatures.push(Signature(1001, 255));
			assert!(justification.clone().check(7, &check_message).is_err());

			justification.signatures.pop();
		}
		// duplicates not allowed.
		justification.signatures.extend((0..10).map(|i| Signature(600, i)));
		assert!(justification.clone().check(11, &check_message).is_err());
	}

	#[test]
	fn accepts_proposal_from_proposer_only() {
		let mut accumulator = Accumulator::<_, Digest, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		let res = accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(5),
			full_signature: Signature(999, 5),
			digest_signature: Signature(999, 5),
			proposal: Candidate(999),
			digest: Digest(999),
			round_number: 1,
		}));

		assert!(res.is_err());

		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(999, 8),
			digest_signature: Signature(999, 8),
			proposal: Candidate(999),
			digest: Digest(999),
			round_number: 1,
		})).unwrap();

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
	}

	#[test]
	fn reaches_prepare_phase() {
		let mut accumulator = Accumulator::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(999, 8),
			digest_signature: Signature(999, 8),
			round_number: 1,
			proposal: Candidate(999),
			digest: Digest(999),
		})).unwrap();

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..6 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Prepare(1, Digest(999)),
			}.into()).unwrap();

			assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
		}

		accumulator.import_message(LocalizedVote {
			sender: AuthorityId(7),
			signature: Signature(999, 7),
			vote: Vote::Prepare(1, Digest(999)),
		}.into()).unwrap();

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn prepare_to_commit() {
		let mut accumulator = Accumulator::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(999, 8),
			digest_signature: Signature(999, 8),
			round_number: 1,
			proposal: Candidate(999),
			digest: Digest(999),
		})).unwrap();

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..6 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Prepare(1, Digest(999)),
			}.into()).unwrap();

			assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
		}

		accumulator.import_message(LocalizedVote {
			sender: AuthorityId(7),
			signature: Signature(999, 7),
			vote: Vote::Prepare(1, Digest(999)),
		}.into()).unwrap();

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..6 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Commit(1, Digest(999)),
			}.into()).unwrap();

			match accumulator.state() {
				&State::Prepared(_) => {},
				s => panic!("wrong state: {:?}", s),
			}
		}

		accumulator.import_message(LocalizedVote {
			sender: AuthorityId(7),
			signature: Signature(999, 7),
			vote: Vote::Commit(1, Digest(999)),
		}.into()).unwrap();

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn prepare_to_advance() {
		let mut accumulator = Accumulator::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(999, 8),
			digest_signature: Signature(999, 8),
			round_number: 1,
			proposal: Candidate(999),
			digest: Digest(999),
		})).unwrap();

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Prepare(1, Digest(999)),
			}.into()).unwrap();
		}

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..6 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::AdvanceRound(1),
			}.into()).unwrap();

			match accumulator.state() {
				&State::Prepared(_) => {},
				s => panic!("wrong state: {:?}", s),
			}
		}

		accumulator.import_message(LocalizedVote {
			sender: AuthorityId(7),
			signature: Signature(999, 7),
			vote: Vote::AdvanceRound(1),
		}.into()).unwrap();

		match accumulator.state() {
			&State::Advanced(Some(_)) => {},
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn conclude_different_than_proposed() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Prepare(1, Digest(999)),
			}.into()).unwrap();
		}

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Commit(1, Digest(999)),
			}.into()).unwrap();
		}

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn begin_to_advance() {
		let mut accumulator = Accumulator::<Candidate, Digest, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(1, i),
				vote: Vote::AdvanceRound(1),
			}.into()).unwrap();
		}

		match accumulator.state() {
			&State::Advanced(ref j) => assert!(j.is_none()),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn conclude_without_prepare() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Commit(1, Digest(999)),
			}.into()).unwrap();
		}

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn double_prepare_is_misbehavior() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Prepare(1, Digest(999)),
			}.into()).unwrap();

			let res = accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(123, i),
				vote: Vote::Prepare(1, Digest(123)),
			}.into());

			assert!(res.is_err());

		}
	}

	#[test]
	fn double_commit_is_misbehavior() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(999, i),
				vote: Vote::Commit(1, Digest(999)),
			}.into()).unwrap();

			let res = accumulator.import_message(LocalizedVote {
				sender: AuthorityId(i),
				signature: Signature(123, i),
				vote: Vote::Commit(1, Digest(123)),
			}.into());

			assert!(res.is_err());

		}
	}

	#[test]
	fn double_propose_is_misbehavior() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, AuthorityId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(999, 8),
			digest_signature: Signature(999, 8),
			round_number: 1,
			proposal: Candidate(999),
			digest: Digest(999),
		})).unwrap();

		let res = accumulator.import_message(LocalizedMessage::Propose(LocalizedProposal {
			sender: AuthorityId(8),
			full_signature: Signature(500, 8),
			digest_signature: Signature(500, 8),
			round_number: 1,
			proposal: Candidate(500),
			digest: Digest(500),
		}));

		assert!(res.is_err());
	}
}
