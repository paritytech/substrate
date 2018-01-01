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

//! Message accumulator for each round of BFT consensus.

use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use super::{Message, LocalizedMessage};

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

/// Accumulates messages for a given round of BFT consensus.
///
/// This isn't tied to the "view" of a single validator. It
/// keeps accurate track of the state of the BFT consensus based
/// on all messages imported.
#[derive(Debug)]
pub struct Accumulator<Candidate, Digest, ValidatorId, Signature>
	where
	Candidate: Eq + Clone,
	Digest: Hash + Eq + Clone,
	ValidatorId: Hash + Eq,
	Signature: Eq + Clone,
{
	round_number: usize,
	threshold: usize,
	round_proposer: ValidatorId,
	proposal: Option<Candidate>,
	prepares: HashMap<ValidatorId, (Digest, Signature)>,
	commits: HashMap<ValidatorId, (Digest, Signature)>,
	vote_counts: HashMap<Digest, VoteCounts>,
	advance_round: HashSet<ValidatorId>,
	state: State<Candidate, Digest, Signature>,
}

impl<Candidate, Digest, ValidatorId, Signature> Accumulator<Candidate, Digest, ValidatorId, Signature>
	where
	Candidate: Eq + Clone,
	Digest: Hash + Eq + Clone,
	ValidatorId: Hash + Eq,
	Signature: Eq + Clone,
{
	/// Create a new state accumulator.
	pub fn new(round_number: usize, threshold: usize, round_proposer: ValidatorId) -> Self {
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

	/// Get the round proposer.
	pub fn round_proposer(&self) -> &ValidatorId {
		&self.round_proposer
	}

	pub fn proposal(&self) -> Option<&Candidate> {
		self.proposal.as_ref()
	}

	/// Inspect the current consensus state.
	pub fn state(&self) -> &State<Candidate, Digest, Signature> {
		&self.state
	}

	/// Import a message. Importing duplicates is fine, but the signature
	/// and authorization should have already been checked.
	pub fn import_message(
		&mut self,
		message: LocalizedMessage<Candidate, Digest, ValidatorId, Signature>,
	)
	{
		// message from different round.
		if message.message.round_number() != self.round_number {
			return;
		}

		let (sender, signature) = (message.sender, message.signature);

		match message.message {
			Message::Propose(_, p) => self.import_proposal(p, sender),
			Message::Prepare(_, d) => self.import_prepare(d, sender, signature),
			Message::Commit(_, d) => self.import_commit(d, sender, signature),
			Message::AdvanceRound(_) => self.import_advance_round(sender),
		}
	}

	fn import_proposal(
		&mut self,
		proposal: Candidate,
		sender: ValidatorId,
	) {
		if sender != self.round_proposer || self.proposal.is_some() { return }

		self.proposal = Some(proposal.clone());
		self.state = State::Proposed(proposal);
	}

	fn import_prepare(
		&mut self,
		digest: Digest,
		sender: ValidatorId,
		signature: Signature,
	) {
		// ignore any subsequent prepares by the same sender.
		// TODO: if digest is different, that's misbehavior.
		let threshold_prepared = if let Entry::Vacant(vacant) = self.prepares.entry(sender) {
			vacant.insert((digest.clone(), signature));
			let count = self.vote_counts.entry(digest.clone()).or_insert_with(Default::default);
			count.prepared += 1;

			if count.prepared >= self.threshold {
				Some(digest)
			} else {
				None
			}
		} else {
			None
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
	}

	fn import_commit(
		&mut self,
		digest: Digest,
		sender: ValidatorId,
		signature: Signature,
	) {
		// ignore any subsequent commits by the same sender.
		// TODO: if digest is different, that's misbehavior.
		let threshold_committed = if let Entry::Vacant(vacant) = self.commits.entry(sender) {
			vacant.insert((digest.clone(), signature));
			let count = self.vote_counts.entry(digest.clone()).or_insert_with(Default::default);
			count.committed += 1;

			if count.committed >= self.threshold {
				Some(digest)
			} else {
				None
			}
		} else {
			None
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
	}

	fn import_advance_round(
		&mut self,
		sender: ValidatorId,
	) {
		self.advance_round.insert(sender);

		if self.advance_round.len() < self.threshold { return }

		// allow transition to new round only if we haven't produced a justification
		// yet.
		self.state = match ::std::mem::replace(&mut self.state, State::Begin) {
			State::Committed(j) => State::Committed(j),
			State::Prepared(j) => State::Advanced(Some(j)),
			State::Advanced(j) => State::Advanced(j),
			State::Begin | State::Proposed(_) => State::Advanced(None),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Candidate(usize);

	#[derive(Hash, PartialEq, Eq, Clone, Debug)]
	pub struct Digest(usize);

	#[derive(Hash, PartialEq, Eq, Debug)]
	pub struct ValidatorId(usize);

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
				Some(ValidatorId(s.1))
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
		let mut accumulator = Accumulator::<_, Digest, _, _>::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(5),
			signature: Signature(999, 5),
			message: Message::Propose(1, Candidate(999)),
		});

		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(8),
			signature: Signature(999, 8),
			message: Message::Propose(1, Candidate(999)),
		});

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
	}

	#[test]
	fn reaches_prepare_phase() {
		let mut accumulator = Accumulator::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(8),
			signature: Signature(999, 8),
			message: Message::Propose(1, Candidate(999)),
		});

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..6 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Prepare(1, Digest(999)),
			});

			assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
		}

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(7),
			signature: Signature(999, 7),
			message: Message::Prepare(1, Digest(999)),
		});

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn prepare_to_commit() {
		let mut accumulator = Accumulator::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(8),
			signature: Signature(999, 8),
			message: Message::Propose(1, Candidate(999)),
		});

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..6 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Prepare(1, Digest(999)),
			});

			assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));
		}

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(7),
			signature: Signature(999, 7),
			message: Message::Prepare(1, Digest(999)),
		});

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..6 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Commit(1, Digest(999)),
			});

			match accumulator.state() {
				&State::Prepared(_) => {},
				s => panic!("wrong state: {:?}", s),
			}
		}

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(7),
			signature: Signature(999, 7),
			message: Message::Commit(1, Digest(999)),
		});

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn prepare_to_advance() {
		let mut accumulator = Accumulator::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(8),
			signature: Signature(999, 8),
			message: Message::Propose(1, Candidate(999)),
		});

		assert_eq!(accumulator.state(), &State::Proposed(Candidate(999)));

		for i in 0..7 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Prepare(1, Digest(999)),
			});
		}

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..6 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::AdvanceRound(1),
			});

			match accumulator.state() {
				&State::Prepared(_) => {},
				s => panic!("wrong state: {:?}", s),
			}
		}

		accumulator.import_message(LocalizedMessage {
			sender: ValidatorId(7),
			signature: Signature(999, 7),
			message: Message::AdvanceRound(1),
		});

		match accumulator.state() {
			&State::Advanced(Some(_)) => {},
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn conclude_different_than_proposed() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Prepare(1, Digest(999)),
			});
		}

		match accumulator.state() {
			&State::Prepared(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}

		for i in 0..7 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Commit(1, Digest(999)),
			});
		}

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn begin_to_advance() {
		let mut accumulator = Accumulator::<Candidate, Digest, _, _>::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(1, i),
				message: Message::AdvanceRound(1),
			});
		}

		match accumulator.state() {
			&State::Advanced(ref j) => assert!(j.is_none()),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn conclude_without_prepare() {
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 7, ValidatorId(8));
		assert_eq!(accumulator.state(), &State::Begin);

		for i in 0..7 {
			accumulator.import_message(LocalizedMessage {
				sender: ValidatorId(i),
				signature: Signature(999, i),
				message: Message::Commit(1, Digest(999)),
			});
		}

		match accumulator.state() {
			&State::Committed(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}
}
