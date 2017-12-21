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

/// Context necessary to execute a round of BFT.
pub trait Context {
	/// A full candidate.
	type Candidate: Clone;
	/// Unique digest of a proposed candidate (think hash).
	type Digest: Hash + Eq + Clone;
	/// Validator ID.
	type ValidatorId: Hash + Eq;
	/// A signature.
	type Signature: Eq + Clone;
}

/// Justification at a given round.
#[derive(PartialEq, Eq, Debug)]
pub struct Justification<D, S> {
	/// The round.
	pub round_number: usize,
	/// The digest prepared for.
	pub digest: D,
	/// Signatures for the prepare messages.
	pub signatures: Vec<S>,
}

impl<D, S> Justification<D, S> {
	/// Fails if there are duplicate signatures or invalid.
	///
	/// Provide a closure for checking whether the signature is valid on a
	/// digest.
	///
	/// The closure should return true iff the round number, digest, and signature
	/// represent a valid prepare message and the signer was authorized to issue
	/// it.
	pub fn check<F, V>(&self, max_faulty: usize, check_message: F) -> bool
		where
			F: Fn(usize, &D, &S) -> Option<V>,
			V: Hash + Eq,
	{
		let mut prepared = HashSet::new();

		let mut good = false;
		for signature in &self.signatures {
			match check_message(self.round_number, &self.digest, signature) {
				None => return false,
				Some(v) => {
					if !prepared.insert(v) {
						return false;
					} else if prepared.len() > max_faulty * 2 {
						// don't return just yet since later signatures may be invalid.
						good = true;
					}
				}
			}
		}

		good
	}
}

/// Type alias to represent a justification specifically for a prepare.
pub type PrepareJustification<D, S> = Justification<D, S>;

/// The round's state, based on imported messages.
#[derive(PartialEq, Eq, Debug)]
pub enum State<C, D, S> {
	/// No proposal yet.
	Begin,
	/// Proposal received.
	Proposed(C),
	/// Seen 2f + 1 prepares for this digest.
	Prepared(PrepareJustification<D, S>),
	/// Seen 2f + 1 commits for a digest.
	Concluded(Justification<D, S>),
	/// Seen 2f + 1 round-advancement messages.
	Advanced(Option<PrepareJustification<D, S>>),
}

/// Accumulates messages for a given round of BFT consensus.
pub struct Accumulator<C, D, V, S> {
	round_number: usize,
	max_faulty: usize,
	round_proposer: V,
	proposal: Option<C>,
	prepares: HashMap<V, (D, S)>,
	commits: HashMap<V, (D, S)>,
	vote_counts: HashMap<D, (usize, usize)>,
	advance_round: HashSet<V>,
	state: State<C, D, S>,
}

impl<C, D, V, S> Accumulator<C, D, V, S>
	where
	C: Eq + Clone,
	D: Hash + Clone + Eq,
	V: Hash + Eq,
	S: Eq + Clone,
{
	/// Create a new state accumulator.
	pub fn new(round_number: usize, max_faulty: usize, round_proposer: V) -> Self {
		Accumulator {
			round_number,
			max_faulty,
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

	/// Inspect the current consensus state.
	pub fn state(&self) -> &State<C, D, S> {
		&self.state
	}

	/// Import a message. Importing duplicates is fine, but the signature
	/// and authorization should have already been checked.
	pub fn import_message(
		&mut self,
		message: LocalizedMessage<C, D, V, S>,
	)
	{
		// old message.
		if message.message.round_number() != self.round_number {
			return;
		}

		let (sender, signature) = (message.sender, message.signature);

		match message.message {
			Message::Propose(_, p) => self.import_proposal(p, sender, signature),
			Message::Prepare(_, d) => self.import_prepare(d, sender, signature),
			Message::Commit(_, d) => self.import_commit(d, sender, signature),
			Message::AdvanceRound(_) => self.import_advance_round(sender),
		}
	}

	fn import_proposal(
		&mut self,
		proposal: C,
		sender: V,
		signature: S,
	) {
		if sender != self.round_proposer || self.proposal.is_some() { return }

		self.proposal = Some(proposal.clone());
		self.state = State::Proposed(proposal);
	}

	fn import_prepare(
		&mut self,
		candidate: D,
		sender: V,
		signature: S,
	) {
		// ignore any subsequent prepares by the same sender.
		// TODO: if digest is different, that's misbehavior.
		let prepared_for = if let Entry::Vacant(vacant) = self.prepares.entry(sender) {
			vacant.insert((candidate.clone(), signature));
			let count = self.vote_counts.entry(candidate.clone()).or_insert((0, 0));
			count.0 += 1;

			if count.0 == self.max_faulty * 2 + 1 {
				Some(candidate)
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

		if let (true, Some(prepared_for)) = (valid_transition, prepared_for) {
			let signatures = self.prepares
				.values()
				.filter(|&&(ref d, _)| d == &prepared_for)
				.map(|&(_, ref s)| s.clone())
				.collect();

			self.state = State::Prepared(PrepareJustification {
				round_number: self.round_number,
				digest: prepared_for,
				signatures: signatures,
			});
		}
	}

	fn import_commit(
		&mut self,
		candidate: D,
		sender: V,
		signature: S,
	) {
		// ignore any subsequent commits by the same sender.
		// TODO: if digest is different, that's misbehavior.
		let committed_for = if let Entry::Vacant(vacant) = self.commits.entry(sender) {
			vacant.insert((candidate.clone(), signature));
			let count = self.vote_counts.entry(candidate.clone()).or_insert((0, 0));
			count.1 += 1;

			if count.1 == self.max_faulty * 2 + 1 {
				Some(candidate)
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
		if let Some(committed_for) = committed_for {
			let signatures = self.commits
				.values()
				.filter(|&&(ref d, _)| d == &committed_for)
				.map(|&(_, ref s)| s.clone())
				.collect();

			self.state = State::Concluded(Justification {
				round_number: self.round_number,
				digest: committed_for,
				signatures: signatures,
			});
		}
	}

	fn import_advance_round(
		&mut self,
		sender: V,
	) {
		self.advance_round.insert(sender);

		if self.advance_round.len() != self.max_faulty * 2 + 1 { return }

		// allow transition to new round only if we haven't produced a justification
		// yet.
		self.state = match ::std::mem::replace(&mut self.state, State::Begin) {
			State::Concluded(j) => State::Concluded(j),
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
		let mut justification = Justification {
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

		assert!(justification.check(3, &check_message));
		assert!(!justification.check(5, &check_message));

		{
			// one bad signature is enough to spoil it.
			justification.signatures.push(Signature(1001, 255));
			assert!(!justification.check(3, &check_message));

			justification.signatures.pop();
		}
		// duplicates not allowed.
		justification.signatures.extend((0..10).map(|i| Signature(600, i)));
		assert!(!justification.check(3, &check_message));
	}

	#[test]
	fn accepts_proposal_from_proposer_only() {
		let mut accumulator = Accumulator::<_, Digest, _, _>::new(1, 3, ValidatorId(8));
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
		let mut accumulator = Accumulator::new(1, 3, ValidatorId(8));
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
		let mut accumulator = Accumulator::new(1, 3, ValidatorId(8));
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
			&State::Concluded(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}

	#[test]
	fn prepare_to_advance() {
		let mut accumulator = Accumulator::new(1, 3, ValidatorId(8));
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
		let mut accumulator = Accumulator::<Candidate, _, _, _>::new(1, 3, ValidatorId(8));
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
			&State::Concluded(ref j) => assert_eq!(j.digest, Digest(999)),
			s => panic!("wrong state: {:?}", s),
		}
	}
}
