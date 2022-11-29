// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use beefy_primitives::{
	crypto::{Public, Signature},
	ValidatorSet, ValidatorSetId,
};
use codec::{Decode, Encode};
use log::{debug, trace};
use sp_runtime::traits::{Block, NumberFor};
use std::{collections::BTreeMap, hash::Hash};

/// Tracks for each round which validators have voted/signed and
/// whether the local `self` validator has voted/signed.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Debug, Decode, Default, Encode, PartialEq)]
struct RoundTracker {
	self_vote: bool,
	votes: BTreeMap<Public, Signature>,
}

impl RoundTracker {
	fn add_vote(&mut self, vote: (Public, Signature), self_vote: bool) -> bool {
		if self.votes.contains_key(&vote.0) {
			return false
		}

		self.self_vote = self.self_vote || self_vote;
		self.votes.insert(vote.0, vote.1);
		true
	}

	fn has_self_vote(&self) -> bool {
		self.self_vote
	}

	fn is_done(&self, threshold: usize) -> bool {
		self.votes.len() >= threshold
	}
}

/// Minimum size of `authorities` subset that produced valid signatures for a block to finalize.
pub fn threshold(authorities: usize) -> usize {
	let faulty = authorities.saturating_sub(1) / 3;
	authorities - faulty
}

/// Keeps track of all voting rounds (block numbers) within a session.
/// Only round numbers > `best_done` are of interest, all others are considered stale.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Debug, Decode, Encode, PartialEq)]
pub(crate) struct Rounds<Payload, B: Block> {
	rounds: BTreeMap<(Payload, NumberFor<B>), RoundTracker>,
	session_start: NumberFor<B>,
	validator_set: ValidatorSet<Public>,
	mandatory_done: bool,
	best_done: Option<NumberFor<B>>,
}

impl<P, B> Rounds<P, B>
where
	P: Ord + Hash + Clone,
	B: Block,
{
	pub(crate) fn new(session_start: NumberFor<B>, validator_set: ValidatorSet<Public>) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			session_start,
			validator_set,
			mandatory_done: false,
			best_done: None,
		}
	}

	pub(crate) fn validator_set_id(&self) -> ValidatorSetId {
		self.validator_set.id()
	}

	pub(crate) fn validators(&self) -> &[Public] {
		self.validator_set.validators()
	}

	pub(crate) fn session_start(&self) -> NumberFor<B> {
		self.session_start
	}

	pub(crate) fn mandatory_done(&self) -> bool {
		self.mandatory_done
	}

	pub(crate) fn should_self_vote(&self, round: &(P, NumberFor<B>)) -> bool {
		Some(round.1) > self.best_done &&
			self.rounds.get(round).map(|tracker| !tracker.has_self_vote()).unwrap_or(true)
	}

	pub(crate) fn add_vote(
		&mut self,
		round: &(P, NumberFor<B>),
		vote: (Public, Signature),
		self_vote: bool,
	) -> bool {
		let num = round.1;
		if num < self.session_start || Some(num) <= self.best_done {
			debug!(target: "beefy", "🥩 received vote for old stale round {:?}, ignoring", num);
			false
		} else if !self.validators().iter().any(|id| vote.0 == *id) {
			debug!(
				target: "beefy",
				"🥩 received vote {:?} from validator that is not in the validator set, ignoring",
				vote
			);
			false
		} else {
			self.rounds.entry(round.clone()).or_default().add_vote(vote, self_vote)
		}
	}

	pub(crate) fn should_conclude(
		&mut self,
		round: &(P, NumberFor<B>),
	) -> Option<Vec<Option<Signature>>> {
		let done = self
			.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.validator_set.len())))
			.unwrap_or(false);
		trace!(target: "beefy", "🥩 Round #{} done: {}", round.1, done);

		if done {
			let signatures = self.rounds.remove(round)?.votes;
			Some(
				self.validators()
					.iter()
					.map(|authority_id| signatures.get(authority_id).cloned())
					.collect(),
			)
		} else {
			None
		}
	}

	pub(crate) fn conclude(&mut self, round_num: NumberFor<B>) {
		// Remove this and older (now stale) rounds.
		self.rounds.retain(|&(_, number), _| number > round_num);
		self.mandatory_done = self.mandatory_done || round_num == self.session_start;
		self.best_done = self.best_done.max(Some(round_num));
		debug!(target: "beefy", "🥩 Concluded round #{}", round_num);
	}
}

#[cfg(test)]
mod tests {
	use sc_network_test::Block;
	use sp_core::H256;

	use beefy_primitives::{crypto::Public, ValidatorSet};

	use super::{threshold, Block as BlockT, Hash, RoundTracker, Rounds};
	use crate::keystore::tests::Keyring;

	impl<P, B> Rounds<P, B>
	where
		P: Ord + Hash + Clone,
		B: BlockT,
	{
		pub(crate) fn test_set_mandatory_done(&mut self, done: bool) {
			self.mandatory_done = done;
		}
	}

	#[test]
	fn round_tracker() {
		let mut rt = RoundTracker::default();
		let bob_vote = (Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed"));
		let threshold = 2;

		// self vote not added yet
		assert!(!rt.has_self_vote());

		// adding new vote allowed
		assert!(rt.add_vote(bob_vote.clone(), false));
		// adding existing vote not allowed
		assert!(!rt.add_vote(bob_vote, false));

		// self vote still not added yet
		assert!(!rt.has_self_vote());

		// vote is not done
		assert!(!rt.is_done(threshold));

		let alice_vote = (Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed"));
		// adding new vote (self vote this time) allowed
		assert!(rt.add_vote(alice_vote, true));

		// self vote registered
		assert!(rt.has_self_vote());
		// vote is now done
		assert!(rt.is_done(threshold));
	}

	#[test]
	fn vote_threshold() {
		assert_eq!(threshold(1), 1);
		assert_eq!(threshold(2), 2);
		assert_eq!(threshold(3), 3);
		assert_eq!(threshold(4), 3);
		assert_eq!(threshold(100), 67);
		assert_eq!(threshold(300), 201);
	}

	#[test]
	fn new_rounds() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			42,
		)
		.unwrap();

		let session_start = 1u64.into();
		let rounds = Rounds::<H256, Block>::new(session_start, validators);

		assert_eq!(42, rounds.validator_set_id());
		assert_eq!(1, rounds.session_start());
		assert_eq!(
			&vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			rounds.validators()
		);
	}

	#[test]
	fn add_and_conclude_votes() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![
				Keyring::Alice.public(),
				Keyring::Bob.public(),
				Keyring::Charlie.public(),
				Keyring::Eve.public(),
			],
			Default::default(),
		)
		.unwrap();
		let round = (H256::from_low_u64_le(1), 1);

		let session_start = 1u64.into();
		let mut rounds = Rounds::<H256, Block>::new(session_start, validators);

		// no self vote yet, should self vote
		assert!(rounds.should_self_vote(&round));

		// add 1st good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true
		));
		// round not concluded
		assert!(rounds.should_conclude(&round).is_none());
		// self vote already present, should not self vote
		assert!(!rounds.should_self_vote(&round));

		// double voting not allowed
		assert!(!rounds.add_vote(
			&round,
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true
		));

		// invalid vote (Dave is not a validator)
		assert!(!rounds.add_vote(
			&round,
			(Keyring::Dave.public(), Keyring::Dave.sign(b"I am committed")),
			false
		));
		assert!(rounds.should_conclude(&round).is_none());

		// add 2nd good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed")),
			false
		));
		// round not concluded
		assert!(rounds.should_conclude(&round).is_none());

		// add 3rd good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am committed")),
			false
		));
		// round concluded
		assert!(rounds.should_conclude(&round).is_some());
		rounds.conclude(round.1);

		// Eve is a validator, but round was concluded, adding vote disallowed
		assert!(!rounds.add_vote(
			&round,
			(Keyring::Eve.public(), Keyring::Eve.sign(b"I am committed")),
			false
		));
	}

	#[test]
	fn old_rounds_not_accepted() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			42,
		)
		.unwrap();
		let alice = (Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed"));

		let session_start = 10u64.into();
		let mut rounds = Rounds::<H256, Block>::new(session_start, validators);

		let mut vote = (H256::from_low_u64_le(1), 9);
		// add vote for previous session, should fail
		assert!(!rounds.add_vote(&vote, alice.clone(), true));
		// no votes present
		assert!(rounds.rounds.is_empty());

		// simulate 11 was concluded
		rounds.best_done = Some(11);
		// add votes for current session, but already concluded rounds, should fail
		vote.1 = 10;
		assert!(!rounds.add_vote(&vote, alice.clone(), true));
		vote.1 = 11;
		assert!(!rounds.add_vote(&vote, alice.clone(), true));
		// no votes present
		assert!(rounds.rounds.is_empty());

		// add good vote
		vote.1 = 12;
		assert!(rounds.add_vote(&vote, alice, true));
		// good vote present
		assert_eq!(rounds.rounds.len(), 1);
	}

	#[test]
	fn multiple_rounds() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![
				Keyring::Alice.public(),
				Keyring::Bob.public(),
				Keyring::Charlie.public(),
				Keyring::Dave.public(),
			],
			Default::default(),
		)
		.unwrap();

		let session_start = 1u64.into();
		let mut rounds = Rounds::<H256, Block>::new(session_start, validators);

		// round 1
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed")),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am committed")),
			false,
		));

		// round 2
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am again committed")),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am again committed")),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am again committed")),
			false,
		));

		// round 3
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am still committed")),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am still committed")),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am still committed")),
			false,
		));
		assert_eq!(3, rounds.rounds.len());

		// conclude unknown round
		assert!(rounds.should_conclude(&(H256::from_low_u64_le(5), 5)).is_none());
		assert_eq!(3, rounds.rounds.len());

		// conclude round 2
		let signatures = rounds.should_conclude(&(H256::from_low_u64_le(2), 2)).unwrap();
		rounds.conclude(2);
		assert_eq!(1, rounds.rounds.len());

		assert_eq!(
			signatures,
			vec![
				Some(Keyring::Alice.sign(b"I am again committed")),
				Some(Keyring::Bob.sign(b"I am again committed")),
				Some(Keyring::Charlie.sign(b"I am again committed")),
				None
			]
		);
	}
}
