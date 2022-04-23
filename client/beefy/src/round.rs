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

use std::{
	collections::{BTreeMap, HashMap},
	hash::Hash,
};

use log::{debug, trace};

use beefy_primitives::{
	crypto::{Public, Signature},
	ValidatorSet, ValidatorSetId,
};
use sp_runtime::traits::{Block, NumberFor};

/// Tracks for each round which validators have voted/signed and
/// whether the local `self` validator has voted/signed.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Default)]
struct RoundTracker {
	self_vote: bool,
	votes: HashMap<Public, Signature>,
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

fn threshold(authorities: usize) -> usize {
	let faulty = authorities.saturating_sub(1) / 3;
	authorities - faulty
}

/// Keeps track of all voting rounds (block numbers) within a session.
/// Only round numbers > `best_done` are of interest, all others are considered stale.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
pub(crate) struct Rounds<Payload, B: Block> {
	rounds: BTreeMap<(Payload, NumberFor<B>), RoundTracker>,
	best_done: Option<NumberFor<B>>,
	session_start: NumberFor<B>,
	validator_set: ValidatorSet<Public>,
	prev_validator_set: ValidatorSet<Public>,
}

impl<P, B> Rounds<P, B>
where
	P: Ord + Hash + Clone,
	B: Block,
{
	pub(crate) fn new(
		session_start: NumberFor<B>,
		validator_set: ValidatorSet<Public>,
		prev_validator_set: ValidatorSet<Public>,
	) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			best_done: None,
			session_start,
			validator_set,
			prev_validator_set,
		}
	}
}

impl<P, B> Rounds<P, B>
where
	P: Ord + Hash + Clone,
	B: Block,
{
	pub(crate) fn validator_set_id_for(&self, block_number: NumberFor<B>) -> ValidatorSetId {
		if block_number > self.session_start {
			self.validator_set.id()
		} else {
			self.prev_validator_set.id()
		}
	}

	pub(crate) fn validators_for(&self, block_number: NumberFor<B>) -> &[Public] {
		if block_number > self.session_start {
			self.validator_set.validators()
		} else {
			self.prev_validator_set.validators()
		}
	}

	pub(crate) fn validator_set(&self) -> &ValidatorSet<Public> {
		&self.validator_set
	}

	pub(crate) fn session_start(&self) -> &NumberFor<B> {
		&self.session_start
	}

	pub(crate) fn should_self_vote(&self, round: &(P, NumberFor<B>)) -> bool {
		Some(round.1.clone()) > self.best_done &&
			self.rounds.get(round).map(|tracker| !tracker.has_self_vote()).unwrap_or(true)
	}

	pub(crate) fn add_vote(
		&mut self,
		round: &(P, NumberFor<B>),
		vote: (Public, Signature),
		self_vote: bool,
	) -> bool {
		if Some(round.1.clone()) <= self.best_done {
			debug!(
				target: "beefy",
				"🥩 received vote for old stale round {:?}, ignoring",
				round.1
			);
			false
		} else if !self.validator_set.validators().iter().any(|id| vote.0 == *id) {
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

	pub(crate) fn try_conclude(
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
			// remove this and older (now stale) rounds
			let signatures = self.rounds.remove(round)?.votes;
			self.rounds.retain(|&(_, number), _| number > round.1);
			self.best_done = self.best_done.clone().max(Some(round.1.clone()));
			debug!(target: "beefy", "🥩 Concluded round #{}", round.1);

			Some(
				self.validator_set
					.validators()
					.iter()
					.map(|authority_id| signatures.get(authority_id).cloned())
					.collect(),
			)
		} else {
			None
		}
	}
}

#[cfg(test)]
mod tests {
	use sc_network_test::Block;
	use sp_core::H256;

	use beefy_primitives::{crypto::Public, ValidatorSet};

	use super::{threshold, RoundTracker, Rounds};
	use crate::keystore::tests::Keyring;

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
		let rounds = Rounds::<H256, Block>::new(session_start, validators.clone(), validators);

		assert_eq!(42, rounds.validator_set_id_for(session_start));
		assert_eq!(1, *rounds.session_start());
		assert_eq!(
			&vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			rounds.validators_for(session_start)
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
		let mut rounds = Rounds::<H256, Block>::new(session_start, validators.clone(), validators);

		// no self vote yet, should self vote
		assert!(rounds.should_self_vote(&round));

		// add 1st good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true
		));
		// round not concluded
		assert!(rounds.try_conclude(&round).is_none());
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
		assert!(rounds.try_conclude(&round).is_none());

		// add 2nd good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed")),
			false
		));
		// round not concluded
		assert!(rounds.try_conclude(&round).is_none());

		// add 3rd good vote
		assert!(rounds.add_vote(
			&round,
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am committed")),
			false
		));
		// round concluded
		assert!(rounds.try_conclude(&round).is_some());

		// Eve is a validator, but round was concluded, adding vote disallowed
		assert!(!rounds.add_vote(
			&round,
			(Keyring::Eve.public(), Keyring::Eve.sign(b"I am committed")),
			false
		));
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
		let mut rounds = Rounds::<H256, Block>::new(session_start, validators.clone(), validators);

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
		assert!(rounds.try_conclude(&(H256::from_low_u64_le(5), 5)).is_none());
		assert_eq!(3, rounds.rounds.len());

		// conclude round 2
		let signatures = rounds.try_conclude(&(H256::from_low_u64_le(2), 2)).unwrap();
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
