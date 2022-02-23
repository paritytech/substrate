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

use std::{collections::BTreeMap, hash::Hash};

use log::trace;

use beefy_primitives::{
	crypto::{Public, Signature},
	ValidatorSet, ValidatorSetId,
};
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_runtime::traits::MaybeDisplay;

#[derive(Default)]
struct RoundTracker {
	self_vote: bool,
	votes: Vec<(Public, Signature)>,
}

impl RoundTracker {
	fn add_vote(&mut self, vote: (Public, Signature), self_vote: bool) -> bool {
		if self.votes.contains(&vote) {
			return false
		}

		self.self_vote = self.self_vote || self_vote;
		self.votes.push(vote);
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

pub(crate) struct Rounds<Payload, Number> {
	rounds: BTreeMap<(Payload, Number), RoundTracker>,
	best_done: Option<Number>,
	session_start: Number,
	validator_set: ValidatorSet<Public>,
}

impl<P, N> Rounds<P, N>
where
	P: Ord + Hash,
	N: Ord + AtLeast32BitUnsigned + MaybeDisplay,
{
	pub(crate) fn new(session_start: N, validator_set: ValidatorSet<Public>) -> Self {
		Rounds { rounds: BTreeMap::new(), best_done: None, session_start, validator_set }
	}
}

impl<H, N> Rounds<H, N>
where
	H: Ord + Hash + Clone,
	N: Ord + AtLeast32BitUnsigned + MaybeDisplay + Clone,
{
	pub(crate) fn validator_set_id(&self) -> ValidatorSetId {
		self.validator_set.id()
	}

	pub(crate) fn validators(&self) -> &[Public] {
		self.validator_set.validators()
	}

	pub(crate) fn session_start(&self) -> &N {
		&self.session_start
	}

	pub(crate) fn should_self_vote(&self, round: &(H, N)) -> bool {
		Some(round.1.clone()) > self.best_done &&
			self.rounds.get(round).map(|tracker| !tracker.has_self_vote()).unwrap_or(true)
	}

	pub(crate) fn add_vote(
		&mut self,
		round: &(H, N),
		vote: (Public, Signature),
		self_vote: bool,
	) -> bool {
		if Some(round.1.clone()) > self.best_done &&
			self.validator_set.validators().iter().any(|id| vote.0 == *id)
		{
			self.rounds.entry(round.clone()).or_default().add_vote(vote, self_vote)
		} else {
			false
		}
	}

	pub(crate) fn try_conclude(&mut self, round: &(H, N)) -> Option<Vec<Option<Signature>>> {
		let done = self
			.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.validator_set.len())))
			.unwrap_or(false);
		trace!(target: "beefy", "🥩 Round #{} done: {}", round.1, done);

		if done {
			let signatures = self.rounds.remove(round)?.votes;
			self.best_done = self.best_done.clone().max(Some(round.1.clone()));
			trace!(target: "beefy", "🥩 Concluded round #{}", round.1);

			Some(
				self.validator_set
					.validators()
					.iter()
					.map(|authority_id| {
						signatures.iter().find_map(|(id, sig)| {
							if id == authority_id {
								Some(sig.clone())
							} else {
								None
							}
						})
					})
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
	use sp_runtime::traits::NumberFor;

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

		let rounds = Rounds::<H256, NumberFor<Block>>::new(1, validators);

		assert_eq!(42, rounds.validator_set_id());
		assert_eq!(1, *rounds.session_start());
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

		let mut rounds = Rounds::<H256, NumberFor<Block>>::new(1, validators);

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

		let mut rounds = Rounds::<H256, NumberFor<Block>>::new(1, validators);

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
		assert_eq!(2, rounds.rounds.len());

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
