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

use log::{debug, trace};

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

	pub(crate) fn should_vote(&self, round: &(H, N)) -> bool {
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

	pub(crate) fn is_done(&self, round: &(H, N)) -> bool {
		let done = self
			.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.validator_set.len())))
			.unwrap_or(false);

		debug!(target: "beefy", "🥩 Round #{} done: {}", round.1, done);

		done
	}

	pub(crate) fn conclude(&mut self, round: &(H, N)) -> Option<Vec<Option<Signature>>> {
		trace!(target: "beefy", "🥩 About to drop round #{}", round.1);

		let signatures = self.rounds.remove(round)?.votes;
		self.best_done = self.best_done.clone().max(Some(round.1.clone()));

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
	}
}

#[cfg(test)]
mod tests {
	use sc_network_test::Block;
	use sp_core::H256;
	use sp_runtime::traits::NumberFor;

	use beefy_primitives::{crypto::Public, ValidatorSet};

	use super::Rounds;
	use crate::keystore::tests::Keyring;

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

		assert_eq!(
			&vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			rounds.validators()
		);
	}

	#[test]
	fn add_vote() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			Default::default(),
		)
		.unwrap();

		let mut rounds = Rounds::<H256, NumberFor<Block>>::new(1, validators);

		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true
		));

		assert!(!rounds.is_done(&(H256::from_low_u64_le(1), 1)));

		// invalid vote
		assert!(!rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Dave.public(), Keyring::Dave.sign(b"I am committed")),
			false
		));

		assert!(!rounds.is_done(&(H256::from_low_u64_le(1), 1)));

		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed")),
			false
		));

		assert!(!rounds.is_done(&(H256::from_low_u64_le(1), 1)));

		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Charlie.public(), Keyring::Charlie.sign(b"I am committed")),
			false
		));

		assert!(rounds.is_done(&(H256::from_low_u64_le(1), 1)));
	}

	#[test]
	fn drop() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			Default::default(),
		)
		.unwrap();

		let mut rounds = Rounds::<H256, NumberFor<Block>>::new(1, validators);

		// round 1
		rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed")),
			true,
		);
		rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am committed")),
			false,
		);

		// round 2
		rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am again committed")),
			false,
		);
		rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am again committed")),
			false,
		);

		// round 3
		rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(Keyring::Alice.public(), Keyring::Alice.sign(b"I am still committed")),
			false,
		);
		rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(Keyring::Bob.public(), Keyring::Bob.sign(b"I am still committed")),
			false,
		);

		assert_eq!(3, rounds.rounds.len());

		// conclude unknown round
		assert!(rounds.conclude(&(H256::from_low_u64_le(5), 5)).is_none());
		assert_eq!(3, rounds.rounds.len());

		// conclude round 2
		let signatures = rounds.conclude(&(H256::from_low_u64_le(2), 2)).unwrap();

		assert_eq!(2, rounds.rounds.len());

		assert_eq!(
			signatures,
			vec![
				Some(Keyring::Alice.sign(b"I am again committed")),
				Some(Keyring::Bob.sign(b"I am again committed")),
				None
			]
		);
	}
}
