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

use crate::LOG_TARGET;
use core::fmt::Debug;

use beefy_primitives::{ValidatorSet, ValidatorSetId};
use codec::{Decode, Encode};
use log::{debug, trace};
use sp_runtime::traits::{Block, NumberFor};

/// Tracks for each round which validators have voted/signed and
/// whether the local `self` validator has voted/signed.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Debug, Decode, Encode, PartialEq)]
struct RoundTracker<
	AuthId: Encode + Decode + Debug + Ord + Sync + Send + std::hash::Hash,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
> {
	self_vote: bool,
	votes: BTreeMap<AuthId, TSignature>,
}

impl<
		AuthId: Encode + Decode + Debug + Ord + Sync + Send + core::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	> Default for RoundTracker<AuthId, TSignature>
{
	fn default() -> Self {
		RoundTracker::<_, _> {
			self_vote: false,
			votes: <BTreeMap<AuthId, TSignature> as Default>::default(),
		}
	}
}

impl<
		AuthId: Encode + Decode + Debug + Ord + Sync + Send + core::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	> RoundTracker<AuthId, TSignature>
{
	fn add_vote(&mut self, vote: (AuthId, TSignature), self_vote: bool) -> bool {
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
pub(crate) struct Rounds<
	Payload,
	B: Block,
	AuthId: Encode + Decode + Debug + Ord + Sync + Send + std::hash::Hash,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
> {
	rounds: BTreeMap<(Payload, NumberFor<B>), RoundTracker<AuthId, TSignature>>,
	session_start: NumberFor<B>,
	validator_set: ValidatorSet<AuthId>,
	mandatory_done: bool,
	best_done: Option<NumberFor<B>>,
}

impl<P, B, AuthId, TSignature> Rounds<P, B, AuthId, TSignature>
where
	P: Ord + Hash + Clone,
	B: Block,
	AuthId: Encode + Decode + Debug + Ord + Sync + Send + std::hash::Hash,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
{
	pub(crate) fn new(session_start: NumberFor<B>, validator_set: ValidatorSet<AuthId>) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			session_start,
			validator_set,
			mandatory_done: false,
			best_done: None,
		}
	}

	pub(crate) fn validator_set(&self) -> &ValidatorSet<AuthId> {
		&self.validator_set
	}

	pub(crate) fn validator_set_id(&self) -> ValidatorSetId {
		self.validator_set.id()
	}

	pub(crate) fn validators(&self) -> &[AuthId] {
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
		vote: (AuthId, TSignature),
		self_vote: bool,
	) -> bool {
		let num = round.1;
		if num < self.session_start || Some(num) <= self.best_done {
			debug!(target: LOG_TARGET, "🥩 received vote for old stale round {:?}, ignoring", num);
			false
		} else if !self.validators().iter().any(|id| vote.0 == *id) {
			debug!(
				target: LOG_TARGET,
				"🥩 received vote {:?} from validator that is not in the validator set, ignoring",
				vote
			);
			false
		} else {
			//self.rounds.entry(round.clone()).or_default().add_vote(vote, self_vote)
			self.rounds.entry(round.clone()).or_default().add_vote(vote, self_vote)
		}
	}

	pub(crate) fn should_conclude(
		&mut self,
		round: &(P, NumberFor<B>),
	) -> Option<Vec<Option<TSignature>>> {
		let done = self
			.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.validator_set.len())))
			.unwrap_or(false);
		trace!(target: LOG_TARGET, "🥩 Round #{} done: {}", round.1, done);

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
		debug!(target: LOG_TARGET, "🥩 Concluded round #{}", round_num);
	}
}

#[cfg(test)]
mod tests {
	use core::fmt::Debug;
	use sc_network_test::Block;
	use sp_core::H256;

	use beefy_primitives::{
		bls_crypto::{Public as BLSPublic, Signature as BLSSignature},
		ecdsa_crypto::{self, Public as ECDSAPublic, Signature as ECDSASignature},
		ValidatorSet,
	};
	use codec::{Decode, Encode};

	use super::{threshold, Block as BlockT, Hash, RoundTracker, Rounds};
	use crate::keystore::tests::{ECDSAnBLSPair, GenericKeyring, Keyring, SimpleKeyPair};

	impl<P, B, AuthId, TSignature> Rounds<P, B, AuthId, TSignature>
	where
		P: Ord + Hash + Clone,
		B: BlockT,
		AuthId: Encode + Decode + Debug + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	{
		pub(crate) fn test_set_mandatory_done(&mut self, done: bool) {
			self.mandatory_done = done;
		}
	}

	fn round_tracker<TKeyPair, AuthId, TSignature>()
	where
		TKeyPair: SimpleKeyPair<Public = AuthId, Signature = TSignature>,
		AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	{
		let mut rt = RoundTracker::default();
		let bob_vote = (
			<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
			<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Bob, b"I am committed"),
		);
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

		let alice_vote = (
			<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
			<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am committed"),
		);
		// adding new vote (self vote this time) allowed
		assert!(rt.add_vote(alice_vote, true));

		// self vote registered
		assert!(rt.has_self_vote());
		// vote is now done
		assert!(rt.is_done(threshold));
	}

	#[test]
	fn round_tracker_with_ecdsa_keys() {
		round_tracker::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature>();
	}

	#[test]
	fn round_tracker_with_ecdsa_n_bls_keys() {
		round_tracker::<ECDSAnBLSPair, (ECDSAPublic, BLSPublic), (ECDSASignature, BLSSignature)>();
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

	fn new_rounds<TKeyPair, AuthId, TSignature>()
	where
		TKeyPair: SimpleKeyPair<Public = AuthId, Signature = TSignature>,
		AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	{
		sp_tracing::try_init_simple();
		let validators = ValidatorSet::new(
			vec![
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
			],
			42,
		)
		.unwrap();

		let session_start = 1u64.into();
		let rounds = Rounds::<H256, Block, AuthId, TSignature>::new(session_start, validators);

		assert_eq!(42, rounds.validator_set_id());
		assert_eq!(1, rounds.session_start());
		assert_eq!(
			&vec![
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie)
			],
			rounds.validators()
		);
	}

	#[test]
	fn new_rounds_with_ecdsa_keys() {
		new_rounds::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature>();
	}

	#[test]
	fn new_rounds_with_ecdsa_n_bls_keys() {
		new_rounds::<ECDSAnBLSPair, (ECDSAPublic, BLSPublic), (ECDSASignature, BLSSignature)>();
	}

	fn add_and_conclude_votes<TKeyPair, AuthId, TSignature>()
	where
		TKeyPair: SimpleKeyPair<Public = AuthId, Signature = TSignature>,
		AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	{
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::new(
			vec![
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Eve),
			],
			Default::default(),
		)
		.unwrap();

		let round = (H256::from_low_u64_le(1), 1);

		let session_start = 1u64.into();
		let mut rounds = Rounds::<H256, Block, AuthId, TSignature>::new(session_start, validators);

		// no self vote yet, should self vote
		assert!(rounds.should_self_vote(&round));

		// add 1st good vote
		assert!(rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am committed")
			),
			true
		));
		// round not concluded
		assert!(rounds.should_conclude(&round).is_none());
		// self vote already present, should not self vote
		assert!(!rounds.should_self_vote(&round));

		// double voting not allowed
		assert!(!rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am committed")
			),
			true
		));

		// invalid vote (Dave is not a validator)
		assert!(!rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Dave),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Dave, b"I am committed")
			),
			false
		));
		assert!(rounds.should_conclude(&round).is_none());

		// add 2nd good vote
		assert!(rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Bob, b"I am committed")
			),
			false
		));
		// round not concluded
		assert!(rounds.should_conclude(&round).is_none());

		// add 3rd good vote
		assert!(rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Charlie, b"I am committed")
			),
			false
		));
		// round concluded
		assert!(rounds.should_conclude(&round).is_some());
		rounds.conclude(round.1);

		// Eve is a validator, but round was concluded, adding vote disallowed
		assert!(!rounds.add_vote(
			&round,
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Eve),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Eve, b"I am committed")
			),
			false
		));
	}

	#[test]
	fn add_and_conclude_votes_with_ecdsa_keys() {
		add_and_conclude_votes::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature>();
	}

	#[test]
	fn add_and_conclude_votes_with_ecdsa_n_bls_keys() {
		add_and_conclude_votes::<
			ECDSAnBLSPair,
			(ECDSAPublic, BLSPublic),
			(ECDSASignature, BLSSignature),
		>();
	}

	fn old_rounds_not_accepted<TKeyPair, AuthId, TSignature>()
	where
		TKeyPair: SimpleKeyPair<Public = AuthId, Signature = TSignature>,
		AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	{
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::new(
			vec![
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
			],
			42,
		)
		.unwrap();
		let alice = (
			<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
			<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am committed"),
		);

		let session_start = 10u64.into();
		let mut rounds = Rounds::<H256, Block, AuthId, TSignature>::new(session_start, validators);

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
	fn old_rounds_not_accepted_with_ecdsa_keys() {
		old_rounds_not_accepted::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature>();
	}

	#[test]
	fn old_rounds_not_accepted_with_ecdsa_n_bls_keys() {
		old_rounds_not_accepted::<
			ECDSAnBLSPair,
			(ECDSAPublic, BLSPublic),
			(ECDSASignature, BLSSignature),
		>();
	}

	fn multiple_rounds<TKeyPair, AuthId, TSignature>()
	where
		TKeyPair: SimpleKeyPair<Public = AuthId, Signature = TSignature>,
		AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
		TSignature: Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq,
	{
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::new(
			vec![
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Dave),
			],
			Default::default(),
		)
		.unwrap();

		let session_start = 1u64.into();
		let mut rounds = Rounds::<H256, Block, AuthId, TSignature>::new(session_start, validators);

		// round 1
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am committed")
			),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Bob, b"I am committed")
			),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(1), 1),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Charlie, b"I am committed")
			),
			false,
		));

		// round 2
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Alice,
					b"I am again committed"
				)
			),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Bob, b"I am again committed")
			),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(2), 2),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Charlie,
					b"I am again committed"
				)
			),
			false,
		));

		// round 3
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
				<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Alice,
					b"I am still committed"
				)
			),
			true,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob),
				<Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Bob, b"I am still committed")
			),
			false,
		));
		assert!(rounds.add_vote(
			&(H256::from_low_u64_le(3), 3),
			(
				<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie),
				<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Charlie,
					b"I am still committed"
				)
			),
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
				Some(<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Alice,
					b"I am again committed"
				)),
				Some(<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Bob,
					b"I am again committed"
				)),
				Some(<Keyring as GenericKeyring<TKeyPair>>::sign(
					Keyring::Charlie,
					b"I am again committed"
				)),
				None
			]
		);
	}

	#[test]
	fn multiple_rounds_with_ecdsa_keys() {
		multiple_rounds::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature>();
	}

	#[test]
	fn multiple_rounds_with_ecdsa_n_bls_keys() {
		multiple_rounds::<ECDSAnBLSPair, (ECDSAPublic, BLSPublic), (ECDSASignature, BLSSignature)>(
		);
	}
}
