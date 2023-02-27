// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::LOG_TARGET;

use beefy_primitives::{
	crypto::{AuthorityId, Public, Signature},
	Commitment, EquivocationProof, SignedCommitment, ValidatorSet, ValidatorSetId, VoteMessage,
};
use codec::{Decode, Encode};
use log::debug;
use sp_runtime::traits::{Block, NumberFor};
use std::collections::BTreeMap;

/// Tracks for each round which validators have voted/signed and
/// whether the local `self` validator has voted/signed.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Debug, Decode, Default, Encode, PartialEq)]
pub(crate) struct RoundTracker {
	votes: BTreeMap<Public, Signature>,
}

impl RoundTracker {
	fn add_vote(&mut self, vote: (Public, Signature)) -> bool {
		if self.votes.contains_key(&vote.0) {
			return false
		}

		self.votes.insert(vote.0, vote.1);
		true
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

#[derive(Debug, PartialEq)]
pub enum VoteImportResult<B: Block> {
	Ok,
	RoundConcluded(SignedCommitment<NumberFor<B>, Signature>),
	Equivocation(EquivocationProof<NumberFor<B>, Public, Signature>),
	Invalid,
	Stale,
}

/// Keeps track of all voting rounds (block numbers) within a session.
/// Only round numbers > `best_done` are of interest, all others are considered stale.
///
/// Does not do any validation on votes or signatures, layers above need to handle that (gossip).
#[derive(Debug, Decode, Encode, PartialEq)]
pub(crate) struct Rounds<B: Block> {
	rounds: BTreeMap<Commitment<NumberFor<B>>, RoundTracker>,
	previous_votes: BTreeMap<(Public, NumberFor<B>), VoteMessage<NumberFor<B>, Public, Signature>>,
	session_start: NumberFor<B>,
	validator_set: ValidatorSet<Public>,
	mandatory_done: bool,
	best_done: Option<NumberFor<B>>,
}

impl<B> Rounds<B>
where
	B: Block,
{
	pub(crate) fn new(session_start: NumberFor<B>, validator_set: ValidatorSet<Public>) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			previous_votes: BTreeMap::new(),
			session_start,
			validator_set,
			mandatory_done: false,
			best_done: None,
		}
	}

	pub(crate) fn validator_set(&self) -> &ValidatorSet<Public> {
		&self.validator_set
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

	pub(crate) fn add_vote(
		&mut self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> VoteImportResult<B> {
		let num = vote.commitment.block_number;
		let vote_key = (vote.id.clone(), num);

		if num < self.session_start || Some(num) <= self.best_done {
			debug!(target: LOG_TARGET, "🥩 received vote for old stale round {:?}, ignoring", num);
			return VoteImportResult::Stale
		} else if vote.commitment.validator_set_id != self.validator_set_id() {
			debug!(
				target: LOG_TARGET,
				"🥩 expected set_id {:?}, ignoring vote {:?}.",
				self.validator_set_id(),
				vote,
			);
			return VoteImportResult::Invalid
		} else if !self.validators().iter().any(|id| &vote.id == id) {
			debug!(
				target: LOG_TARGET,
				"🥩 received vote {:?} from validator that is not in the validator set, ignoring",
				vote
			);
			return VoteImportResult::Invalid
		}

		if let Some(previous_vote) = self.previous_votes.get(&vote_key) {
			// is the same public key voting for a different payload?
			if previous_vote.commitment.payload != vote.commitment.payload {
				debug!(
					target: LOG_TARGET,
					"🥩 detected equivocated vote: 1st: {:?}, 2nd: {:?}", previous_vote, vote
				);
				return VoteImportResult::Equivocation(EquivocationProof {
					first: previous_vote.clone(),
					second: vote,
				})
			}
		} else {
			// this is the first vote sent by `id` for `num`, all good
			self.previous_votes.insert(vote_key, vote.clone());
		}

		// add valid vote
		let round = self.rounds.entry(vote.commitment.clone()).or_default();
		if round.add_vote((vote.id, vote.signature)) &&
			round.is_done(threshold(self.validator_set.len()))
		{
			if let Some(round) = self.rounds.remove_entry(&vote.commitment) {
				return VoteImportResult::RoundConcluded(self.signed_commitment(round))
			}
		}
		VoteImportResult::Ok
	}

	fn signed_commitment(
		&mut self,
		round: (Commitment<NumberFor<B>>, RoundTracker),
	) -> SignedCommitment<NumberFor<B>, Signature> {
		let votes = round.1.votes;
		let signatures = self
			.validators()
			.iter()
			.map(|authority_id| votes.get(authority_id).cloned())
			.collect();
		SignedCommitment { commitment: round.0, signatures }
	}

	pub(crate) fn conclude(&mut self, round_num: NumberFor<B>) {
		// Remove this and older (now stale) rounds.
		self.rounds.retain(|commitment, _| commitment.block_number > round_num);
		self.previous_votes.retain(|&(_, number), _| number > round_num);
		self.mandatory_done = self.mandatory_done || round_num == self.session_start;
		self.best_done = self.best_done.max(Some(round_num));
		debug!(target: LOG_TARGET, "🥩 Concluded round #{}", round_num);
	}
}

#[cfg(test)]
mod tests {
	use sc_network_test::Block;

	use beefy_primitives::{
		crypto::Public, known_payloads::MMR_ROOT_ID, Commitment, EquivocationProof, Keyring,
		Payload, SignedCommitment, ValidatorSet, VoteMessage,
	};

	use super::{threshold, Block as BlockT, RoundTracker, Rounds};
	use crate::round::VoteImportResult;

	impl<B> Rounds<B>
	where
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

		// adding new vote allowed
		assert!(rt.add_vote(bob_vote.clone()));
		// adding existing vote not allowed
		assert!(!rt.add_vote(bob_vote));

		// vote is not done
		assert!(!rt.is_done(threshold));

		let alice_vote = (Keyring::Alice.public(), Keyring::Alice.sign(b"I am committed"));
		// adding new vote (self vote this time) allowed
		assert!(rt.add_vote(alice_vote));

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
		let rounds = Rounds::<Block>::new(session_start, validators);

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
		let validator_set_id = validators.id();

		let session_start = 1u64.into();
		let mut rounds = Rounds::<Block>::new(session_start, validators);

		let payload = Payload::from_single_entry(MMR_ROOT_ID, vec![]);
		let block_number = 1;
		let commitment = Commitment { block_number, payload, validator_set_id };
		let mut vote = VoteMessage {
			id: Keyring::Alice.public(),
			commitment: commitment.clone(),
			signature: Keyring::Alice.sign(b"I am committed"),
		};
		// add 1st good vote
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Ok);

		// double voting (same vote), ok, no effect
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Ok);

		vote.id = Keyring::Dave.public();
		vote.signature = Keyring::Dave.sign(b"I am committed");
		// invalid vote (Dave is not a validator)
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Invalid);

		vote.id = Keyring::Bob.public();
		vote.signature = Keyring::Bob.sign(b"I am committed");
		// add 2nd good vote
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Ok);

		vote.id = Keyring::Charlie.public();
		vote.signature = Keyring::Charlie.sign(b"I am committed");
		// add 3rd good vote -> round concluded -> signatures present
		assert_eq!(
			rounds.add_vote(vote.clone()),
			VoteImportResult::RoundConcluded(SignedCommitment {
				commitment,
				signatures: vec![
					Some(Keyring::Alice.sign(b"I am committed")),
					Some(Keyring::Bob.sign(b"I am committed")),
					Some(Keyring::Charlie.sign(b"I am committed")),
					None,
				]
			})
		);
		rounds.conclude(block_number);

		vote.id = Keyring::Eve.public();
		vote.signature = Keyring::Eve.sign(b"I am committed");
		// Eve is a validator, but round was concluded, adding vote disallowed
		assert_eq!(rounds.add_vote(vote), VoteImportResult::Stale);
	}

	#[test]
	fn old_rounds_not_accepted() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			42,
		)
		.unwrap();
		let validator_set_id = validators.id();

		// active rounds starts at block 10
		let session_start = 10u64.into();
		let mut rounds = Rounds::<Block>::new(session_start, validators);

		// vote on round 9
		let block_number = 9;
		let payload = Payload::from_single_entry(MMR_ROOT_ID, vec![]);
		let commitment = Commitment { block_number, payload, validator_set_id };
		let mut vote = VoteMessage {
			id: Keyring::Alice.public(),
			commitment,
			signature: Keyring::Alice.sign(b"I am committed"),
		};
		// add vote for previous session, should fail
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Stale);
		// no votes present
		assert!(rounds.rounds.is_empty());

		// simulate 11 was concluded
		rounds.best_done = Some(11);
		// add votes for current session, but already concluded rounds, should fail
		vote.commitment.block_number = 10;
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Stale);
		vote.commitment.block_number = 11;
		assert_eq!(rounds.add_vote(vote.clone()), VoteImportResult::Stale);
		// no votes present
		assert!(rounds.rounds.is_empty());

		// add vote for active round 12
		vote.commitment.block_number = 12;
		assert_eq!(rounds.add_vote(vote), VoteImportResult::Ok);
		// good vote present
		assert_eq!(rounds.rounds.len(), 1);
	}

	#[test]
	fn multiple_rounds() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
			Default::default(),
		)
		.unwrap();
		let validator_set_id = validators.id();

		let session_start = 1u64.into();
		let mut rounds = Rounds::<Block>::new(session_start, validators);

		let payload = Payload::from_single_entry(MMR_ROOT_ID, vec![]);
		let commitment = Commitment { block_number: 1, payload, validator_set_id };
		let mut alice_vote = VoteMessage {
			id: Keyring::Alice.public(),
			commitment: commitment.clone(),
			signature: Keyring::Alice.sign(b"I am committed"),
		};
		let mut bob_vote = VoteMessage {
			id: Keyring::Bob.public(),
			commitment: commitment.clone(),
			signature: Keyring::Bob.sign(b"I am committed"),
		};
		let mut charlie_vote = VoteMessage {
			id: Keyring::Charlie.public(),
			commitment,
			signature: Keyring::Charlie.sign(b"I am committed"),
		};
		let expected_signatures = vec![
			Some(Keyring::Alice.sign(b"I am committed")),
			Some(Keyring::Bob.sign(b"I am committed")),
			Some(Keyring::Charlie.sign(b"I am committed")),
		];

		// round 1 - only 2 out of 3 vote
		assert_eq!(rounds.add_vote(alice_vote.clone()), VoteImportResult::Ok);
		assert_eq!(rounds.add_vote(charlie_vote.clone()), VoteImportResult::Ok);
		// should be 1 active round
		assert_eq!(1, rounds.rounds.len());

		// round 2 - only Charlie votes
		charlie_vote.commitment.block_number = 2;
		assert_eq!(rounds.add_vote(charlie_vote.clone()), VoteImportResult::Ok);
		// should be 2 active rounds
		assert_eq!(2, rounds.rounds.len());

		// round 3 - all validators vote -> round is concluded
		alice_vote.commitment.block_number = 3;
		bob_vote.commitment.block_number = 3;
		charlie_vote.commitment.block_number = 3;
		assert_eq!(rounds.add_vote(alice_vote.clone()), VoteImportResult::Ok);
		assert_eq!(rounds.add_vote(bob_vote.clone()), VoteImportResult::Ok);
		assert_eq!(
			rounds.add_vote(charlie_vote.clone()),
			VoteImportResult::RoundConcluded(SignedCommitment {
				commitment: charlie_vote.commitment,
				signatures: expected_signatures
			})
		);
		// should be only 2 active since this one auto-concluded
		assert_eq!(2, rounds.rounds.len());

		// conclude round 2
		rounds.conclude(2);
		// should be no more active rounds since 2 was officially concluded and round "1" is stale
		assert!(rounds.rounds.is_empty());

		// conclude round 3
		rounds.conclude(3);
		assert!(rounds.previous_votes.is_empty());
	}

	#[test]
	fn should_provide_equivocation_proof() {
		sp_tracing::try_init_simple();

		let validators = ValidatorSet::<Public>::new(
			vec![Keyring::Alice.public(), Keyring::Bob.public()],
			Default::default(),
		)
		.unwrap();
		let validator_set_id = validators.id();
		let session_start = 1u64.into();
		let mut rounds = Rounds::<Block>::new(session_start, validators);

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![1, 1, 1, 1]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![2, 2, 2, 2]);
		let commitment1 = Commitment { block_number: 1, payload: payload1, validator_set_id };
		let commitment2 = Commitment { block_number: 1, payload: payload2, validator_set_id };

		let alice_vote1 = VoteMessage {
			id: Keyring::Alice.public(),
			commitment: commitment1,
			signature: Keyring::Alice.sign(b"I am committed"),
		};
		let mut alice_vote2 = alice_vote1.clone();
		alice_vote2.commitment = commitment2;

		let expected_result = VoteImportResult::Equivocation(EquivocationProof {
			first: alice_vote1.clone(),
			second: alice_vote2.clone(),
		});

		// vote on one payload - ok
		assert_eq!(rounds.add_vote(alice_vote1), VoteImportResult::Ok);

		// vote on _another_ commitment/payload -> expected equivocation proof
		assert_eq!(rounds.add_vote(alice_vote2), expected_result);
	}
}
