// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg(test)]

use super::Error;
use crate::check_commit_signatures;
use crate::mock::*;
use frame_support::assert_err;
use frame_support::assert_ok;
use sp_core::H256;
use sp_finality_grandpa::accountable_safety::{Query, QueryResponse};
use sp_finality_grandpa::AuthorityId;
use sp_keyring::Ed25519Keyring;

#[test]
fn accountable_safety_start_twice() {
	new_test_ext().execute_with(|| {
		use Ed25519Keyring::{Alice, Bob};
		let round = 42;
		let set_id = 4;
		let hash = H256::random();
		let number = 5;

		let block_not_included = {
			let commit = sp_finality_grandpa::Commit {
				target_hash: hash,
				target_number: number,
				precommits: vec![
					new_precommit(Alice, hash, number, round, set_id),
					new_precommit(Bob, hash, number, round, set_id),
				],
			};
			(commit, round, set_id)
		};

		let round = round + 1;
		let hash = H256::random();
		let number = 6;

		let new_block = {
			let commit = sp_finality_grandpa::Commit {
				target_hash: hash,
				target_number: number,
				precommits: vec![
					new_precommit(Alice, hash, number, round, set_id),
					new_precommit(Bob, hash, number, round, set_id),
				],
			};
			(commit, round, set_id)
		};

		// Fail, since the newer block isn't from a later round
		assert_err!(
			GrandpaAccountableSafety::start_accountable_safety(
				block_not_included.clone(),
				block_not_included.clone()
			),
			Error::<Test>::BlockIsNotFromLaterRound,
		);

		// Success!
		assert_ok!(GrandpaAccountableSafety::start_accountable_safety(
			block_not_included.clone(),
			new_block.clone()
		));

		// ... but we currently don't support running more than one session in parallel
		assert_err!(
			GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block),
			Error::<Test>::SessionAlreadyRunning,
		);
	});
}

#[test]
fn accountable_safety_start_with_invalid_signature() {
	new_test_ext().execute_with(|| {
		use Ed25519Keyring::{Alice, Bob};
		let round = 42;
		let set_id = 4;
		let hash = H256::random();
		let number = 5;

		let block_not_included = {
			let precommit_alice = new_precommit(Alice, hash, number, round, set_id);
			let mut precommit_bob = new_precommit(Bob, H256::random(), number + 1, round, set_id);

			// Overwrite the Precommit, invalidating the signature
			precommit_bob.precommit = new_precommit(Bob, hash, number + 3, round, set_id).precommit;

			let commit = sp_finality_grandpa::Commit {
				target_hash: hash,
				target_number: number,
				precommits: vec![precommit_alice, precommit_bob],
			};
			(commit, round, set_id)
		};

		let new_block = {
			let precommit_alice = new_precommit(Alice, hash, number, round + 1, set_id);
			let precommit_bob = new_precommit(Bob, H256::random(), number + 1, round + 1, set_id);

			let commit = sp_finality_grandpa::Commit {
				target_hash: hash,
				target_number: number,
				precommits: vec![precommit_alice, precommit_bob],
			};
			(commit, round, set_id)
		};

		assert_err!(
			GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block),
			Error::<Test>::InvalidSignature,
		);
	});
}

#[test]
fn accountable_safety_start_with_commits_inverted() {
	new_test_ext().execute_with(|| {
		use Ed25519Keyring::{Alice, Bob};
		let round = 42;
		let set_id = 4;
		let hash = H256::random();
		let number = 5;

		let precommit_alice = new_precommit(Alice, hash, number, round, set_id);
		let precommit_bob = new_precommit(Bob, H256::random(), number + 1, round, set_id);

		let precommits = vec![precommit_alice, precommit_bob];
		let commit = sp_finality_grandpa::Commit {
			target_hash: hash,
			target_number: number,
			precommits,
		};

		// Same block for both, since we are not actually running the protocol in this test
		let block_not_included = (commit.clone(), round.clone(), set_id);
		let new_block = (commit.clone(), round, set_id);

		assert_err!(
			GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block),
			Error::<Test>::BlockIsNotFromLaterRound,
		);
	});
}

#[test]
fn accountable_safety_setup_and_submit_reply() {
	new_test_ext().execute_with(|| {
		use Ed25519Keyring::{Alice, Bob, Charlie};
		let auth = vec![Alice, Bob];
		let pub_ids: Vec<AuthorityId> =
			auth.iter().map(|keyring| keyring.public().into()).collect();
		let round = 42;
		let set_id = 4;

		let commit0 = new_commit(auth.clone(), H256::random(), 5, round, set_id);
		let block_not_included = (commit0.clone(), round.clone(), set_id);

		let commit1 = new_commit(auth.clone(), H256::random(), 6, round + 1, set_id);
		let new_block = (commit1, round + 1, set_id);

		assert!(check_commit_signatures(&block_not_included));
		assert!(check_commit_signatures(&new_block));

		// Start the protocol and check that we are now waiting for replies
		for pub_id in &pub_ids {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(&pub_id),
				None,
			);
		}
		assert_ok!(
			GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block),
		);
		for pub_id in &pub_ids {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(&pub_id),
				Some(Query::WaitingForReply),
			);
		}

		// Also query a voter that is not in the set of recipients.
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(&Charlie.public().into()),
			None,
		);

		// Add response and check that it is registered
		assert_ok!(
			GrandpaAccountableSafety::add_response(
				&pub_ids[0],
				QueryResponse::Precommits(commit0.precommits.clone()),
			),
		);
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(&pub_ids[0]),
			Some(Query::Replied(QueryResponse::Precommits(
				commit0.precommits
			))),
		);
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(&pub_ids[1]),
			Some(Query::WaitingForReply)
		);

		// Also query a voter that is not in the set of recipients, to check that it is not being
		// asked to participate
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(&Charlie.public().into()),
			None,
		);
	});
}

#[test]
fn accountable_safety_proceed_to_previous_round() {
	new_test_ext().execute_with(|| {
		use Ed25519Keyring::{Alice, Bob, Charlie};
		let auth = vec![Alice, Bob, Charlie];
		let pub_ids: Vec<AuthorityId> =
			auth.iter().map(|keyring| keyring.public().into()).collect();
		let round = 42;
		let set_id = 4;

		let commit0 = new_commit(auth.clone(), H256::random(), 5, round, set_id);
		let block_not_included = (commit0.clone(), round.clone(), set_id);

		let commit1 = new_commit(auth.clone(), H256::random(), 6, round + 1, set_id);
		let new_block = (commit1, round + 1, set_id);

		GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block);

		// All authorities submit their replies
		for pub_id in &pub_ids {
			assert_ok!(
				GrandpaAccountableSafety::add_response(
					pub_id,
					QueryResponse::Precommits(commit0.precommits.clone()),
				),
			);
		}

		for pub_id in &pub_ids {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(pub_id),
				Some(Query::Replied(QueryResponse::Precommits(
					commit0.precommits.clone()
				))),
			);
		}

		// With all requested replies submitted, we will now progress to the next state, which is
		// the previous round
		assert_eq!(
			GrandpaAccountableSafety::session().unwrap().current_round,
			43
		);
		GrandpaAccountableSafety::update();
		assert_eq!(
			GrandpaAccountableSafety::session().unwrap().current_round,
			42
		);

		// Again waiting for replies from the requested authorities
		for pub_id in &pub_ids {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(pub_id),
				Some(Query::WaitingForReply),
			);
		}
	});
}
