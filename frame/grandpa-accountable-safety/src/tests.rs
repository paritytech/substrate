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

use crate::check_commit_signatures;
use crate::mock::*;
use sp_core::H256;
use sp_finality_grandpa::accountable_safety::{Query, QueryResponse};
use sp_keyring::Ed25519Keyring;

#[test]
fn accountable_safety_setup_and_submit_reply() {
	new_test_ext().execute_with(|| {
		let authorities = vec![
			Ed25519Keyring::Alice,
			Ed25519Keyring::Bob,
			Ed25519Keyring::Charlie,
		];
		let alice = &authorities[0].public().into();
		let round = 42;
		let set_id = 4;
		let commit = new_commit(authorities.clone(), H256::random(), 5, round, set_id);
		let block_not_included = (commit.clone(), round.clone(), set_id);
		let new_block = (commit.clone(), round, set_id);

		assert!(check_commit_signatures(&block_not_included));

		// Start the protocol and check that we are now waiting for replies
		assert_eq!(GrandpaAccountableSafety::query_state_for_voter(alice), None);
		GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block);
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(alice),
			Some(Query::WaitingForReply)
		);

		// Add response and check that it is registered
		GrandpaAccountableSafety::add_response(
			alice,
			QueryResponse::Precommits(commit.precommits.clone()),
		);
		assert_eq!(
			GrandpaAccountableSafety::query_state_for_voter(alice),
			Some(Query::Replied(QueryResponse::Precommits(commit.precommits))),
		);
	});
}

#[test]
fn accountable_safety_proceed_to_previous_round() {
	new_test_ext().execute_with(|| {
		let authorities = vec![
			Ed25519Keyring::Alice,
			Ed25519Keyring::Bob,
			Ed25519Keyring::Charlie,
		];

		let round = 42;
		let set_id = 4;
		let commit = new_commit(authorities.clone(), H256::random(), 5, round, set_id);
		let block_not_included = (commit.clone(), round.clone(), set_id);
		let new_block = (commit.clone(), round, set_id);

		GrandpaAccountableSafety::start_accountable_safety(block_not_included, new_block);

		// All authorities submit their replies
		for authority in &authorities {
			GrandpaAccountableSafety::add_response(
				&authority.public().into(),
				QueryResponse::Precommits(commit.precommits.clone()),
			);
		}

		for authority in &authorities {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(&authority.public().into()),
				Some(Query::Replied(QueryResponse::Precommits(
					commit.precommits.clone()
				))),
			);
		}

		// With all requested replies submitted, we will now progress to the previous round
		assert_eq!(
			GrandpaAccountableSafety::session().unwrap().current_round,
			42
		);
		GrandpaAccountableSafety::update();
		assert_eq!(
			GrandpaAccountableSafety::session().unwrap().current_round,
			41
		);

		// Again waiting for replies from the requested authorities
		for authority in &authorities {
			assert_eq!(
				GrandpaAccountableSafety::query_state_for_voter(&authority.public().into()),
				Some(Query::WaitingForReply),
			);
		}
	});
}
