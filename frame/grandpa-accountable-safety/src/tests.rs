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

use crate::{self as pallet_grandpa_accountable_safety, check_commit_signatures};
use frame_support::parameter_types;
use sp_core::H256;
use sp_finality_grandpa::{
	accountable_safety::{Query, QueryResponse},
	AuthorityId, AuthoritySignature, Commit, RoundNumber, SetId,
};
use sp_keyring::Ed25519Keyring;
use sp_runtime::{testing::Header, traits::IdentityLookup};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		GrandpaAccountableSafety: pallet_grandpa_accountable_safety::{Pallet, Event},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}

impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u128>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}

parameter_types! {
	pub const BlockTimeout: u64 = 10;
}

impl crate::Config for Test {
	type Event = Event;
	type BlockTimeout = BlockTimeout;
}

fn new_test_ext() -> sp_io::TestExternalities {
	let storage = frame_system::GenesisConfig::default()
		.build_storage::<Test>()
		.unwrap();

	storage.into()
}

fn create_precommits(
	target_hash: H256,
	target_number: u64,
	round: RoundNumber,
	set_id: SetId,
	authorities: Vec<Ed25519Keyring>,
) -> Vec<grandpa::SignedPrecommit<H256, RoundNumber, AuthoritySignature, AuthorityId>> {
	let mut precommits = Vec::new();
	for keyring in authorities {
		let precommit = grandpa::Precommit {
			target_hash,
			target_number,
		};
		let msg = grandpa::Message::Precommit(precommit.clone());
		let encoded = sp_finality_grandpa::localized_payload(round, set_id, &msg);
		let signature = keyring.sign(&encoded[..]).into();
		let signed_precommit = grandpa::SignedPrecommit {
			precommit,
			signature,
			id: keyring.public().into(),
		};
		precommits.push(signed_precommit);
	}
	precommits
}

fn create_commit(
	target_hash: H256,
	target_number: u64,
	round: RoundNumber,
	set_id: SetId,
	authorities: Vec<Ed25519Keyring>,
) -> Commit<H256, RoundNumber> {
	sp_finality_grandpa::Commit {
		target_hash,
		target_number,
		precommits: create_precommits(target_hash, target_number, round, set_id, authorities),
	}
}

#[test]
fn verify_commit_signatures() {
	let authorities = vec![
		Ed25519Keyring::Alice,
		Ed25519Keyring::Bob,
		Ed25519Keyring::Charlie,
	];
	let round = 42;
	let set_id = 4;
	let commit = create_commit(H256::random(), 5, round, set_id, authorities);
	assert!(check_commit_signatures(&(commit, round, set_id)));
}

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
		let commit = create_commit(H256::random(), 5, round, set_id, authorities.clone());
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
		let commit = create_commit(H256::random(), 5, round, set_id, authorities.clone());
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
