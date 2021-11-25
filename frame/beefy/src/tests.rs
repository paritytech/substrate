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

use std::vec;

use beefy_primitives::ValidatorSet;
use codec::Encode;

use sp_runtime::DigestItem;

use frame_support::traits::OnInitialize;

use crate::mock::*;

fn init_block(block: u64) {
	System::set_block_number(block);
	Session::on_initialize(block);
}

pub fn beefy_log(log: ConsensusLog<BeefyId>) -> DigestItem {
	DigestItem::Consensus(BEEFY_ENGINE_ID, log.encode())
}

#[test]
fn genesis_session_initializes_authorities() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let authorities = Beefy::authorities();

		assert!(authorities.len() == 2);
		assert_eq!(want[0], authorities[0]);
		assert_eq!(want[1], authorities[1]);

		assert!(Beefy::validator_set_id() == 0);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);
	});
}

#[test]
fn session_change_updates_authorities() {
	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		init_block(1);

		assert!(0 == Beefy::validator_set_id());

		// no change - no log
		assert!(System::digest().logs.is_empty());

		init_block(2);

		assert!(1 == Beefy::validator_set_id());

		let want = beefy_log(ConsensusLog::AuthoritiesChange(ValidatorSet {
			validators: vec![mock_beefy_id(3), mock_beefy_id(4)],
			id: 1,
		}));

		let log = System::digest().logs[0].clone();

		assert_eq!(want, log);
	});
}

#[test]
fn session_change_updates_next_authorities() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		init_block(1);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);

		init_block(2);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[2], next_authorities[0]);
		assert_eq!(want[3], next_authorities[1]);
	});
}

#[test]
fn validator_set_at_genesis() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let vs = Beefy::validator_set();

		assert_eq!(vs.id, 0u64);
		assert_eq!(vs.validators[0], want[0]);
		assert_eq!(vs.validators[1], want[1]);
	});
}

#[test]
fn validator_set_updates_work() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		init_block(1);

		let vs = Beefy::validator_set();

		assert_eq!(vs.id, 0u64);
		assert_eq!(want[0], vs.validators[0]);
		assert_eq!(want[1], vs.validators[1]);

		init_block(2);

		let vs = Beefy::validator_set();

		assert_eq!(vs.id, 1u64);
		assert_eq!(want[2], vs.validators[0]);
		assert_eq!(want[3], vs.validators[1]);
	});
}
