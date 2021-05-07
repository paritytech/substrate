// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for transction-storage pallet.

use super::*;
use crate::mock::*;
use super::Pallet as TransactionStorage;
use frame_support::{assert_ok, assert_noop};
use frame_system::RawOrigin;
use sp_transaction_storage_proof::registration::build_proof;

#[test]
fn discards_data() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller.clone()).into(),
			vec![0u8; 2000 as usize]
		));
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller.clone()).into(),
			vec![0u8; 2000 as usize]
		));
		run_to_block(11);
		assert!(TransactionRoots::<Test>::get(1, 0).is_some());
		assert!(TransactionRoots::<Test>::get(1, 1).is_some());
		assert!(TransactionRoots::<Test>::get(1, 2).is_none());
		assert_eq!(TransactionCount::<Test>::get(1), 2);
		run_to_block(12);
		assert!(TransactionRoots::<Test>::get(1, 0).is_none());
		assert!(TransactionRoots::<Test>::get(1, 1).is_none());
		assert_eq!(TransactionCount::<Test>::get(1), 0);
	});
}

#[test]
fn burns_fee() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		let caller = 1;
		assert_noop!(TransactionStorage::<Test>::store(
				RawOrigin::Signed(5).into(),
				vec![0u8; 2000 as usize]
			),
			Error::<Test>::InsufficientFunds,
		);
		assert_ok!(TransactionStorage::<Test>::store(
				RawOrigin::Signed(caller.clone()).into(),
				vec![0u8; 2000 as usize]
		));
		assert_eq!(Balances::free_balance(1), 1_000_000_000 - 2000 * 2);
	});
}

#[test]
fn checks_proof() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller.clone()).into(),
			vec![0u8; MAX_DATA_SIZE as usize]
		));
		run_to_block(10);
		let parent_hash = <frame_system::Pallet<Test>>::parent_hash();
		let proof = build_proof(
			parent_hash.as_ref(),
			vec![vec![0u8; MAX_DATA_SIZE as usize]]
		).unwrap();
		assert_noop!(TransactionStorage::<Test>::check_proof(
				Origin::none(),
				Some(proof),
			),
			Error::<Test>::UnexpectedProof,
		);
		run_to_block(11);
		let parent_hash = <frame_system::Pallet<Test>>::parent_hash();
		let proof = build_proof(
			parent_hash.as_ref(),
			vec![vec![0u8; MAX_DATA_SIZE as usize]]
		).unwrap();
		assert_ok!(TransactionStorage::<Test>::check_proof(Origin::none(), Some(proof)));
		let invalid_proof = build_proof(
			parent_hash.as_ref(),
			vec![vec![0u8; 1000]]
		).unwrap();
		assert_noop!(TransactionStorage::<Test>::check_proof(
				Origin::none(),
				Some(invalid_proof),
			),
			Error::<Test>::InvalidProof,
		);
	});
}

#[test]
fn renews_data() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
				RawOrigin::Signed(caller.clone()).into(),
				vec![0u8; 2000 as usize]
		));
		let info = TransactionRoots::<Test>::get(1, 0).unwrap();
		run_to_block(6);
		assert_ok!(TransactionStorage::<Test>::renew(
				RawOrigin::Signed(caller.clone()).into(),
				1, // block
				0, // transaction
		));
		assert_eq!(Balances::free_balance(1), 1_000_000_000 - 4000 * 2);
		run_to_block(16);
		assert!(TransactionRoots::<Test>::get(1, 0).is_none());
		assert_eq!(TransactionRoots::<Test>::get(6, 0), Some(info));
		run_to_block(17);
		assert!(TransactionRoots::<Test>::get(6, 0).is_none());
	});
}

