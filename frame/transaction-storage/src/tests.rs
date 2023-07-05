// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::{Pallet as TransactionStorage, *};
use crate::mock::*;
use frame_support::{assert_noop, assert_ok};
use frame_system::RawOrigin;
use sp_transaction_storage_proof::registration::build_proof;

const MAX_DATA_SIZE: u32 = DEFAULT_MAX_TRANSACTION_SIZE;

#[test]
fn discards_data() {
	new_test_ext().execute_with(|| {
		run_to_block(1, || None);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller).into(),
			vec![0u8; 2000 as usize]
		));
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller).into(),
			vec![0u8; 2000 as usize]
		));
		let proof_provider = || {
			let block_num = <frame_system::Pallet<Test>>::block_number();
			if block_num == 11 {
				let parent_hash = <frame_system::Pallet<Test>>::parent_hash();
				Some(
					build_proof(parent_hash.as_ref(), vec![vec![0u8; 2000], vec![0u8; 2000]])
						.unwrap(),
				)
			} else {
				None
			}
		};
		run_to_block(11, proof_provider);
		assert!(Transactions::<Test>::get(1).is_some());
		let transctions = Transactions::<Test>::get(1).unwrap();
		assert_eq!(transctions.len(), 2);
		assert_eq!(ChunkCount::<Test>::get(1), 16);
		run_to_block(12, proof_provider);
		assert!(Transactions::<Test>::get(1).is_none());
		assert_eq!(ChunkCount::<Test>::get(1), 0);
	});
}

#[test]
fn burns_fee() {
	new_test_ext().execute_with(|| {
		run_to_block(1, || None);
		let caller = 1;
		assert_noop!(
			TransactionStorage::<Test>::store(
				RawOrigin::Signed(5).into(),
				vec![0u8; 2000 as usize]
			),
			Error::<Test>::InsufficientFunds,
		);
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller).into(),
			vec![0u8; 2000 as usize]
		));
		assert_eq!(Balances::free_balance(1), 1_000_000_000 - 2000 * 2 - 200);
	});
}

#[test]
fn checks_proof() {
	new_test_ext().execute_with(|| {
		run_to_block(1, || None);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller).into(),
			vec![0u8; MAX_DATA_SIZE as usize]
		));
		run_to_block(10, || None);
		let parent_hash = <frame_system::Pallet<Test>>::parent_hash();
		let proof =
			build_proof(parent_hash.as_ref(), vec![vec![0u8; MAX_DATA_SIZE as usize]]).unwrap();
		assert_noop!(
			TransactionStorage::<Test>::check_proof(RuntimeOrigin::none(), proof,),
			Error::<Test>::UnexpectedProof,
		);
		run_to_block(11, || None);
		let parent_hash = <frame_system::Pallet<Test>>::parent_hash();

		let invalid_proof = build_proof(parent_hash.as_ref(), vec![vec![0u8; 1000]]).unwrap();
		assert_noop!(
			TransactionStorage::<Test>::check_proof(RuntimeOrigin::none(), invalid_proof,),
			Error::<Test>::InvalidProof,
		);

		let proof =
			build_proof(parent_hash.as_ref(), vec![vec![0u8; MAX_DATA_SIZE as usize]]).unwrap();
		assert_ok!(TransactionStorage::<Test>::check_proof(RuntimeOrigin::none(), proof));
	});
}

#[test]
fn renews_data() {
	new_test_ext().execute_with(|| {
		run_to_block(1, || None);
		let caller = 1;
		assert_ok!(TransactionStorage::<Test>::store(
			RawOrigin::Signed(caller).into(),
			vec![0u8; 2000]
		));
		let info = BlockTransactions::<Test>::get().last().unwrap().clone();
		run_to_block(6, || None);
		assert_ok!(TransactionStorage::<Test>::renew(
			RawOrigin::Signed(caller).into(),
			1, // block
			0, // transaction
		));
		assert_eq!(Balances::free_balance(1), 1_000_000_000 - 4000 * 2 - 200 * 2);
		let proof_provider = || {
			let block_num = <frame_system::Pallet<Test>>::block_number();
			if block_num == 11 || block_num == 16 {
				let parent_hash = <frame_system::Pallet<Test>>::parent_hash();
				Some(build_proof(parent_hash.as_ref(), vec![vec![0u8; 2000]]).unwrap())
			} else {
				None
			}
		};
		run_to_block(16, proof_provider);
		assert!(Transactions::<Test>::get(1).is_none());
		assert_eq!(Transactions::<Test>::get(6).unwrap().get(0), Some(info).as_ref());
		run_to_block(17, proof_provider);
		assert!(Transactions::<Test>::get(6).is_none());
	});
}
