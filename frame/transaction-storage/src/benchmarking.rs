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

//! Benchmarks for transaction-storage Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, impl_benchmark_test_suite, whitelisted_caller};
use frame_support::traits::{Currency, OnFinalize, OnInitialize};
use frame_system::{EventRecord, Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One, Zero};
use sp_std::*;
use sp_transaction_storage_proof::TransactionStorageProof;

use crate::Pallet as TransactionStorage;

const PROOF: &[u8] = &hex_literal::hex!(
	"
	0104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
	0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
	0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
	0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
	0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
	000000000000000000000000000000014cd0780ffff80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe8
	7d12a3662c4c0080e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb
	13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2
	f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f
	1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f
	3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a47
	8e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cf
	f93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e31
	6a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f
	53cff93f3ca2f3dfe87d12a3662c4c80e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4c8
	0e316a478e2f1fcb13cf22fd0b2dbb54a6f53cff93f3ca2f3dfe87d12a3662c4cbd05807777809a5d7a720ce5f9d9a012
	fbf25e92c30e732dadba8f312b05e02976313ea64d9f807d43bcbf8a3dc2f6b9e957d129e610c06d411e11743062dc1cf
	3ac289390ae4c8008592aa2d915f52941036afbe72bac4ebe7ce186c4ddc53f118e0ddd4decd8cc809a5d7a720ce5f9d9
	a012fbf25e92c30e732dadba8f312b05e02976313ea64d9f807d43bcbf8a3dc2f6b9e957d129e610c06d411e11743062d
	c1cf3ac289390ae4c00809a5d7a720ce5f9d9a012fbf25e92c30e732dadba8f312b05e02976313ea64d9f807d43bcbf8a
	3dc2f6b9e957d129e610c06d411e11743062dc1cf3ac289390ae4c8008592aa2d915f52941036afbe72bac4ebe7ce186c
	4ddc53f118e0ddd4decd8cc809a5d7a720ce5f9d9a012fbf25e92c30e732dadba8f312b05e02976313ea64d9f807d43bc
	bf8a3dc2f6b9e957d129e610c06d411e11743062dc1cf3ac289390ae4c8008592aa2d915f52941036afbe72bac4ebe7ce
	186c4ddc53f118e0ddd4decd8cccd0780ffff8081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb0
	3bdb31008081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253
	515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa139
	8e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5
	f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3a
	a1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2b
	a8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f32
	2d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa
	9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f0
	2f322d3aa1398e0cb03bdb318081b825bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb318081b82
	5bfa9b2ba8f5f253515e7db09eb1ad3d4f02f322d3aa1398e0cb03bdb31cd0780ffff80b4f23ac50c8e67d9b280f2b31a
	5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd1885
	44c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2
	b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd
	188544c5f9b0080b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9
	b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84
	d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e
	67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977aca
	ac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac5
	0c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b89297
	7acaac84d530bd188544c5f9b80b4f23ac50c8e67d9b280f2b31a5707d52b892977acaac84d530bd188544c5f9b104401
	0000
"
);

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	let events = System::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

pub fn run_to_block<T: Config>(n: T::BlockNumber) {
	while frame_system::Pallet::<T>::block_number() < n {
		crate::Pallet::<T>::on_finalize(frame_system::Pallet::<T>::block_number());
		frame_system::Pallet::<T>::on_finalize(frame_system::Pallet::<T>::block_number());
		frame_system::Pallet::<T>::set_block_number(
			frame_system::Pallet::<T>::block_number() + One::one(),
		);
		frame_system::Pallet::<T>::on_initialize(frame_system::Pallet::<T>::block_number());
		crate::Pallet::<T>::on_initialize(frame_system::Pallet::<T>::block_number());
	}
}

benchmarks! {
	store {
		let l in 1 .. MaxTransactionSize::<T>::get();
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(RawOrigin::Signed(caller.clone()), vec![0u8; l as usize])
	verify {
		assert!(!BlockTransactions::<T>::get().is_empty());
		assert_last_event::<T>(Event::Stored(0).into());
	}

	renew {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		TransactionStorage::<T>::store(
			RawOrigin::Signed(caller.clone()).into(),
			vec![0u8; MaxTransactionSize::<T>::get() as usize],
		)?;
		run_to_block::<T>(1u32.into());
	}: _(RawOrigin::Signed(caller.clone()), T::BlockNumber::zero(), 0)
	verify {
		assert_last_event::<T>(Event::Renewed(0).into());
	}

	check_proof_max {
		run_to_block::<T>(1u32.into());
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for _ in 0 .. MaxBlockTransactions::<T>::get() {
			TransactionStorage::<T>::store(
				RawOrigin::Signed(caller.clone()).into(),
				vec![0u8; MaxTransactionSize::<T>::get() as usize],
			)?;
		}
		run_to_block::<T>(StoragePeriod::<T>::get() + T::BlockNumber::one());
		let random_hash = [0u8];
		let mut encoded_proof = PROOF;
		let proof = TransactionStorageProof::decode(&mut encoded_proof).unwrap();
	}: check_proof(RawOrigin::None, proof)
	verify {
		assert_last_event::<T>(Event::ProofChecked.into());
	}
}

impl_benchmark_test_suite!(TransactionStorage, crate::mock::new_test_ext(), crate::mock::Test,);
