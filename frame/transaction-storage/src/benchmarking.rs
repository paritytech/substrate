// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, OnFinalize, OnInitialize};
use frame_system::{EventRecord, Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One, Zero};
use sp_std::*;
use sp_transaction_storage_proof::TransactionStorageProof;

use crate::Pallet as TransactionStorage;

// Proof generated from max size storage:
// ```
// let mut transactions = Vec::new();
// let tx_size = DEFAULT_MAX_TRANSACTION_SIZE;
// for _ in 0..DEFAULT_MAX_BLOCK_TRANSACTIONS {
//   transactions.push(vec![0; tx_size]);
// }
// let hash = vec![0; 32];
// build_proof(hash.as_slice(), transactions).unwrap().encode()
// ```
// while hardforcing target chunk key in `build_proof` to [22, 21, 1, 0].
const PROOF: &[u8] = &hex_literal::hex!(
	"
		0104000000000000000000000000000000000000000000000000000000000000000000000000
		0000000000000000000000000000000000000000000000000000000000000000000000000000
		0000000000000000000000000000000000000000000000000000000000000000000000000000
		0000000000000000000000000000000000000000000000000000000000000000000000000000
		0000000000000000000000000000000000000000000000000000000000000000000000000000
		0000000000000000000000000000000000000000000000000000000000000000000000000000
		00000000000000000000000000000000000000000000000000000000000014cd0780ffff8030
		2eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba0080302eb0a6d2
		f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15
		f1e729d1c1004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1
		004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e304
		8cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697
		eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a
		30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba80302e
		b0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b
		834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e7
		29d1c1004657e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c10046
		57e3048cf206d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf2
		06d697eeb153f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb1
		53f61a30ba80302eb0a6d2f63b834d15f1e729d1c1004657e3048cf206d697eeb153f61a30ba
		bd058077778010fd81bc1359802f0b871aeb95e4410a8ec92b93af10ea767a2027cf4734e8de
		808da338e6b722f7bf2051901bd5bccee5e71d5cf6b1faff338ad7120b0256c28380221ce17f
		19117affa96e077905fe48a99723a065969c638593b7d9ab57b538438010fd81bc1359802f0b
		871aeb95e4410a8ec92b93af10ea767a2027cf4734e8de808da338e6b722f7bf2051901bd5bc
		cee5e71d5cf6b1faff338ad7120b0256c283008010fd81bc1359802f0b871aeb95e4410a8ec9
		2b93af10ea767a2027cf4734e8de808da338e6b722f7bf2051901bd5bccee5e71d5cf6b1faff
		338ad7120b0256c28380221ce17f19117affa96e077905fe48a99723a065969c638593b7d9ab
		57b538438010fd81bc1359802f0b871aeb95e4410a8ec92b93af10ea767a2027cf4734e8de80
		8da338e6b722f7bf2051901bd5bccee5e71d5cf6b1faff338ad7120b0256c28380221ce17f19
		117affa96e077905fe48a99723a065969c638593b7d9ab57b53843cd0780ffff804509f59593
		fd47b1a97189127ba65a5649cfb0346637f9836e155eaf891a939c00804509f59593fd47b1a9
		7189127ba65a5649cfb0346637f9836e155eaf891a939c804509f59593fd47b1a97189127ba6
		5a5649cfb0346637f9836e155eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb0
		346637f9836e155eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb0346637f983
		6e155eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb0346637f9836e155eaf89
		1a939c804509f59593fd47b1a97189127ba65a5649cfb0346637f9836e155eaf891a939c8045
		09f59593fd47b1a97189127ba65a5649cfb0346637f9836e155eaf891a939c804509f59593fd
		47b1a97189127ba65a5649cfb0346637f9836e155eaf891a939c804509f59593fd47b1a97189
		127ba65a5649cfb0346637f9836e155eaf891a939c804509f59593fd47b1a97189127ba65a56
		49cfb0346637f9836e155eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb03466
		37f9836e155eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb0346637f9836e15
		5eaf891a939c804509f59593fd47b1a97189127ba65a5649cfb0346637f9836e155eaf891a93
		9c804509f59593fd47b1a97189127ba65a5649cfb0346637f9836e155eaf891a939ccd0780ff
		ff8078916e776c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e
		776c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea
		05e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea05e958559f
		015c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea05e958559f015c082d9d
		06feafa3610fc44a5b2ef543cb81008078916e776c64ccea05e958559f015c082d9d06feafa3
		610fc44a5b2ef543cb818078916e776c64ccea05e958559f015c082d9d06feafa3610fc44a5b
		2ef543cb818078916e776c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef543cb81
		8078916e776c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e77
		6c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea05
		e958559f015c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea05e958559f01
		5c082d9d06feafa3610fc44a5b2ef543cb818078916e776c64ccea05e958559f015c082d9d06
		feafa3610fc44a5b2ef543cb818078916e776c64ccea05e958559f015c082d9d06feafa3610f
		c44a5b2ef543cb818078916e776c64ccea05e958559f015c082d9d06feafa3610fc44a5b2ef5
		43cb811044010000
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
		assert_last_event::<T>(Event::Stored { index: 0 }.into());
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
		assert_last_event::<T>(Event::Renewed { index: 0 }.into());
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
		let mut encoded_proof = PROOF;
		let proof = TransactionStorageProof::decode(&mut encoded_proof).unwrap();
	}: check_proof(RawOrigin::None, proof)
	verify {
		assert_last_event::<T>(Event::ProofChecked.into());
	}

	impl_benchmark_test_suite!(TransactionStorage, crate::mock::new_test_ext(), crate::mock::Test);
}
