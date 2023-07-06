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

//! Benchmarks for the name service pallet.

#![cfg(feature = "runtime-benchmarks")]
#![cfg_attr(not(feature = "std"), no_std)]

use super::{types::*, *};
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, Get};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One};
use sp_std::vec;
// use sp_io::hashing::blake2_256;
use crate::Pallet as NameService;

type CurrencyOf<T> = <T as Config>::Currency;

const SEED: u32 = 1;

fn run_to_block<T: Config>(n: T::BlockNumber) {
	while System::<T>::block_number() < n {
		NameService::<T>::on_finalize(System::<T>::block_number());
		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		NameService::<T>::on_initialize(System::<T>::block_number());
	}
}

benchmarks! {
	commit {
		let balance = BalanceOf::<T>::max_value();
		let caller = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, balance);

		let l in 3..T::MaxNameLength::get();
		let name = vec![0; l as usize];
		let secret = 3_u64;
		let hash = NameService::<T>::commitment_hash(&name, secret.clone());
		let owner: T::AccountId = account("recipient", 0, SEED);

	}: _(RawOrigin::Signed(caller.clone()), owner, hash.clone())
	verify {
		// commitment is now being stored.
		assert!(Commitments::<T>::contains_key(hash));
	}

	reveal {
		let l in 3..T::MaxNameLength::get();

		// Fund the account
		let balance = BalanceOf::<T>::max_value();
		let caller = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, balance);

		let name = vec![0; l as usize];
		let secret = 3_u64;

		// Commit
		let hash: CommitmentHash = NameService::<T>::commitment_hash(&name, secret);
		let owner: T::AccountId = account("recipient", 0, SEED);
		let origin = RawOrigin::Signed(caller.clone());
		NameService::<T>::commit(origin.into(), owner.clone(), hash.clone()).expect("Must commit");
		let run_to: T::BlockNumber = 100u32.into();
		run_to_block::<T>(run_to);

	}: _(RawOrigin::Signed(caller.clone()), name.to_vec(), secret, 100u32.into())
	verify {
		// commitment has been removed.
		assert!(!Commitments::<T>::contains_key(hash));
		// registered name is now stored.
		assert_eq!(Registrations::<T>::get(NameService::<T>::name_hash(&name)).unwrap(), Registration {
			owner: owner.clone(), expiry: Some(200u32.into()), deposit: None
		});
		// fees have been deducted from fee payer.
		assert_eq!(CurrencyOf::<T>::free_balance(&caller), BalanceOf::<T>::max_value()-100u32.into());
	}

	impl_benchmark_test_suite!(NameService, crate::mock::new_test_ext(), crate::mock::Test);
}
