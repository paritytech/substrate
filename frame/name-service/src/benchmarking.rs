// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Name Service Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::{types::*, *};
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, Get, OnFinalize, OnInitialize};
use frame_system::{pallet_prelude::OriginFor, Pallet as System, RawOrigin};
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{AtLeast32BitUnsigned, One, Saturating};
use sp_std::vec;

use crate::Pallet as NameService;
const SEED: u32 = 1;

fn run_to_block<T: Config>(n: T::BlockNumber) {
	while System::<T>::block_number() < n {
		NameService::<T>::on_finalize(System::<T>::block_number());
		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		NameService::<T>::on_initialize(System::<T>::block_number());
	}
}
/*
fn commit_setup<T: Config>() -> (caller: OriginFor<T>, acc: T::AccountId, hash: CommitmentHash {


}*/

benchmarks! {
	where_clause { where T::BlockNumber: From<u32> }

	commit {
		let mut balance = T::Currency::minimum_balance();
		balance = balance.saturating_mul(balance);	// TODO
		let caller = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, balance);

		let hash: CommitmentHash = Default::default();
		let acc: T::AccountId = account("recipient", 0, SEED);

	}: _(RawOrigin::Signed(caller), acc, hash)

	reveal {
		let l in 3..100_000; // TODO limit

		// Fund the account
		let mut balance = T::Currency::minimum_balance();
		balance = balance.saturating_mul(balance);	// TODO
		balance = balance.saturating_mul(balance);	// TODO
		let caller = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, balance);

		let name = vec![0; l as usize];
		let secret = 3_u64;

		// Commit
		let hash: CommitmentHash = NameService::<T>::commitment_hash(&name, secret);
		let acc: T::AccountId = account("recipient", 0, SEED);
		let origin = RawOrigin::Signed(caller.clone());
		NameService::<T>::commit(origin.into(), acc, hash).expect("Must commit");

		let periods: T::BlockNumber = Default::default();
		let run_to: T::BlockNumber = 100u32.into();
		run_to_block::<T>(run_to);

	}: _(RawOrigin::Signed(caller), name.to_vec(), secret, periods)


	impl_benchmark_test_suite!(NameService, crate::mock::new_test_ext(), crate::mock::Test);
}
