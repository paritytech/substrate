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

// Benchmarks for Gilt Pallet

#![cfg(feature = "runtime-benchmarks")]

use sp_std::prelude::*;
use super::*;
use sp_runtime::traits::Bounded;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller, impl_benchmark_test_suite};
use frame_support::traits::Currency;

use crate::Pallet as Gilt;

const SEED: u32 = 0;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

benchmarks! {
	place_bid {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(RawOrigin::Signed(caller.clone()), BalanceOf::<T>::max_value(), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (1, BalanceOf::<T>::max_value()));
	}
}

impl_benchmark_test_suite!(
	Gilt,
	crate::mock::new_test_ext(),
	crate::mock::Test,
);
