// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Preimage pallet benchmarking.

use super::*;
use sp_core::Hasher;
use sp_runtime::traits::BlakeTwo256;
use frame_benchmarking::{benchmarks, whitelist_account, account};
use frame_support::ensure;
use frame_system::RawOrigin;
use sp_std::{prelude::*, vec};
use crate::mock::*;

use crate::Pallet as Preimage;
use frame_system::Pallet as System;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	System::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

benchmarks! {
	note_preimage {
		let s in 0 .. T::MaxSize::get();
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let mut preimage = vec![];
		preimage.resize(s as usize, 0);
	}: _(RawOrigin::Signed(caller), preimage)
	verify {
		assert!(Pallet::have_preimage(BlakeTwo256::hash(&preimage[..])));
	}
	impl_benchmark_test_suite!(Preimage, crate::mock::new_test_ext(), crate::mock::Test);
}
