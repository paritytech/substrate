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

//! Benchmarks for Sudo Pallet

use super::*;
use crate::Pallet;
use frame_benchmarking::v2::*;
use frame_system::RawOrigin;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

#[benchmarks( where <T as Config>::RuntimeCall: From<frame_system::Call<T>>)]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn set_key() {
		let caller: T::AccountId = whitelisted_caller();
		Key::<T>::put(caller.clone());

		let new_sudoer: T::AccountId = account("sudoer", 0, SEED);
		let new_sudoer_lookup = T::Lookup::unlookup(new_sudoer.clone());

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), new_sudoer_lookup);

		assert_last_event::<T>(Event::KeyChanged { old_sudoer: Some(caller) }.into());
	}

	#[benchmark]
	fn sudo() {
		let caller: T::AccountId = whitelisted_caller();
		Key::<T>::put(caller.clone());

		let call: <T as Config>::RuntimeCall = frame_system::Call::remark { remark: vec![] }.into();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), Box::new(call.clone()));

		assert_last_event::<T>(Event::Sudid { sudo_result: Ok(()) }.into())
	}

	#[benchmark]
	fn sudo_as() {
		let caller: T::AccountId = whitelisted_caller();
		Key::<T>::put(caller.clone());

		let call: <T as Config>::RuntimeCall = frame_system::Call::remark { remark: vec![] }.into();

		let who: T::AccountId = account("as", 0, SEED);
		let who_lookup = T::Lookup::unlookup(who.clone());

		#[extrinsic_call]
		_(RawOrigin::Signed(caller), who_lookup, Box::new(call.clone()));

		assert_last_event::<T>(Event::SudoAsDone { sudo_result: Ok(()) }.into())
	}

	impl_benchmark_test_suite!(Pallet, crate::mock::new_bench_ext(), crate::mock::Test);
}
