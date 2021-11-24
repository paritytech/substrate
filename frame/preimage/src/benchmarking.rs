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
use sp_std::{prelude::*, vec};
use sp_runtime::traits::Bounded;
use frame_benchmarking::{benchmarks, whitelist_account, account};
use frame_system::RawOrigin;
use frame_support::{assert_ok};

use crate::Pallet as Preimage;
use frame_system::Pallet as System;

const SEED: u32 = 0;

#[allow(dead_code)]
fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	System::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

fn preimage_and_hash<T: Config>() -> (Vec<u8>, T::Hash) {
	sized_preimage_and_hash::<T>(T::MaxSize::get())
}

fn sized_preimage_and_hash<T: Config>(size: u32) -> (Vec<u8>, T::Hash) {
	let mut preimage = vec![];
	preimage.resize(size as usize, 0);
	let hash = <T as frame_system::Config>::Hashing::hash(&preimage[..]);
	(preimage, hash)
}

benchmarks! {
	note_preimage {
		let s in 0 .. T::MaxSize::get();
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = sized_preimage_and_hash::<T>(s);
	}: _(RawOrigin::Signed(caller), preimage)
	verify {
		assert!(Preimage::<T>::have_preimage(&hash));
	}
	note_requested_preimage {
		let s in 0 .. T::MaxSize::get();
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = sized_preimage_and_hash::<T>(s);
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash.clone()));
	}: note_preimage(RawOrigin::Signed(caller), preimage)
	verify {
		assert!(Preimage::<T>::have_preimage(&hash));
	}
	unnote_preimage {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::note_preimage(RawOrigin::Signed(caller.clone()).into(), preimage));
	}: _(RawOrigin::Signed(caller), hash.clone())
	verify {
		assert!(!Preimage::<T>::have_preimage(&hash));
	}
	request_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		let noter = funded_account::<T>("noter", 0);
		whitelist_account!(noter);
		// Must be a normal account to force the unreserve operation during request_preimage.
		assert_ok!(Preimage::<T>::note_preimage(RawOrigin::Signed(noter).into(), preimage));
	}: _<T::Origin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), Some(RequestStatus::Requested(1)));
	}
	request_unnoted_preimage {
		let (_, hash) = preimage_and_hash::<T>();
	}: request_preimage<T::Origin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), Some(RequestStatus::Requested(1)));
	}
	unrequest_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash.clone()));
		let noter = funded_account::<T>("noter", 0);
		whitelist_account!(noter);
		// Must be a normal account to force it to become unnoted during unrequest_preimage.
		assert_ok!(Preimage::<T>::note_preimage(RawOrigin::Signed(noter).into(), preimage));
	}: _<T::Origin>(T::ManagerOrigin::successful_origin(), hash.clone())
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), None);
	}
	unrequest_unnoted_preimage {
		let (_, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash.clone()));
	}: unrequest_preimage<T::Origin>(T::ManagerOrigin::successful_origin(), hash.clone())
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), None);
	}

	impl_benchmark_test_suite!(Preimage, crate::mock::new_test_ext(), crate::mock::Test);
}
