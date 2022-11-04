// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use frame_benchmarking::{account, benchmarks, whitelist_account};
use frame_support::assert_ok;
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded;
use sp_std::{prelude::*, vec};

use crate::Pallet as Preimage;

const SEED: u32 = 0;

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

fn preimage_and_hash<T: Config>() -> (Vec<u8>, T::Hash) {
	sized_preimage_and_hash::<T>(MAX_SIZE)
}

fn sized_preimage_and_hash<T: Config>(size: u32) -> (Vec<u8>, T::Hash) {
	let mut preimage = vec![];
	preimage.resize(size as usize, 0);
	let hash = <T as frame_system::Config>::Hashing::hash(&preimage[..]);
	(preimage, hash)
}

benchmarks! {
	// Expensive note - will reserve.
	note_preimage {
		let s in 0 .. MAX_SIZE;
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = sized_preimage_and_hash::<T>(s);
	}: _(RawOrigin::Signed(caller), preimage)
	verify {
		assert!(Preimage::<T>::have_preimage(&hash));
	}
	// Cheap note - will not reserve since it was requested.
	note_requested_preimage {
		let s in 0 .. MAX_SIZE;
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = sized_preimage_and_hash::<T>(s);
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
	}: note_preimage(RawOrigin::Signed(caller), preimage)
	verify {
		assert!(Preimage::<T>::have_preimage(&hash));
	}
	// Cheap note - will not reserve since it's the manager.
	note_no_deposit_preimage {
		let s in 0 .. MAX_SIZE;
		let (preimage, hash) = sized_preimage_and_hash::<T>(s);
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
	}: note_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), preimage)
	verify {
		assert!(Preimage::<T>::have_preimage(&hash));
	}

	// Expensive unnote - will unreserve.
	unnote_preimage {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::note_preimage(RawOrigin::Signed(caller.clone()).into(), preimage));
	}: _(RawOrigin::Signed(caller), hash)
	verify {
		assert!(!Preimage::<T>::have_preimage(&hash));
	}
	// Cheap unnote - will not unreserve since there's no deposit held.
	unnote_no_deposit_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::note_preimage(T::ManagerOrigin::successful_origin(), preimage));
	}: unnote_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		assert!(!Preimage::<T>::have_preimage(&hash));
	}

	// Expensive request - will unreserve the noter's deposit.
	request_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		let noter = funded_account::<T>("noter", 0);
		whitelist_account!(noter);
		assert_ok!(Preimage::<T>::note_preimage(RawOrigin::Signed(noter.clone()).into(), preimage));
	}: _<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		let deposit = T::BaseDeposit::get() + T::ByteDeposit::get() * MAX_SIZE.into();
		let s = RequestStatus::Requested { deposit: Some((noter, deposit)), count: 1, len: Some(MAX_SIZE) };
		assert_eq!(StatusFor::<T>::get(&hash), Some(s));
	}
	// Cheap request - would unreserve the deposit but none was held.
	request_no_deposit_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::note_preimage(T::ManagerOrigin::successful_origin(), preimage));
	}: request_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		let s = RequestStatus::Requested { deposit: None, count: 2, len: Some(MAX_SIZE) };
		assert_eq!(StatusFor::<T>::get(&hash), Some(s));
	}
	// Cheap request - the preimage is not yet noted, so deposit to unreserve.
	request_unnoted_preimage {
		let (_, hash) = preimage_and_hash::<T>();
	}: request_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		let s = RequestStatus::Requested { deposit: None, count: 1, len: None };
		assert_eq!(StatusFor::<T>::get(&hash), Some(s));
	}
	// Cheap request - the preimage is already requested, so just a counter bump.
	request_requested_preimage {
		let (_, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
	}: request_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		let s = RequestStatus::Requested { deposit: None, count: 2, len: None };
		assert_eq!(StatusFor::<T>::get(&hash), Some(s));
	}

	// Expensive unrequest - last reference and it's noted, so will destroy the preimage.
	unrequest_preimage {
		let (preimage, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
		assert_ok!(Preimage::<T>::note_preimage(T::ManagerOrigin::successful_origin(), preimage));
	}: _<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), None);
	}
	// Cheap unrequest - last reference, but it's not noted.
	unrequest_unnoted_preimage {
		let (_, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
	}: unrequest_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		assert_eq!(StatusFor::<T>::get(&hash), None);
	}
	// Cheap unrequest - not the last reference.
	unrequest_multi_referenced_preimage {
		let (_, hash) = preimage_and_hash::<T>();
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
		assert_ok!(Preimage::<T>::request_preimage(T::ManagerOrigin::successful_origin(), hash));
	}: unrequest_preimage<T::RuntimeOrigin>(T::ManagerOrigin::successful_origin(), hash)
	verify {
		let s = RequestStatus::Requested { deposit: None, count: 1, len: None };
		assert_eq!(StatusFor::<T>::get(&hash), Some(s));
	}

	impl_benchmark_test_suite!(Preimage, crate::mock::new_test_ext(), crate::mock::Test);
}
