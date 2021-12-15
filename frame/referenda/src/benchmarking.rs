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

//! Democracy pallet benchmarking.

use super::*;
use frame_benchmarking::{account, benchmarks, whitelist_account};
use frame_support::{assert_ok, traits::{Currency, EnsureOrigin}};
use frame_system::RawOrigin;
use sp_runtime::traits::{Bounded, Hash};
use assert_matches::assert_matches;
use crate::Pallet as Referenda;

const SEED: u32 = 0;

#[allow(dead_code)]
fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

benchmarks! {
	submit {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: _(
		RawOrigin::Signed(caller),
		RawOrigin::Root.into(),
		T::Hashing::hash_of(&0),
		AtOrAfter::After(0u32.into())
	) verify {
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
		let status = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(status, ReferendumInfo::Ongoing(_));
	}

	place_decision_deposit {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let origin = move || RawOrigin::Signed(caller.clone());
		assert_ok!(Referenda::<T>::submit(
			origin().into(),
			RawOrigin::Root.into(),
			T::Hashing::hash_of(&0),
			AtOrAfter::After(0u32.into())
		));
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
	}: _(origin(), index)
	verify {
		let status = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(status, ReferendumInfo::Ongoing(ReferendumStatus {
			decision_deposit: Some(..),
			..
		}));
	}

	refund_decision_deposit {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let origin = move || RawOrigin::Signed(caller.clone());
		assert_ok!(Referenda::<T>::submit(
			origin().into(),
			RawOrigin::Root.into(),
			T::Hashing::hash_of(&0),
			AtOrAfter::After(0u32.into())
		));
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
		assert_ok!(Referenda::<T>::place_decision_deposit(origin().into(), index));
		assert_ok!(Referenda::<T>::cancel(T::CancelOrigin::successful_origin(), index));
	}: _(origin(), index)
	verify {
		let status = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(status, ReferendumInfo::Cancelled(_, _, None));
	}

	cancel {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let origin = move || RawOrigin::Signed(caller.clone());
		assert_ok!(Referenda::<T>::submit(
			origin().into(),
			RawOrigin::Root.into(),
			T::Hashing::hash_of(&0),
			AtOrAfter::After(0u32.into())
		));
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
		assert_ok!(Referenda::<T>::place_decision_deposit(origin().into(), index));
	}: _<T::Origin>(T::CancelOrigin::successful_origin(), index)
	verify {
		let status = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(status, ReferendumInfo::Cancelled(..));
	}

	kill {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let origin = move || RawOrigin::Signed(caller.clone());
		assert_ok!(Referenda::<T>::submit(
			origin().into(),
			RawOrigin::Root.into(),
			T::Hashing::hash_of(&0),
			AtOrAfter::After(0u32.into())
		));
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
		assert_ok!(Referenda::<T>::place_decision_deposit(origin().into(), index));
	}: _<T::Origin>(T::KillOrigin::successful_origin(), index)
	verify {
		let status = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(status, ReferendumInfo::Killed(..));
	}
/*
	nudge_referendum {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller), 0)
	verify {
	}
*/
	impl_benchmark_test_suite!(
		Referenda,
		crate::mock::new_test_ext(),
		crate::mock::Test
	);
}
