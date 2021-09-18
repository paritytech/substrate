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

//! Benchmarks for Gilt Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, impl_benchmark_test_suite, whitelisted_caller};
use frame_support::{
	dispatch::UnfilteredDispatchable,
	traits::{Currency, EnsureOrigin, Get},
};
use frame_system::RawOrigin;
use sp_arithmetic::Perquintill;
use sp_runtime::traits::{Bounded, Zero};
use sp_std::prelude::*;

use crate::Pallet as Gilt;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

benchmarks! {
	place_bid {
		let l in 0..(T::MaxQueueLen::get() - 1);
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..l {
			Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		}
	}: _(RawOrigin::Signed(caller.clone()), T::MinFreeze::get() * BalanceOf::<T>::from(2u32), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (l + 1, T::MinFreeze::get() * BalanceOf::<T>::from(l + 2)));
	}

	place_bid_max {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..T::MaxQueueLen::get() {
			Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		}
	}: {
		Gilt::<T>::place_bid(
			RawOrigin::Signed(caller.clone()).into(),
			T::MinFreeze::get() * BalanceOf::<T>::from(2u32),
			1,
		)?
	}
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (
			T::MaxQueueLen::get(),
			T::MinFreeze::get() * BalanceOf::<T>::from(T::MaxQueueLen::get() + 1),
		));
	}

	retract_bid {
		let l in 1..T::MaxQueueLen::get();
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..l {
			Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		}
	}: _(RawOrigin::Signed(caller.clone()), T::MinFreeze::get(), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (l - 1, T::MinFreeze::get() * BalanceOf::<T>::from(l - 1)));
	}

	set_target {
		let call = Call::<T>::set_target { target: Default::default() };
		let origin = T::AdminOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }

	thaw {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinFreeze::get() * BalanceOf::<T>::from(3u32));
		Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		Gilt::<T>::enlarge(T::MinFreeze::get() * BalanceOf::<T>::from(2u32), 2);
		Active::<T>::mutate(0, |m_g| if let Some(ref mut g) = m_g { g.expiry = Zero::zero() });
	}: _(RawOrigin::Signed(caller.clone()), 0)
	verify {
		assert!(Active::<T>::get(0).is_none());
	}

	pursue_target_noop {
	}: { Gilt::<T>::pursue_target(0) }

	pursue_target_per_item {
		// bids taken
		let b in 1..T::MaxQueueLen::get();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinFreeze::get() * BalanceOf::<T>::from(b + 1));

		for _ in 0..b {
			Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), 1)?;
		}

		Call::<T>::set_target { target: Perquintill::from_percent(100) }
			.dispatch_bypass_filter(T::AdminOrigin::successful_origin())?;

	}: { Gilt::<T>::pursue_target(b) }

	pursue_target_per_queue {
		// total queues hit
		let q in 1..T::QueueCount::get();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinFreeze::get() * BalanceOf::<T>::from(q + 1));

		for i in 0..q {
			Gilt::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinFreeze::get(), i + 1)?;
		}

		Call::<T>::set_target { target: Perquintill::from_percent(100) }
			.dispatch_bypass_filter(T::AdminOrigin::successful_origin())?;

	}: { Gilt::<T>::pursue_target(q) }
}

impl_benchmark_test_suite!(Gilt, crate::mock::new_test_ext(), crate::mock::Test);
