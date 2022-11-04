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

//! Benchmarks for NIS Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, EnsureOrigin, Get};
use frame_system::RawOrigin;
use sp_arithmetic::Perquintill;
use sp_runtime::traits::{Bounded, One, Zero};
use sp_std::prelude::*;

use crate::Pallet as Nis;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

benchmarks! {
	place_bid {
		let l in 0..(T::MaxQueueLen::get() - 1);
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..l {
			Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		}
	}: _(RawOrigin::Signed(caller.clone()), T::MinBid::get() * BalanceOf::<T>::from(2u32), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (l + 1, T::MinBid::get() * BalanceOf::<T>::from(l + 2)));
	}

	place_bid_max {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..T::MaxQueueLen::get() {
			Nis::<T>::place_bid(origin.clone().into(), T::MinBid::get(), 1)?;
		}
	}: place_bid(origin, T::MinBid::get() * BalanceOf::<T>::from(2u32), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (
			T::MaxQueueLen::get(),
			T::MinBid::get() * BalanceOf::<T>::from(T::MaxQueueLen::get() + 1),
		));
	}

	retract_bid {
		let l in 1..T::MaxQueueLen::get();
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		for i in 0..l {
			Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		}
	}: _(RawOrigin::Signed(caller.clone()), T::MinBid::get(), 1)
	verify {
		assert_eq!(QueueTotals::<T>::get()[0], (l - 1, T::MinBid::get() * BalanceOf::<T>::from(l - 1)));
	}

	fund_deficit {
		let origin = T::FundOrigin::successful_origin();
		let caller: T::AccountId = whitelisted_caller();
		let bid = T::MinBid::get().max(One::one());
		T::Currency::make_free_balance_be(&caller, bid);
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), bid, 1)?;
		Nis::<T>::enlarge(bid, 1);
		let original = T::Currency::free_balance(&Nis::<T>::account_id());
		T::Currency::make_free_balance_be(&Nis::<T>::account_id(), BalanceOf::<T>::min_value());
	}: _<T::RuntimeOrigin>(origin)
	verify {
		assert_eq!(original, T::Currency::free_balance(&Nis::<T>::account_id()));
	}

	thaw {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(3u32));
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::enlarge(T::MinBid::get() * BalanceOf::<T>::from(2u32), 2);
		Receipts::<T>::mutate(0, |m_g| if let Some(ref mut g) = m_g { g.expiry = Zero::zero() });
	}: _(RawOrigin::Signed(caller.clone()), 0, None)
	verify {
		assert!(Receipts::<T>::get(0).is_none());
	}

	process_queues {
	}: { Nis::<T>::pursue_target(0, Zero::zero()) }

	process_queue {
		// bids taken
		let b in 0..T::MaxQueueLen::get();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(b + 1));

		for _ in 0..b {
			Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		}
		let target = Perquintill::one();
	}: { Nis::<T>::pursue_target(b, target) }

	process_bid {
		// total queues hit
		let q in 0..T::QueueCount::get();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(q + 1));

		for i in 0..q {
			Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), i + 1)?;
		}

		let target = Perquintill::one();
	}: { Nis::<T>::pursue_target(q, target) }

	impl_benchmark_test_suite!(Nis, crate::mock::new_test_ext(), crate::mock::Test);
}
