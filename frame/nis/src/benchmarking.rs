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
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{nonfungible::Inspect, Currency, EnsureOrigin, Get};
use frame_system::RawOrigin;
use sp_arithmetic::Perquintill;
use sp_runtime::{
	traits::{Bounded, One, Zero},
	DispatchError, PerThing,
};
use sp_std::prelude::*;

use crate::Pallet as Nis;

const SEED: u32 = 0;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

fn fill_queues<T: Config>() -> Result<(), DispatchError> {
	// filling queues involves filling the first queue entirely and placing a single item in all
	// other queues.

	let queues = T::QueueCount::get();
	let bids = T::MaxQueueLen::get();

	let caller: T::AccountId = whitelisted_caller();
	T::Currency::make_free_balance_be(
		&caller,
		T::MinBid::get() * BalanceOf::<T>::from(queues + bids),
	);

	for _ in 0..bids {
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
	}
	for d in 1..queues {
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1 + d)?;
	}
	Ok(())
}

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
		Nis::<T>::process_queues(Perquintill::one(), 1, 1, &mut WeightCounter::unlimited());
		Nis::<T>::communify(RawOrigin::Signed(caller.clone()).into(), 0)?;
		let original = T::Currency::free_balance(&Nis::<T>::account_id());
		T::Currency::make_free_balance_be(&Nis::<T>::account_id(), BalanceOf::<T>::min_value());
	}: _<T::RuntimeOrigin>(origin)
	verify {
		// Must fund at least 99.999% of the required amount.
		let missing = Perquintill::from_rational(
			T::Currency::free_balance(&Nis::<T>::account_id()), original).left_from_one();
		assert!(missing <= Perquintill::one() / 100_000);
	}

	thaw_private {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(3u32));
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::process_queues(Perquintill::one(), 1, 2, &mut WeightCounter::unlimited());
		Receipts::<T>::mutate(0, |m_g| if let Some(ref mut g) = m_g { g.expiry = Zero::zero() });
	}: _(RawOrigin::Signed(caller.clone()), 0, None)
	verify {
		assert!(Receipts::<T>::get(0).is_none());
	}

	thaw_communal {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(3u32));
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::process_queues(Perquintill::one(), 1, 2, &mut WeightCounter::unlimited());
		Receipts::<T>::mutate(0, |m_g| if let Some(ref mut g) = m_g { g.expiry = Zero::zero() });
		Nis::<T>::communify(RawOrigin::Signed(caller.clone()).into(), 0)?;
	}: _(RawOrigin::Signed(caller.clone()), 0)
	verify {
		assert!(Receipts::<T>::get(0).is_none());
	}

	privatize {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(3u32));
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::process_queues(Perquintill::one(), 1, 2, &mut WeightCounter::unlimited());
		Nis::<T>::communify(RawOrigin::Signed(caller.clone()).into(), 0)?;
	}: _(RawOrigin::Signed(caller.clone()), 0)
	verify {
		assert_eq!(Nis::<T>::owner(&0), Some(caller));
	}

	communify {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::MinBid::get() * BalanceOf::<T>::from(3u32));
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::place_bid(RawOrigin::Signed(caller.clone()).into(), T::MinBid::get(), 1)?;
		Nis::<T>::process_queues(Perquintill::one(), 1, 2, &mut WeightCounter::unlimited());
	}: _(RawOrigin::Signed(caller.clone()), 0)
	verify {
		assert_eq!(Nis::<T>::owner(&0), None);
	}

	process_queues {
		fill_queues::<T>()?;
	}: {
		Nis::<T>::process_queues(
			Perquintill::one(),
			Zero::zero(),
			u32::max_value(),
			&mut WeightCounter::unlimited(),
		)
	}

	process_queue {
		let our_account = Nis::<T>::account_id();
		let issuance = Nis::<T>::issuance();
		let mut summary = Summary::<T>::get();
	}: {
		Nis::<T>::process_queue(
			1u32,
			1u32.into(),
			&our_account,
			&issuance,
			0,
			&mut Bounded::max_value(),
			&mut (T::MaxQueueLen::get(), Bounded::max_value()),
			&mut summary,
			&mut WeightCounter::unlimited(),
		)
	}

	process_bid {
		let who = account::<T::AccountId>("bidder", 0, SEED);
		let bid = Bid {
			amount: T::MinBid::get(),
			who,
		};
		let our_account = Nis::<T>::account_id();
		let issuance = Nis::<T>::issuance();
		let mut summary = Summary::<T>::get();
	}: {
		Nis::<T>::process_bid(
			bid,
			2u32.into(),
			&our_account,
			&issuance,
			&mut Bounded::max_value(),
			&mut Bounded::max_value(),
			&mut summary,
		)
	}

	impl_benchmark_test_suite!(Nis, crate::mock::new_test_ext(), crate::mock::Test);
}
