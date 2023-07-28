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

//! Benchmarking for pallet-fast-unstake.

#![cfg(feature = "runtime-benchmarks")]

use crate::{types::*, Pallet as FastUnstake, *};
use frame_benchmarking::v1::{benchmarks, whitelist_account, BenchmarkError};
use frame_support::{
	assert_ok,
	traits::{Currency, EnsureOrigin, Get, Hooks},
};
use frame_system::RawOrigin;
use sp_runtime::traits::Zero;
use sp_staking::{EraIndex, StakingInterface};
use sp_std::prelude::*;

const USER_SEED: u32 = 0;

type CurrencyOf<T> = <T as Config>::Currency;

fn create_unexposed_batch<T: Config>(batch_size: u32) -> Vec<T::AccountId> {
	(0..batch_size)
		.map(|i| {
			let account =
				frame_benchmarking::account::<T::AccountId>("unexposed_nominator", i, USER_SEED);
			fund_and_bond_account::<T>(&account);
			account
		})
		.collect()
}

fn fund_and_bond_account<T: Config>(account: &T::AccountId) {
	let stake = CurrencyOf::<T>::minimum_balance() * 100u32.into();
	CurrencyOf::<T>::make_free_balance_be(&account, stake * 10u32.into());

	// bond and nominate ourselves, this will guarantee that we are not backing anyone.
	assert_ok!(T::Staking::bond(account, stake, account));
	assert_ok!(T::Staking::nominate(account, vec![account.clone()]));
}

pub(crate) fn fast_unstake_events<T: Config>() -> Vec<crate::Event<T>> {
	frame_system::Pallet::<T>::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| <T as Config>::RuntimeEvent::from(e).try_into().ok())
		.collect::<Vec<_>>()
}

fn setup_staking<T: Config>(v: u32, until: EraIndex) {
	let ed = CurrencyOf::<T>::minimum_balance();

	log!(debug, "registering {} validators and {} eras.", v, until);

	// our validators don't actually need to registered in staking -- just generate `v` random
	// accounts.
	let validators = (0..v)
		.map(|x| frame_benchmarking::account::<T::AccountId>("validator", x, USER_SEED))
		.collect::<Vec<_>>();

	for era in 0..=until {
		let others = (0..T::MaxBackersPerValidator::get())
			.map(|s| {
				let who = frame_benchmarking::account::<T::AccountId>("nominator", era, s);
				let value = ed;
				(who, value)
			})
			.collect::<Vec<_>>();
		validators.iter().for_each(|v| {
			T::Staking::add_era_stakers(&era, &v, others.clone());
		});
	}
}

fn on_idle_full_block<T: Config>() {
	let remaining_weight = <T as frame_system::Config>::BlockWeights::get().max_block;
	FastUnstake::<T>::on_idle(Zero::zero(), remaining_weight);
}

benchmarks! {
	// on_idle, we don't check anyone, but fully unbond them.
	on_idle_unstake {
		let b in 1 .. T::BatchSize::get();

		ErasToCheckPerBlock::<T>::put(1);
		for who in create_unexposed_batch::<T>(b).into_iter() {
			assert_ok!(FastUnstake::<T>::register_fast_unstake(
				RawOrigin::Signed(who.clone()).into(),
			));
		}

		// run on_idle once. This will check era 0.
		assert_eq!(Head::<T>::get(), None);
		on_idle_full_block::<T>();

		assert!(matches!(
			Head::<T>::get(),
			Some(UnstakeRequest {
				checked,
				stashes,
				..
			}) if checked.len() == 1 && stashes.len() as u32 == b
		));
	}
	: {
		on_idle_full_block::<T>();
	}
	verify {
		assert!(matches!(
			fast_unstake_events::<T>().last(),
			Some(Event::BatchFinished { size: b })
		));
	}

	// on_idle, when we check some number of eras and the queue is already set.
	on_idle_check {
		let v in 1 .. 256;
		let b in 1 .. T::BatchSize::get();
		let u = T::MaxErasToCheckPerBlock::get().min(T::Staking::bonding_duration());

		ErasToCheckPerBlock::<T>::put(u);
		T::Staking::set_current_era(u);

		// setup staking with v validators and u eras of data (0..=u+1)
		setup_staking::<T>(v, u);

		let stashes = create_unexposed_batch::<T>(b).into_iter().map(|s| {
			assert_ok!(FastUnstake::<T>::register_fast_unstake(
				RawOrigin::Signed(s.clone()).into(),
			));
			(s, T::Deposit::get())
		}).collect::<Vec<_>>();

		// no one is queued thus far.
		assert_eq!(Head::<T>::get(), None);

		Head::<T>::put(UnstakeRequest { stashes: stashes.clone().try_into().unwrap(), checked: Default::default() });
	}
	: {
		on_idle_full_block::<T>();
	}
	verify {
		let checked = (1..=u).rev().collect::<Vec<EraIndex>>();
		let request = Head::<T>::get().unwrap();
		assert_eq!(checked, request.checked.into_inner());
		assert!(matches!(
			fast_unstake_events::<T>().last(),
			Some(Event::BatchChecked { .. })
		));
		assert!(stashes.iter().all(|(s, _)| request.stashes.iter().find(|(ss, _)| ss == s).is_some()));
	}

	register_fast_unstake {
		ErasToCheckPerBlock::<T>::put(1);
		let who = create_unexposed_batch::<T>(1).get(0).cloned().unwrap();
		whitelist_account!(who);
		assert_eq!(Queue::<T>::count(), 0);

	}
	:_(RawOrigin::Signed(who.clone()))
	verify {
		assert_eq!(Queue::<T>::count(), 1);
	}

	deregister {
		ErasToCheckPerBlock::<T>::put(1);
		let who = create_unexposed_batch::<T>(1).get(0).cloned().unwrap();
		assert_ok!(FastUnstake::<T>::register_fast_unstake(
			RawOrigin::Signed(who.clone()).into(),
		));
		assert_eq!(Queue::<T>::count(), 1);
		whitelist_account!(who);
	}
	:_(RawOrigin::Signed(who.clone()))
	verify {
		assert_eq!(Queue::<T>::count(), 0);
	}

	control {
		let origin = <T as Config>::ControlOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;
	}
	: _<T::RuntimeOrigin>(origin, T::MaxErasToCheckPerBlock::get())
	verify {}

	impl_benchmark_test_suite!(Pallet, crate::mock::ExtBuilder::default().build(), crate::mock::Runtime)
}
