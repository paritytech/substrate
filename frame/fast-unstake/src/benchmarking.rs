// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Benchmarking for pallet-example-basic.

#![cfg(feature = "runtime-benchmarks")]

use crate::{Pallet as FastUnstake, *};
use frame_benchmarking::{benchmarks, whitelist_account};
use frame_support::traits::{Currency, EnsureOrigin, Get};
use frame_system::RawOrigin;
use pallet_nomination_pools::{Pallet as Pools, PoolId};
use pallet_staking::Pallet as Staking;
use sp_runtime::traits::{Bounded, StaticLookup, Zero};
use sp_std::prelude::*;
use frame_support::traits::Hooks;

const USER_SEED: u32 = 0;
const DEFAULT_BACKER_PER_VALIDATOR: u32 = 128;

type CurrencyOf<T> = <T as pallet_staking::Config>::Currency;

fn l<T: Config>(
	who: T::AccountId,
) -> <<T as frame_system::Config>::Lookup as StaticLookup>::Source {
	T::Lookup::unlookup(who)
}

fn create_unexposed_nominator<T: Config>() -> T::AccountId {
	let account = frame_benchmarking::account::<T::AccountId>("nominator_42", 0, USER_SEED);
	let stake = CurrencyOf::<T>::minimum_balance() * 100u32.into();
	CurrencyOf::<T>::make_free_balance_be(&account, stake * 10u32.into());

	let account_lookup = l::<T>(account.clone());
	// bond and nominate ourselves, this will guarantee that we are not backing anyone.
	Staking::<T>::bond(
		RawOrigin::Signed(account.clone()).into(),
		account_lookup.clone(),
		stake,
		pallet_staking::RewardDestination::Controller,
	)
	.unwrap();
	Staking::<T>::nominate(RawOrigin::Signed(account.clone()).into(), vec![account_lookup])
		.unwrap();

	account
}

fn setup_pool<T: Config>() -> PoolId {
	let depositor = frame_benchmarking::account::<T::AccountId>("depositor_42", 0, USER_SEED);
	let depositor_lookup = l::<T>(depositor.clone());

	let stake = Pools::<T>::depositor_min_bond();
	CurrencyOf::<T>::make_free_balance_be(&depositor, stake * 10u32.into());

	Pools::<T>::create(
		RawOrigin::Signed(depositor.clone()).into(),
		stake,
		depositor_lookup.clone(),
		depositor_lookup.clone(),
		depositor_lookup,
	)
	.unwrap();

	pallet_nomination_pools::LastPoolId::<T>::get()
}

fn setup_staking<T: Config>(v: u32) {
	let ed = CurrencyOf::<T>::minimum_balance();

	// make sure there are enough validator candidates
	// NOTE: seems like these actually don't need to be real validators..
	for seed in 0..(pallet_staking::Validators::<T>::iter().count().saturating_sub(v as usize)) {
		let account =
			frame_benchmarking::account::<T::AccountId>("validator", seed as u32, USER_SEED);
		let account_lookup = l::<T>(account.clone());

		let stake = ed * 100u32.into();
		CurrencyOf::<T>::make_free_balance_be(&account, stake * 10u32.into());

		Staking::<T>::bond(
			RawOrigin::Signed(account.clone()).into(),
			account_lookup.clone(),
			stake,
			pallet_staking::RewardDestination::Controller,
		)
		.unwrap();
		Staking::<T>::validate(RawOrigin::Signed(account.clone()).into(), Default::default())
			.unwrap();
	}

	let validators = pallet_staking::Validators::<T>::iter_keys().collect::<Vec<_>>();

	for era in 0..(2 * <T as pallet_staking::Config>::BondingDuration::get()) {
		let others = (0..DEFAULT_BACKER_PER_VALIDATOR)
			.map(|s| {
				let who = frame_benchmarking::account::<T::AccountId>("nominator", era, s);
				let value = ed;
				pallet_staking::IndividualExposure { who, value }
			})
			.collect::<Vec<_>>();
		let exposure =
			pallet_staking::Exposure { total: Default::default(), own: Default::default(), others };
		validators.iter().for_each(|v| {
			Staking::<T>::add_era_stakers(era, v.clone(), exposure.clone());
		});
	}
}

fn on_idle_full_block<T: Config>() {
	let remaining_weight = <T as frame_system::Config>::BlockWeights::get().max_block;
	FastUnstake::<T>::on_idle(Zero::zero(), remaining_weight);
}

benchmarks! {
	// on_idle, we we don't check anyone, but fully unbond and move them to another pool.
	on_idle_unstake {
		let who = create_unexposed_nominator::<T>();
		let pool_id = setup_pool::<T>();
		FastUnstake::<T>::register_fast_unstake(
			RawOrigin::Signed(who.clone()).into(),
			Some(pool_id)
		).unwrap();
		ErasToCheckPerBlock::<T>::put(1);

		// no era to check, because staking era is still 0.
		assert_eq!(pallet_staking::CurrentEra::<T>::get().unwrap_or_default(), 0);

		// run on_idle once.
		on_idle_full_block::<T>();
	}
	: {
		on_idle_full_block::<T>();
	}
	verify {}

	// on_idle, when we check some number of eras,
	on_idle_check {
		// staking should have enough validators and progress to a state where enough eras exist.
		// add non-exposed nominator
		// register
		//
	}
	: {}
	verify {}

	// same as above, but we do the entire check and realize that we had to slash our nominator now.
	on_idle_check_slash {}
	: {}
	verify {}

	register_fast_unstake {
		let who = create_unexposed_nominator::<T>();
		whitelist_account!(who);
	}
	:_(RawOrigin::Signed(who.clone()), None)
	verify {}

	deregister {
		let who = create_unexposed_nominator::<T>();
		FastUnstake::<T>::register_fast_unstake(
			RawOrigin::Signed(who.clone()).into(),
			None
		).unwrap();
		whitelist_account!(who);
	}
	:_(RawOrigin::Signed(who.clone()))
	verify {}

	control {
		let origin = <T as Config>::ControlOrigin::successful_origin();
	}
	: _<T::Origin>(origin, 128)
	verify {}

	// impl_benchmark_test_suite!(Pallet, crate::tests::new_test_ext(), crate::tests::Test)
}
