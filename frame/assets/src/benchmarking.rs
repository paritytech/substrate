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

//! Assets pallet benchmarking.

use super::*;
use sp_runtime::traits::Bounded;
use frame_system::RawOrigin as SystemOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller, impl_benchmark_test_suite};
use frame_support::traits::Get;

use crate::Module as Assets;

const SEED: u32 = 0;

fn create_default_asset<T: Config>(max_zombies: u32)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let root = SystemOrigin::Root.into();
	assert!(Assets::<T>::force_create(
		root,
		Default::default(),
		caller_lookup.clone(),
		max_zombies,
		1u32.into(),
	).is_ok());
	(caller, caller_lookup)
}

fn create_default_minted_asset<T: Config>(max_zombies: u32, amount: T::Balance)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let (caller, caller_lookup)  = create_default_asset::<T>(max_zombies);
	assert!(Assets::<T>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
		caller_lookup.clone(),
		amount,
	).is_ok());
	(caller, caller_lookup)
}

fn add_zombies<T: Config>(minter: T::AccountId, n: u32) {
	let origin = SystemOrigin::Signed(minter);
	for i in 0..n {
		let target = account("zombie", i, SEED);
		let target_lookup = T::Lookup::unlookup(target);
		assert!(Assets::<T>::mint(origin.clone().into(), Default::default(), target_lookup, 100u32.into()).is_ok());
	}
}

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	// compare to the last event record
	let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks! {
	create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, 1, 1u32.into())
	verify {
		assert_last_event::<T>(Event::Created(Default::default(), caller.clone(), caller).into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, 1, 1u32.into())
	verify {
		assert_last_event::<T>(Event::ForceCreated(Default::default(), caller).into());
	}

	destroy {
		let z in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(10_000);
		add_zombies::<T>(caller.clone(), z);
	}: _(SystemOrigin::Signed(caller), Default::default(), 10_000)
	verify {
		assert_last_event::<T>(Event::Destroyed(Default::default()).into());
	}

	force_destroy {
		let z in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(10_000);
		add_zombies::<T>(caller.clone(), z);
	}: _(SystemOrigin::Root, Default::default(), 10_000)
	verify {
		assert_last_event::<T>(Event::Destroyed(Default::default()).into());
	}

	mint {
		let (caller, caller_lookup) = create_default_asset::<T>(10);
		let amount = T::Balance::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Issued(Default::default(), caller, amount).into());
	}

	burn {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Burned(Default::default(), caller, amount).into());
	}

	transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), target_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Transferred(Default::default(), caller, target, amount).into());
	}

	force_transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, target_lookup, amount)
	verify {
		assert_last_event::<T>(
			Event::ForceTransferred(Default::default(), caller, target, amount).into()
		);
	}

	freeze {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T>(Event::Frozen(Default::default(), caller).into());
	}

	thaw {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
		Assets::<T>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			Default::default(),
			caller_lookup.clone(),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T>(Event::Thawed(Default::default(), caller).into());
	}

	freeze_asset {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default())
	verify {
		assert_last_event::<T>(Event::AssetFrozen(Default::default()).into());
	}

	thaw_asset {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
		Assets::<T>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			Default::default(),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), Default::default())
	verify {
		assert_last_event::<T>(Event::AssetThawed(Default::default()).into());
	}

	transfer_ownership {
		let (caller, _) = create_default_asset::<T>(10);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller), Default::default(), target_lookup)
	verify {
		assert_last_event::<T>(Event::OwnerChanged(Default::default(), target).into());
	}

	set_team {
		let (caller, _) = create_default_asset::<T>(10);
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), Default::default(), target0.clone(), target1.clone(), target2.clone())
	verify {
		assert_last_event::<T>(Event::TeamChanged(
			Default::default(),
			account("target", 0, SEED),
			account("target", 1, SEED),
			account("target", 2, SEED),
		).into());
	}

	set_max_zombies {
		let (caller, _) = create_default_asset::<T>(10);
		let max_zombies: u32 = 100;
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), max_zombies)
	verify {
		assert_last_event::<T>(Event::MaxZombiesChanged(Default::default(), max_zombies).into());
	}

	set_metadata {
		let n in 0 .. T::StringLimit::get();
		let s in 0 .. T::StringLimit::get();

		let name = vec![0u8; n as usize];
		let symbol = vec![0u8; s as usize];
		let decimals = 12;

		let (caller, _) = create_default_asset::<T>(10);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), name.clone(), symbol.clone(), decimals)
	verify {
		assert_last_event::<T>(Event::MetadataSet(Default::default(), name, symbol, decimals).into());
	}
}

impl_benchmark_test_suite!(Assets, crate::tests::new_test_ext(), crate::tests::Test);
