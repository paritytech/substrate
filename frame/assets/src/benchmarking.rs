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

fn create_default_asset<T: Config>(is_sufficient: bool)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let root = SystemOrigin::Root.into();
	assert!(Assets::<T>::force_create(
		root,
		Default::default(),
		caller_lookup.clone(),
		is_sufficient,
		1u32.into(),
	).is_ok());
	(caller, caller_lookup)
}

fn create_default_minted_asset<T: Config>(is_sufficient: bool, amount: T::Balance)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let (caller, caller_lookup)  = create_default_asset::<T>(is_sufficient);
	if !is_sufficient {
		T::Currency::make_free_balance_be(&caller, T::Currency::minimum_balance());
	}
	assert!(Assets::<T>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
		caller_lookup.clone(),
		amount,
	).is_ok());
	(caller, caller_lookup)
}

fn swap_is_sufficient<T: Config>(s: &mut bool) {
	Asset::<T>::mutate(&T::AssetId::default(), |maybe_a|
		if let Some(ref mut a) = maybe_a { sp_std::mem::swap(s, &mut a.is_sufficient) }
	);
}

fn add_consumers<T: Config>(minter: T::AccountId, n: u32) {
	let origin = SystemOrigin::Signed(minter);
	let mut s = false;
	swap_is_sufficient::<T>(&mut s);
	for i in 0..n {
		let target = account("consumer", i, SEED);
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let target_lookup = T::Lookup::unlookup(target);
		assert!(Assets::<T>::mint(origin.clone().into(), Default::default(), target_lookup, 100u32.into()).is_ok());
	}
	swap_is_sufficient::<T>(&mut s);
}

fn add_sufficients<T: Config>(minter: T::AccountId, n: u32) {
	let origin = SystemOrigin::Signed(minter);
	let mut s = true;
	swap_is_sufficient::<T>(&mut s);
	for i in 0..n {
		let target = account("sufficient", i, SEED);
		let target_lookup = T::Lookup::unlookup(target);
		assert!(Assets::<T>::mint(origin.clone().into(), Default::default(), target_lookup, 100u32.into()).is_ok());
	}
	swap_is_sufficient::<T>(&mut s);
}

fn add_approvals<T: Config>(minter: T::AccountId, n: u32) {
	T::Currency::deposit_creating(&minter, T::ApprovalDeposit::get() * n.into());
	let minter_lookup = T::Lookup::unlookup(minter.clone());
	let origin = SystemOrigin::Signed(minter);
	Assets::<T>::mint(
		origin.clone().into(),
		Default::default(),
		minter_lookup,
		(100 * (n + 1)).into(),
	).unwrap();
	for i in 0..n {
		let target = account("approval", i, SEED);
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let target_lookup = T::Lookup::unlookup(target);
		Assets::<T>::approve_transfer(
			origin.clone().into(),
			Default::default(),
			target_lookup,
			100u32.into(),
		).unwrap();
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
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, 1u32.into())
	verify {
		assert_last_event::<T>(Event::Created(Default::default(), caller.clone(), caller).into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, true, 1u32.into())
	verify {
		assert_last_event::<T>(Event::ForceCreated(Default::default(), caller).into());
	}

	destroy {
		let c in 0 .. 10_000;
		let s in 0 .. 10_000;
		let a in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(true);
		add_consumers::<T>(caller.clone(), c);
		add_sufficients::<T>(caller.clone(), s);
		add_approvals::<T>(caller.clone(), a);
		let witness = Asset::<T>::get(T::AssetId::default()).unwrap().destroy_witness();
	}: _(SystemOrigin::Signed(caller), Default::default(), witness)
	verify {
		assert_last_event::<T>(Event::Destroyed(Default::default()).into());
	}

	force_destroy {
		let c in 0 .. 10_000;
		let s in 0 .. 10_000;
		let a in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(true);
		add_consumers::<T>(caller.clone(), c);
		add_sufficients::<T>(caller.clone(), s);
		add_approvals::<T>(caller.clone(), a);
		let witness = Asset::<T>::get(T::AssetId::default()).unwrap().destroy_witness();
	}: _(SystemOrigin::Root, Default::default(), witness)
	verify {
		assert_last_event::<T>(Event::Destroyed(Default::default()).into());
	}

	mint {
		let (caller, caller_lookup) = create_default_asset::<T>(true);
		let amount = T::Balance::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Issued(Default::default(), caller, amount).into());
	}

	burn {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, amount);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Burned(Default::default(), caller, amount).into());
	}

	transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), target_lookup, amount)
	verify {
		assert_last_event::<T>(Event::Transferred(Default::default(), caller, target, amount).into());
	}

	force_transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, target_lookup, amount)
	verify {
		assert_last_event::<T>(
			Event::Transferred(Default::default(), caller, target, amount).into()
		);
	}

	freeze {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T>(Event::Frozen(Default::default(), caller).into());
	}

	thaw {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, 100u32.into());
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
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default())
	verify {
		assert_last_event::<T>(Event::AssetFrozen(Default::default()).into());
	}

	thaw_asset {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(true, 100u32.into());
		Assets::<T>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			Default::default(),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), Default::default())
	verify {
		assert_last_event::<T>(Event::AssetThawed(Default::default()).into());
	}

	transfer_ownership {
		let (caller, _) = create_default_asset::<T>(true);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller), Default::default(), target_lookup)
	verify {
		assert_last_event::<T>(Event::OwnerChanged(Default::default(), target).into());
	}

	set_team {
		let (caller, _) = create_default_asset::<T>(true);
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
/*
	set_max_zombies {
		let (caller, _) = create_default_asset::<T>(10);
		let max_zombies: u32 = 100;
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), max_zombies)
	verify {
		assert_last_event::<T>(Event::MaxZombiesChanged(Default::default(), max_zombies).into());
	}
*/
	set_metadata {
		let n in 0 .. T::StringLimit::get();
		let s in 0 .. T::StringLimit::get();

		let name = vec![0u8; n as usize];
		let symbol = vec![0u8; s as usize];
		let decimals = 12;

		let (caller, _) = create_default_asset::<T>(true);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), name.clone(), symbol.clone(), decimals)
	verify {
		assert_last_event::<T>(Event::MetadataSet(Default::default(), name, symbol, decimals).into());
	}
}

impl_benchmark_test_suite!(Assets, crate::tests::new_test_ext(), crate::tests::Test);
