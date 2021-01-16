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
use sp_std::prelude::*;
use sp_runtime::traits::Bounded;
use frame_system::RawOrigin as SystemOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller};

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
		assert_last_event::<T>(RawEvent::Created(Default::default(), caller.clone(), caller).into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, 1, 1u32.into())
	verify {
		assert_last_event::<T>(RawEvent::ForceCreated(Default::default(), caller).into());
	}

	destroy {
		let z in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(10_000);
		add_zombies::<T>(caller.clone(), z);
	}: _(SystemOrigin::Signed(caller), Default::default(), 10_000)
	verify {
		assert_last_event::<T>(RawEvent::Destroyed(Default::default()).into());
	}

	force_destroy {
		let z in 0 .. 10_000;
		let (caller, _) = create_default_asset::<T>(10_000);
		add_zombies::<T>(caller.clone(), z);
	}: _(SystemOrigin::Root, Default::default(), 10_000)
	verify {
		assert_last_event::<T>(RawEvent::Destroyed(Default::default()).into());
	}

	mint {
		let (caller, caller_lookup) = create_default_asset::<T>(10);
		let amount = T::Balance::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(RawEvent::Issued(Default::default(), caller, amount).into());
	}

	burn {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, amount)
	verify {
		assert_last_event::<T>(RawEvent::Burned(Default::default(), caller, amount).into());
	}

	transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), target_lookup, amount)
	verify {
		assert_last_event::<T>(RawEvent::Transferred(Default::default(), caller, target, amount).into());
	}

	force_transfer {
		let amount = T::Balance::from(100u32);
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup, target_lookup, amount)
	verify {
		assert_last_event::<T>(RawEvent::ForceTransferred(Default::default(), caller, target, amount).into());
	}

	freeze {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T>(RawEvent::Frozen(Default::default(), caller).into());
	}

	thaw {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100u32.into());
		assert!(Assets::<T>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			Default::default(),
			caller_lookup.clone()
		).is_ok());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T>(RawEvent::Thawed(Default::default(), caller).into());
	}

	transfer_ownership {
		let (caller, _) = create_default_asset::<T>(10);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller), Default::default(), target_lookup)
	verify {
		assert_last_event::<T>(RawEvent::OwnerChanged(Default::default(), target).into());
	}

	set_team {
		let (caller, _) = create_default_asset::<T>(10);
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), Default::default(), target0.clone(), target1.clone(), target2.clone())
	verify {
		assert_last_event::<T>(RawEvent::TeamChanged(
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
		assert_last_event::<T>(RawEvent::MaxZombiesChanged(Default::default(), max_zombies).into());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};

	#[test]
	fn create() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_create::<Test>().is_ok());
		});
	}

	#[test]
	fn force_create() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_force_create::<Test>().is_ok());
		});
	}

	#[test]
	fn destroy() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_destroy::<Test>().is_ok());
		});
	}

	#[test]
	fn force_destroy() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_force_destroy::<Test>().is_ok());
		});
	}

	#[test]
	fn mint() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_mint::<Test>().is_ok());
		});
	}

	#[test]
	fn burn() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_burn::<Test>().is_ok());
		});
	}

	#[test]
	fn transfer() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_transfer::<Test>().is_ok());
		});
	}

	#[test]
	fn force_transfer() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_force_transfer::<Test>().is_ok());
		});
	}

	#[test]
	fn freeze() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_freeze::<Test>().is_ok());
		});
	}

	#[test]
	fn thaw() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_thaw::<Test>().is_ok());
		});
	}

	#[test]
	fn transfer_ownership() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_transfer_ownership::<Test>().is_ok());
		});
	}

	#[test]
	fn set_team() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_set_team::<Test>().is_ok());
		});
	}

	#[test]
	fn set_max_zombies() {
		new_test_ext().execute_with(|| {
			assert!(test_benchmark_set_max_zombies::<Test>().is_ok());
		});
	}
}
