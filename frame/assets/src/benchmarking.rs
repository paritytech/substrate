// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Staking pallet benchmarking.

use super::*;
use sp_std::prelude::*;
use sp_runtime::traits::Bounded;
use frame_system::RawOrigin as SystemOrigin;
use frame_support::assert_ok;
use frame_benchmarking::{benchmarks, account, whitelisted_caller};

use crate::Module as Assets;

const SEED: u32 = 0;

fn create_default_asset<T: Trait>(max_zombies: u32)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let root = SystemOrigin::Root.into();
	assert_ok!(Assets::<T>::force_create(
		root,
		Default::default(),
		caller_lookup.clone(),
		max_zombies,
		1.into(),
	));
	(caller, caller_lookup)
}

fn create_default_minted_asset<T: Trait>(max_zombies: u32, amount: T::Balance)
	-> (T::AccountId, <T::Lookup as StaticLookup>::Source)
{
	let (caller, caller_lookup)  = create_default_asset::<T>(max_zombies);
	assert_ok!(Assets::<T>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
		caller_lookup.clone(),
		amount,
	));
	(caller, caller_lookup)
}

benchmarks! {
	_ { }

	create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup, 1, 1.into())
	verify {
		assert!(true)
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller);
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, 1, 1.into())
	verify {
		assert!(true)
	}

	destroy {
		let (caller, _) = create_default_asset::<T>(10);
	}: _(SystemOrigin::Signed(caller), Default::default())
	verify {
		assert!(true)
	}

	force_destroy {
		let _ = create_default_asset::<T>(10);
	}: _(SystemOrigin::Root, Default::default())
	verify {
		assert!(true)
	}

	mint {
		let (caller, caller_lookup) = create_default_asset::<T>(10);
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup, 100.into())
	verify {
		assert!(true)
	}

	burn {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100.into());
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup, 100.into())
	verify {
		assert!(true)
	}

	transfer {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100.into());
		let target = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target);
	}: _(SystemOrigin::Signed(caller), Default::default(), target_lookup, 100.into())
	verify {
		assert!(true)
	}

	force_transfer {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100.into());
		let target = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target);
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup, target_lookup, 100.into())
	verify {
		assert!(true)
	}

	freeze {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100.into());
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup)
	verify {
		assert!(true)
	}

	thaw {
		let (caller, caller_lookup) = create_default_minted_asset::<T>(10, 100.into());
		assert_ok!(Assets::<T>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			Default::default(),
			caller_lookup.clone()
		));
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup)
	verify {
		assert!(true)
	}

	transfer_ownership {
		let (caller, _) = create_default_asset::<T>(10);
		let target = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target);
	}: _(SystemOrigin::Signed(caller), Default::default(), target_lookup)
	verify {
		assert!(true)
	}

	set_team {
		let (caller, _) = create_default_asset::<T>(10);
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), Default::default(), target0, target1, target2)
	verify {
		assert!(true)
	}

	set_max_zombies {
		let (caller, _) = create_default_asset::<T>(10);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), 100)
	verify {
		assert!(true)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};

	#[test]
	fn create() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_create::<Test>());
		});
	}

	#[test]
	fn force_create() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_force_create::<Test>());
		});
	}

	#[test]
	fn destroy() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_destroy::<Test>());
		});
	}

	#[test]
	fn force_destroy() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_force_destroy::<Test>());
		});
	}

	#[test]
	fn mint() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_mint::<Test>());
		});
	}

	#[test]
	fn burn() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_burn::<Test>());
		});
	}

	#[test]
	fn transfer() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_transfer::<Test>());
		});
	}

	#[test]
	fn force_transfer() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_force_transfer::<Test>());
		});
	}

	#[test]
	fn freeze() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_freeze::<Test>());
		});
	}

	#[test]
	fn thaw() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_thaw::<Test>());
		});
	}

	#[test]
	fn transfer_ownership() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_transfer_ownership::<Test>());
		});
	}

	#[test]
	fn set_team() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set_team::<Test>());
		});
	}

	#[test]
	fn set_max_zombies() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set_max_zombies::<Test>());
		});
	}
}
