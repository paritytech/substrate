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

use sp_runtime::traits::Bounded;
use frame_system::RawOrigin as SystemOrigin;
use frame_support::assert_ok;
use frame_benchmarking::{benchmarks, whitelisted_caller};

use crate::Module as Assets;

/*
use frame_system::EventRecord;
fn assert_last_event<T: Trait>(generic_event: <T as Trait>::Event) {
	let events = System::<T>::events();
	let system_event: <T as frame_system::Trait>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}
*/

benchmarks! {
	_ { }

	create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(SystemOrigin::Signed(caller), Default::default(), caller_lookup, 1, 1.into())
	verify {
		assert!(true)
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller);
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, 1, 1.into())
	verify {
		assert!(true)
	}

	destroy {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		let root = SystemOrigin::Root.into();
		assert_ok!(Assets::<T>::force_create(root, Default::default(), caller_lookup, 1, 1.into()));
	}: _(SystemOrigin::Signed(caller), Default::default())
	verify {
		assert!(true)
	}

	force_destroy {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		let root = SystemOrigin::Root.into();
		assert_ok!(Assets::<T>::force_create(root, Default::default(), caller_lookup, 1, 1.into()));
	}: _(SystemOrigin::Root, Default::default())
	verify {
		assert!(true)
	}

	/*mint {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	burn {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	transfer {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	force_transfer {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	freeze {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	thaw {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	transfer_ownership {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	set_team {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}

	set_max_zombies {
		let caller: T::AccountId = whitelisted_caller();
	}: _(SystemOrigin::Signed(caller))
	verify {
		assert(true)
	}*/
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
/*
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
	}*/
}
