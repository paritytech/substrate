// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use crate::Pallet;
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, Get};
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded;

const SEED: u32 = 0;
const DEFAULT_DELAY: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn get_total_deposit<T: Config>(
	bounded_friends: &FriendsOf<T>,
) -> Option<<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance>
{
	let friend_deposit = T::FriendDepositFactor::get()
		.checked_mul(&bounded_friends.len().saturated_into())
		.unwrap();

	T::ConfigDepositBase::get().checked_add(&friend_deposit)
}

fn generate_friends<T: Config>(num: u32) -> Vec<<T as frame_system::Config>::AccountId> {
	// Create friends
	let mut friends = (0..num).map(|x| account("friend", x, SEED)).collect::<Vec<_>>();
	// Sort
	friends.sort();

	for friend in 0..friends.len() {
		// Top up accounts of friends
		T::Currency::make_free_balance_be(
			&friends.get(friend).unwrap(),
			BalanceOf::<T>::max_value(),
		);
	}

	friends
}

fn add_caller_and_generate_friends<T: Config>(
	caller: T::AccountId,
	num: u32,
) -> Vec<<T as frame_system::Config>::AccountId> {
	// Create friends
	let mut friends = generate_friends::<T>(num - 1);

	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

	friends.push(caller);

	// Sort
	friends.sort();

	friends
}

fn insert_recovery_account<T: Config>(caller: &T::AccountId, account: &T::AccountId) {
	T::Currency::make_free_balance_be(&account, BalanceOf::<T>::max_value());

	let n = T::MaxFriends::get();

	let friends = generate_friends::<T>(n);

	let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

	// Get deposit for recovery
	let total_deposit = get_total_deposit::<T>(&bounded_friends).unwrap();

	let recovery_config = RecoveryConfig {
		delay_period: DEFAULT_DELAY.into(),
		deposit: total_deposit,
		friends: bounded_friends,
		threshold: n as u16,
	};

	// Reserve deposit for recovery
	T::Currency::reserve(&caller, total_deposit).unwrap();

	<Recoverable<T>>::insert(&account, recovery_config);
}

benchmarks! {
	as_recovered {
		let caller: T::AccountId = whitelisted_caller();
		let recovered_account: T::AccountId = account("recovered_account", 0, SEED);
		let call: <T as Config>::Call = frame_system::Call::<T>::remark { remark: vec![] }.into();

		Proxy::<T>::insert(&caller, &recovered_account);
	}: _(
		RawOrigin::Signed(caller),
		recovered_account,
		Box::new(call)
	)

	set_recovered {
		let lost: T::AccountId = whitelisted_caller();
		let rescuer: T::AccountId = whitelisted_caller();
	}: _(
		RawOrigin::Root,
		lost.clone(),
		rescuer.clone()
	) verify {
		assert_last_event::<T>(
			Event::AccountRecovered {
				lost_account: lost,
				rescuer_account: rescuer,
			}.into()
		);
	}

	create_recovery {
		let n in 1 .. T::MaxFriends::get();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>(n);
	}: _(
		RawOrigin::Signed(caller.clone()),
		friends,
		n as u16,
		DEFAULT_DELAY.into()
	) verify {
		assert_last_event::<T>(Event::RecoveryCreated { account: caller }.into());
	}

	initiate_recovery {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let lost_account: T::AccountId = account("lost_account", 0, SEED);

		insert_recovery_account::<T>(&caller, &lost_account);
	}: _(
		RawOrigin::Signed(caller.clone()),
		lost_account.clone()
	) verify {
		assert_last_event::<T>(
			Event::RecoveryInitiated {
				lost_account: lost_account,
				rescuer_account: caller,
			}.into()
		);
	}

	vouch_recovery {
		let n in 1 .. T::MaxFriends::get();

		let caller: T::AccountId = whitelisted_caller();
		let lost_account: T::AccountId = account("lost_account", 0, SEED);
		let rescuer_account: T::AccountId = account("rescuer_account", 0, SEED);

		// Create friends
		let friends = add_caller_and_generate_friends::<T>(caller.clone(), n);
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		// Get deposit for recovery
		let total_deposit = get_total_deposit::<T>(&bounded_friends).unwrap();

		let recovery_config = RecoveryConfig {
			delay_period: DEFAULT_DELAY.into(),
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold: n as u16,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&lost_account, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: DEFAULT_DELAY.into(),
			deposit: total_deposit,
			friends: generate_friends::<T>(n - 1).try_into().unwrap(),
		};

		// Create the active recovery storage item
		<ActiveRecoveries<T>>::insert(&lost_account, &rescuer_account, recovery_status);

	}: _(
		RawOrigin::Signed(caller.clone()),
		lost_account.clone(),
		rescuer_account.clone()
	) verify {
		assert_last_event::<T>(
			Event::RecoveryVouched {
				lost_account: lost_account,
				rescuer_account: rescuer_account,
				sender: caller,
			}.into()
		);
	}

	claim_recovery {
		let n in 1 .. T::MaxFriends::get();

		let caller: T::AccountId = whitelisted_caller();
		let lost_account: T::AccountId = account("lost_account", 0, SEED);

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>(n);
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		// Get deposit for recovery
		let total_deposit = get_total_deposit::<T>(&bounded_friends).unwrap();

		let recovery_config = RecoveryConfig {
			delay_period: 0u32.into(),
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold: n as u16,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&lost_account, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: 0u32.into(),
			deposit: total_deposit,
			friends: bounded_friends.clone(),
		};

		// Create the active recovery storage item
		<ActiveRecoveries<T>>::insert(&lost_account, &caller, recovery_status);
	}: _(
		RawOrigin::Signed(caller.clone()),
		lost_account.clone()
	) verify {
		assert_last_event::<T>(
			Event::AccountRecovered {
				lost_account: lost_account,
				rescuer_account: caller,
			}.into()
		);
	}

	close_recovery {
		let caller: T::AccountId = whitelisted_caller();
		let rescuer_account: T::AccountId = account("rescuer_account", 0, SEED);

		let n in 1 .. T::MaxFriends::get();

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		T::Currency::make_free_balance_be(&rescuer_account, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>(n);
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		// Get deposit for recovery
		let total_deposit = get_total_deposit::<T>(&bounded_friends).unwrap();

		let recovery_config = RecoveryConfig {
			delay_period: DEFAULT_DELAY.into(),
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold: n as u16,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&caller, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: DEFAULT_DELAY.into(),
			deposit: total_deposit,
			friends: bounded_friends.clone(),
		};

		// Create the active recovery storage item
		<ActiveRecoveries<T>>::insert(&caller, &rescuer_account, recovery_status);
	}: _(
		RawOrigin::Signed(caller.clone()),
		rescuer_account.clone()
	) verify {
		assert_last_event::<T>(
			Event::RecoveryClosed {
				lost_account: caller,
				rescuer_account: rescuer_account,
			}.into()
		);
	}

	remove_recovery {
		let n in 1 .. T::MaxFriends::get();

		let caller: T::AccountId = whitelisted_caller();

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>(n);
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		// Get deposit for recovery
		let total_deposit = get_total_deposit::<T>(&bounded_friends).unwrap();

		let recovery_config = RecoveryConfig {
			delay_period: DEFAULT_DELAY.into(),
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold: n as u16,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&caller, recovery_config);

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();
	}: _(
		RawOrigin::Signed(caller.clone())
	) verify {
		assert_last_event::<T>(
			Event::RecoveryRemoved {
				lost_account: caller
			}.into()
		);
	}

	cancel_recovered {
		let caller: T::AccountId = whitelisted_caller();
		let account: T::AccountId = account("account", 0, SEED);

		frame_system::Pallet::<T>::inc_providers(&caller);

		frame_system::Pallet::<T>::inc_consumers(&caller)?;

		Proxy::<T>::insert(&caller, &account);
	}: _(
		RawOrigin::Signed(caller),
		account
	)

	impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test);
}
