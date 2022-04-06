// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use frame_benchmarking::{benchmarks, whitelisted_caller, account};
use frame_support::traits::{Currency, Get};
use frame_system::RawOrigin;
use sp_runtime::traits::{BlockNumberProvider, Bounded};
use crate::Pallet;

const SEED: u32 = 0;

#[allow(dead_code)]
fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn block_number<T: Config>() -> T::BlockNumber {
	frame_system::Pallet::<T>::current_block_number()
}

fn generate_friends<T: Config>() -> Vec<<T as frame_system::Config>::AccountId> {
	// Create friends
	let mut friends = vec![
		account("friend_0", 0, SEED),
		account("friend_1", 1, SEED),
		account("friend_2", 2, SEED),
		account("friend_3", 3, SEED),
		account("friend_4", 4, SEED),
		account("friend_5", 5, SEED),
		account("friend_6", 6, SEED),
		account("friend_7", 7, SEED),
	];
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

fn add_caller_and_generate_friends<T: Config>(caller: T::AccountId) -> Vec<<T as frame_system::Config>::AccountId> {
	// Create friends
	let mut friends = vec![
		account("friend_0", 0, SEED),
		account("friend_1", 1, SEED),
		account("friend_2", 2, SEED),
		account("friend_3", 3, SEED),
		account("friend_4", 4, SEED),
		account("friend_5", 5, SEED),
		account("friend_6", 6, SEED),
		caller,
	];
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

fn insert_recovery_account<T: Config>(caller: &T::AccountId, account: &T::AccountId) {
	T::Currency::make_free_balance_be(&account, BalanceOf::<T>::max_value());

	let friends = generate_friends::<T>();
	let threshold: u16 = 8;
	let delay_period = block_number::<T>();

	let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

	// Get deposit for recovery
	let friend_deposit = T::FriendDepositFactor::get()
		.checked_mul(&bounded_friends.len().saturated_into())
		.unwrap();
	let total_deposit = T::ConfigDepositBase::get()
		.checked_add(&friend_deposit)
		.unwrap();

	let recovery_config = RecoveryConfig {
		delay_period,
		deposit: total_deposit,
		friends: bounded_friends,
		threshold,
	};

	// Reserve deposit for recovery
	T::Currency::reserve(&caller, total_deposit).unwrap();

	<Recoverable<T>>::insert(&account, recovery_config);
}

benchmarks! {
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
		let caller: T::AccountId = whitelisted_caller();

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>();
		let bounded_friends: FriendsOf<T> = friends.clone().try_into().unwrap();

		let threshold: u16 = 8;
		let delay_period = block_number::<T>();

		// Get deposit for recovery
		let friend_deposit = T::FriendDepositFactor::get()
				.checked_mul(&bounded_friends.len().saturated_into())
				.unwrap();
		let total_deposit = T::ConfigDepositBase::get()
			.checked_add(&friend_deposit)
			.unwrap();

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit)?;
	}: _(
		RawOrigin::Signed(caller.clone()),
		friends,
		threshold,
		delay_period
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
		let caller: T::AccountId = whitelisted_caller();
		let lost_account: T::AccountId = account("lost_account", 0, SEED);
		let rescuer_account: T::AccountId = account("rescuer_account", 0, SEED);

		// Create friends
		let friends = add_caller_and_generate_friends::<T>(caller.clone());
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		let threshold: u16 = 8;
		let delay_period = block_number::<T>();

		// Get deposit for recovery
		let friend_deposit = T::FriendDepositFactor::get()
			.checked_mul(&bounded_friends.len().saturated_into())
			.unwrap();
		let total_deposit = T::ConfigDepositBase::get()
			.checked_add(&friend_deposit)
			.unwrap();

		let recovery_config = RecoveryConfig {
			delay_period,
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&lost_account, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: block_number::<T>(),
			deposit: total_deposit,
			friends: vec![].try_into().unwrap(),
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
		let caller: T::AccountId = whitelisted_caller();
		let lost_account: T::AccountId = account("lost_account", 0, SEED);

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>();
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		let threshold: u16 = 8;
		let delay_period = block_number::<T>();

		// Get deposit for recovery
		let friend_deposit = T::FriendDepositFactor::get()
			.checked_mul(&bounded_friends.len().saturated_into())
			.unwrap();
		let total_deposit = T::ConfigDepositBase::get()
			.checked_add(&friend_deposit)
			.unwrap();

		let recovery_config = RecoveryConfig {
			delay_period,
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&lost_account, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&caller, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: block_number::<T>(),
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

		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		T::Currency::make_free_balance_be(&rescuer_account, BalanceOf::<T>::max_value());

		// Create friends
		let friends = generate_friends::<T>();
		let bounded_friends: FriendsOf<T> = friends.try_into().unwrap();

		let threshold: u16 = 8;
		let delay_period = block_number::<T>();

		// Get deposit for recovery
		let friend_deposit = T::FriendDepositFactor::get()
			.checked_mul(&bounded_friends.len().saturated_into())
			.unwrap();
		let total_deposit = T::ConfigDepositBase::get()
			.checked_add(&friend_deposit)
			.unwrap();

		let recovery_config = RecoveryConfig {
			delay_period,
			deposit: total_deposit.clone(),
			friends: bounded_friends.clone(),
			threshold,
		};

		// Create the recovery config storage item
		<Recoverable<T>>::insert(&caller, recovery_config.clone());

		// Reserve deposit for recovery
		T::Currency::reserve(&rescuer_account, total_deposit).unwrap();

		// Create an active recovery status
		let recovery_status = ActiveRecovery {
			created: block_number::<T>(),
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
		let caller: T::AccountId = whitelisted_caller();
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

		let count_before = frame_system::Pallet::<T>::consumers(&caller);

		frame_system::Pallet::<T>::dec_consumers(&caller);

		let count_after = frame_system::Pallet::<T>::consumers(&caller);
	}: _(
		RawOrigin::Signed(caller.clone()),
		account.clone()
	) verify {
		assert_ne!(count_before, count_after);
	}

	impl_benchmark_test_suite!(Recovery, crate::mock::new_test_ext(), crate::mock::Test);
}
