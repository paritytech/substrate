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
use frame_system::RawOrigin;
use sp_runtime::traits::BlockNumberProvider;

const SEED: u32 = 0;

#[allow(dead_code)]
fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn block_number<T: Config>() -> T::BlockNumber {
	frame_system::Pallet::<T>::current_block_number()
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
		let friends = vec![
			account("friend_0", 0, SEED),
			account("friend_1", 1, SEED),
			account("friend_2", 2, SEED),
			account("friend_3", 3, SEED),
			account("friend_4", 4, SEED)
		];
		let threshold: u16 = 6;
		let delay_period = block_number::<T>();
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
		let lost_account: T::AccountId = account("lost_account", 0, SEED);
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
