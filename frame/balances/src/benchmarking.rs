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

//! Balances pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use sp_runtime::traits::Bounded;

use crate::Module as Balances;

const SEED: u32 = 0;
// existential deposit multiplier
const ED_MULTIPLIER: u32 = 10;


benchmarks! {
	_ { }

	// Benchmark `transfer` extrinsic with the worst possible conditions:
	// * Transfer will kill the sender account.
	// * Transfer will create the recipient account.
	transfer {
		let existential_deposit = T::ExistentialDeposit::get();
		let caller = whitelisted_caller();

		// Give some multiple of the existential deposit + creation fee + transfer fee
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&caller, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account, and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());
		let transfer_amount = existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1.into();
	}: transfer(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount)
	verify {
		assert_eq!(Balances::<T>::free_balance(&caller), Zero::zero());
		assert_eq!(Balances::<T>::free_balance(&recipient), transfer_amount);
	}

	// Benchmark `transfer` with the best possible condition:
	// * Both accounts exist and will continue to exist.
	#[extra]
	transfer_best_case {
		let caller = whitelisted_caller();
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());

		// Give the sender account max funds for transfer (their account will never reasonably be killed).
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&caller, T::Balance::max_value());

		// Give the recipient account existential deposit (thus their account already exists).
		let existential_deposit = T::ExistentialDeposit::get();
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&recipient, existential_deposit);
		let transfer_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
	}: transfer(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount)
	verify {
		assert!(!Balances::<T>::free_balance(&caller).is_zero());
		assert!(!Balances::<T>::free_balance(&recipient).is_zero());
	}

	// Benchmark `transfer_keep_alive` with the worst possible condition:
	// * The recipient account is created.
	transfer_keep_alive {
		let caller = whitelisted_caller();
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());

		// Give the sender account max funds, thus a transfer will not kill account.
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&caller, T::Balance::max_value());
		let existential_deposit = T::ExistentialDeposit::get();
		let transfer_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
	}: _(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount)
	verify {
		assert!(!Balances::<T>::free_balance(&caller).is_zero());
		assert_eq!(Balances::<T>::free_balance(&recipient), transfer_amount);
	}

	// Benchmark `set_balance` coming from ROOT account. This always creates an account.
	set_balance_creating {
		let user: T::AccountId = account("user", 0, SEED);
		let user_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(user.clone());

		// Give the user some initial balance.
		let existential_deposit = T::ExistentialDeposit::get();
		let balance_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, balance_amount);
	}: set_balance(RawOrigin::Root, user_lookup, balance_amount, balance_amount)
	verify {
		assert_eq!(Balances::<T>::free_balance(&user), balance_amount);
		assert_eq!(Balances::<T>::reserved_balance(&user), balance_amount);
	}

	// Benchmark `set_balance` coming from ROOT account. This always kills an account.
	set_balance_killing {
		let user: T::AccountId = account("user", 0, SEED);
		let user_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(user.clone());

		// Give the user some initial balance.
		let existential_deposit = T::ExistentialDeposit::get();
		let balance_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, balance_amount);
	}: set_balance(RawOrigin::Root, user_lookup, Zero::zero(), Zero::zero())
	verify {
		assert!(Balances::<T>::free_balance(&user).is_zero());
	}

	// Benchmark `force_transfer` extrinsic with the worst possible conditions:
	// * Transfer will kill the sender account.
	// * Transfer will create the recipient account.
	force_transfer {
		let existential_deposit = T::ExistentialDeposit::get();
		let source: T::AccountId = account("source", 0, SEED);
		let source_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(source.clone());

		// Give some multiple of the existential deposit + creation fee + transfer fee
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&source, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account, and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());
		let transfer_amount = existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1.into();
	}: force_transfer(RawOrigin::Root, source_lookup, recipient_lookup, transfer_amount)
	verify {
		assert_eq!(Balances::<T>::free_balance(&source), Zero::zero());
		assert_eq!(Balances::<T>::free_balance(&recipient), transfer_amount);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests_composite::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn transfer() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_transfer::<Test>());
		});
	}

	#[test]
	fn transfer_best_case() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_transfer_best_case::<Test>());
		});
	}

	#[test]
	fn transfer_keep_alive() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_transfer_keep_alive::<Test>());
		});
	}

	#[test]
	fn transfer_set_balance_creating() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_set_balance_creating::<Test>());
		});
	}

	#[test]
	fn transfer_set_balance_killing() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_set_balance_killing::<Test>());
		});
	}

	#[test]
	fn force_transfer() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_force_transfer::<Test>());
		});
	}
}
