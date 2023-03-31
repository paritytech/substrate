// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use crate::Pallet as Balances;

use frame_benchmarking::v2::*;
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded;
use types::ExtraFlags;

const SEED: u32 = 0;
// existential deposit multiplier
const ED_MULTIPLIER: u32 = 10;

#[instance_benchmarks]
mod benchmarks {
	use super::*;

	// Benchmark `transfer` extrinsic with the worst possible conditions:
	// * Transfer will kill the sender account.
	// * Transfer will create the recipient account.
	#[benchmark]
	fn transfer_allow_death() {
		let existential_deposit = T::ExistentialDeposit::get();
		let caller = whitelisted_caller();

		// Give some multiple of the existential deposit
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account,
		// and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());
		let transfer_amount =
			existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1u32.into();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount);

		assert_eq!(Balances::<T, I>::free_balance(&caller), Zero::zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), transfer_amount);
	}

	// Benchmark `transfer` with the best possible condition:
	// * Both accounts exist and will continue to exist.
	#[benchmark(extra)]
	fn transfer_best_case() {
		let caller = whitelisted_caller();
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());

		// Give the sender account max funds for transfer (their account will never reasonably be
		// killed).
		let _ =
			<Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, T::Balance::max_value());

		// Give the recipient account existential deposit (thus their account already exists).
		let existential_deposit = T::ExistentialDeposit::get();
		let _ =
			<Balances<T, I> as Currency<_>>::make_free_balance_be(&recipient, existential_deposit);
		let transfer_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());

		#[extrinsic_call]
		transfer_allow_death(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount);

		assert!(!Balances::<T, I>::free_balance(&caller).is_zero());
		assert!(!Balances::<T, I>::free_balance(&recipient).is_zero());
	}

	// Benchmark `transfer_keep_alive` with the worst possible condition:
	// * The recipient account is created.
	#[benchmark]
	fn transfer_keep_alive() {
		let caller = whitelisted_caller();
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());

		// Give the sender account max funds, thus a transfer will not kill account.
		let _ =
			<Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, T::Balance::max_value());
		let existential_deposit = T::ExistentialDeposit::get();
		let transfer_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount);

		assert!(!Balances::<T, I>::free_balance(&caller).is_zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), transfer_amount);
	}

	// Benchmark `force_set_balance` coming from ROOT account. This always creates an account.
	#[benchmark]
	fn force_set_balance_creating() {
		let user: T::AccountId = account("user", 0, SEED);
		let user_lookup = T::Lookup::unlookup(user.clone());

		// Give the user some initial balance.
		let existential_deposit = T::ExistentialDeposit::get();
		let balance_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&user, balance_amount);

		#[extrinsic_call]
		force_set_balance(RawOrigin::Root, user_lookup, balance_amount);

		assert_eq!(Balances::<T, I>::free_balance(&user), balance_amount);
	}

	// Benchmark `force_set_balance` coming from ROOT account. This always kills an account.
	#[benchmark]
	fn force_set_balance_killing() {
		let user: T::AccountId = account("user", 0, SEED);
		let user_lookup = T::Lookup::unlookup(user.clone());

		// Give the user some initial balance.
		let existential_deposit = T::ExistentialDeposit::get();
		let balance_amount = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&user, balance_amount);

		#[extrinsic_call]
		force_set_balance(RawOrigin::Root, user_lookup, Zero::zero());

		assert!(Balances::<T, I>::free_balance(&user).is_zero());
	}

	// Benchmark `force_transfer` extrinsic with the worst possible conditions:
	// * Transfer will kill the sender account.
	// * Transfer will create the recipient account.
	#[benchmark]
	fn force_transfer() {
		let existential_deposit = T::ExistentialDeposit::get();
		let source: T::AccountId = account("source", 0, SEED);
		let source_lookup = T::Lookup::unlookup(source.clone());

		// Give some multiple of the existential deposit
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&source, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account,
		// and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());
		let transfer_amount =
			existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1u32.into();

		#[extrinsic_call]
		_(RawOrigin::Root, source_lookup, recipient_lookup, transfer_amount);

		assert_eq!(Balances::<T, I>::free_balance(&source), Zero::zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), transfer_amount);
	}

	// This benchmark performs the same operation as `transfer` in the worst case scenario,
	// but additionally introduces many new users into the storage, increasing the the merkle
	// trie and PoV size.
	#[benchmark(extra)]
	fn transfer_increasing_users(u: Linear<0, 1_000>) {
		// 1_000 is not very much, but this upper bound can be controlled by the CLI.
		let existential_deposit = T::ExistentialDeposit::get();
		let caller = whitelisted_caller();

		// Give some multiple of the existential deposit
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account,
		// and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());
		let transfer_amount =
			existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1u32.into();

		// Create a bunch of users in storage.
		for i in 0..u {
			// The `account` function uses `blake2_256` to generate unique accounts, so these
			// should be quite random and evenly distributed in the trie.
			let new_user: T::AccountId = account("new_user", i, SEED);
			let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&new_user, balance);
		}

		#[extrinsic_call]
		transfer_allow_death(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount);

		assert_eq!(Balances::<T, I>::free_balance(&caller), Zero::zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), transfer_amount);
	}

	// Benchmark `transfer_all` with the worst possible condition:
	// * The recipient account is created
	// * The sender is killed
	#[benchmark]
	fn transfer_all() {
		let caller = whitelisted_caller();
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());

		// Give some multiple of the existential deposit
		let existential_deposit = T::ExistentialDeposit::get();
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, balance);

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), recipient_lookup, false);

		assert!(Balances::<T, I>::free_balance(&caller).is_zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), balance);
	}

	#[benchmark]
	fn force_unreserve() -> Result<(), BenchmarkError> {
		let user: T::AccountId = account("user", 0, SEED);
		let user_lookup = T::Lookup::unlookup(user.clone());

		// Give some multiple of the existential deposit
		let ed = T::ExistentialDeposit::get();
		let balance = ed + ed;
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&user, balance);

		// Reserve the balance
		<Balances<T, I> as ReservableCurrency<_>>::reserve(&user, ed)?;
		assert_eq!(Balances::<T, I>::reserved_balance(&user), ed);
		assert_eq!(Balances::<T, I>::free_balance(&user), ed);

		#[extrinsic_call]
		_(RawOrigin::Root, user_lookup, balance);

		assert!(Balances::<T, I>::reserved_balance(&user).is_zero());
		assert_eq!(Balances::<T, I>::free_balance(&user), ed + ed);

		Ok(())
	}

	#[benchmark]
	fn upgrade_accounts(u: Linear<1, 1_000>) {
		let caller: T::AccountId = whitelisted_caller();
		let who = (0..u)
			.into_iter()
			.map(|i| -> T::AccountId {
				let user = account("old_user", i, SEED);
				let account = AccountData {
					free: T::ExistentialDeposit::get(),
					reserved: T::ExistentialDeposit::get(),
					frozen: Zero::zero(),
					flags: ExtraFlags::old_logic(),
				};
				frame_system::Pallet::<T>::inc_providers(&user);
				assert!(T::AccountStore::try_mutate_exists(&user, |a| -> DispatchResult {
					*a = Some(account);
					Ok(())
				})
				.is_ok());
				assert!(!Balances::<T, I>::account(&user).flags.is_new_logic());
				assert_eq!(frame_system::Pallet::<T>::providers(&user), 1);
				assert_eq!(frame_system::Pallet::<T>::consumers(&user), 0);
				user
			})
			.collect();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), who);

		for i in 0..u {
			let user: T::AccountId = account("old_user", i, SEED);
			assert!(Balances::<T, I>::account(&user).flags.is_new_logic());
			assert_eq!(frame_system::Pallet::<T>::providers(&user), 1);
			assert_eq!(frame_system::Pallet::<T>::consumers(&user), 1);
		}
	}

	impl_benchmark_test_suite! {
		Balances,
		crate::tests::ExtBuilder::default().build(),
		crate::tests::Test,
	}
}
