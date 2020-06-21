// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Macro for creating the tests for the module.

#![cfg(test)]

#[derive(Debug)]
pub struct CallWithDispatchInfo;
impl sp_runtime::traits::Dispatchable for CallWithDispatchInfo {
	type Origin = ();
	type Trait = ();
	type Info = frame_support::weights::DispatchInfo;
	type PostInfo = frame_support::weights::PostDispatchInfo;

	fn dispatch(self, _origin: Self::Origin)
		-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
			panic!("Do not use dummy implementation for dispatch.");
	}
}

#[macro_export]
macro_rules! decl_tests {
	($test:ty, $ext_builder:ty, $existential_deposit:expr) => {

		use crate::*;
		use sp_runtime::{FixedPointNumber, traits::{SignedExtension, BadOrigin}};
		use frame_support::{
			assert_noop, assert_ok, assert_err,
			traits::{
				LockableCurrency, LockIdentifier, WithdrawReason, WithdrawReasons,
				Currency, ReservableCurrency, ExistenceRequirement::AllowDeath, StoredMap
			}
		};
		use pallet_transaction_payment::{ChargeTransactionPayment, Multiplier};
		use frame_system::RawOrigin;

		const ID_1: LockIdentifier = *b"1       ";
		const ID_2: LockIdentifier = *b"2       ";

		pub type System = frame_system::Module<$test>;
		pub type Balances = Module<$test>;

		pub const CALL: &<$test as frame_system::Trait>::Call = &$crate::tests::CallWithDispatchInfo;

		/// create a transaction info struct from weight. Handy to avoid building the whole struct.
		pub fn info_from_weight(w: Weight) -> DispatchInfo {
			DispatchInfo { weight: w, ..Default::default() }
		}

		fn events() -> Vec<Event> {
			let evt = System::events().into_iter().map(|evt| evt.event).collect::<Vec<_>>();

			System::reset_events();

			evt
		}

		fn last_event() -> Event {
			system::Module::<Test>::events().pop().expect("Event expected").event
		}

		#[test]
		fn basic_locking_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				assert_eq!(Balances::free_balance(1), 10);
				Balances::set_lock(ID_1, &1, 9, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 5, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
			});
		}

		#[test]
		fn account_should_be_reaped() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				assert_eq!(Balances::free_balance(1), 10);
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 10, AllowDeath));
				assert!(!<<Test as Trait>::AccountStore as StoredMap<u64, AccountData<u64>>>::is_explicit(&1));
			});
		}

		#[test]
		fn partial_locking_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			});
		}

		#[test]
		fn lock_removal_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::all());
				Balances::remove_lock(ID_1, &1);
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			});
		}

		#[test]
		fn lock_replacement_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::all());
				Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			});
		}

		#[test]
		fn double_locking_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
				Balances::set_lock(ID_2, &1, 5, WithdrawReasons::all());
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			});
		}

		#[test]
		fn combination_locking_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::none());
				Balances::set_lock(ID_2, &1, 0, WithdrawReasons::all());
				assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			});
		}

		#[test]
		fn lock_value_extension_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				Balances::extend_lock(ID_1, &1, 2, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				Balances::extend_lock(ID_1, &1, 8, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
			});
		}

		#[test]
		fn lock_reasons_should_work() {
			<$ext_builder>::default()
				.existential_deposit(1)
				.monied(true)
				.build()
				.execute_with(|| {
					pallet_transaction_payment::NextFeeMultiplier::put(Multiplier::saturating_from_integer(1));
					Balances::set_lock(ID_1, &1, 10, WithdrawReason::Reserve.into());
					assert_noop!(
						<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath),
						Error::<$test, _>::LiquidityRestrictions
					);
					assert_noop!(
						<Balances as ReservableCurrency<_>>::reserve(&1, 1),
						Error::<$test, _>::LiquidityRestrictions,
					);
					assert!(<ChargeTransactionPayment<$test> as SignedExtension>::pre_dispatch(
						ChargeTransactionPayment::from(1),
						&1,
						CALL,
						&info_from_weight(1),
						1,
					).is_err());
					assert!(<ChargeTransactionPayment<$test> as SignedExtension>::pre_dispatch(
						ChargeTransactionPayment::from(0),
						&1,
						CALL,
						&info_from_weight(1),
						1,
					).is_ok());

					Balances::set_lock(ID_1, &1, 10, WithdrawReason::TransactionPayment.into());
					assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
					assert_ok!(<Balances as ReservableCurrency<_>>::reserve(&1, 1));
					assert!(<ChargeTransactionPayment<$test> as SignedExtension>::pre_dispatch(
						ChargeTransactionPayment::from(1),
						&1,
						CALL,
						&info_from_weight(1),
						1,
					).is_err());
					assert!(<ChargeTransactionPayment<$test> as SignedExtension>::pre_dispatch(
						ChargeTransactionPayment::from(0),
						&1,
						CALL,
						&info_from_weight(1),
						1,
					).is_err());
				});
		}

		#[test]
		fn lock_block_number_extension_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, 10, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				System::set_block_number(2);
				Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
			});
		}

		#[test]
		fn lock_reasons_extension_should_work() {
			<$ext_builder>::default().existential_deposit(1).monied(true).build().execute_with(|| {
				Balances::set_lock(ID_1, &1, 10, WithdrawReason::Transfer.into());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::none());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
				Balances::extend_lock(ID_1, &1, 10, WithdrawReason::Reserve.into());
				assert_noop!(
					<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
					Error::<$test, _>::LiquidityRestrictions
				);
			});
		}

		#[test]
		fn default_indexing_on_new_accounts_should_not_work2() {
			<$ext_builder>::default()
				.existential_deposit(10)
				.monied(true)
				.build()
				.execute_with(|| {
					assert_eq!(Balances::is_dead_account(&5), true);
					// account 5 should not exist
					// ext_deposit is 10, value is 9, not satisfies for ext_deposit
					assert_noop!(
						Balances::transfer(Some(1).into(), 5, 9),
						Error::<$test, _>::ExistentialDeposit,
					);
					assert_eq!(Balances::is_dead_account(&5), true); // account 5 should not exist
					assert_eq!(Balances::free_balance(1), 100);
				});
		}

		#[test]
		fn reserved_balance_should_prevent_reclaim_count() {
			<$ext_builder>::default()
				.existential_deposit(256 * 1)
				.monied(true)
				.build()
				.execute_with(|| {
					System::inc_account_nonce(&2);
					assert_eq!(Balances::is_dead_account(&2), false);
					assert_eq!(Balances::is_dead_account(&5), true);
					assert_eq!(Balances::total_balance(&2), 256 * 20);

					assert_ok!(Balances::reserve(&2, 256 * 19 + 1)); // account 2 becomes mostly reserved
					assert_eq!(Balances::free_balance(2), 255); // "free" account deleted."
					assert_eq!(Balances::total_balance(&2), 256 * 20); // reserve still exists.
					assert_eq!(Balances::is_dead_account(&2), false);
					assert_eq!(System::account_nonce(&2), 1);

					// account 4 tries to take index 1 for account 5.
					assert_ok!(Balances::transfer(Some(4).into(), 5, 256 * 1 + 0x69));
					assert_eq!(Balances::total_balance(&5), 256 * 1 + 0x69);
					assert_eq!(Balances::is_dead_account(&5), false);

					assert!(Balances::slash(&2, 256 * 19 + 2).1.is_zero()); // account 2 gets slashed
					// "reserve" account reduced to 255 (below ED) so account deleted
					assert_eq!(Balances::total_balance(&2), 0);
					assert_eq!(System::account_nonce(&2), 0);    // nonce zero
					assert_eq!(Balances::is_dead_account(&2), true);

					// account 4 tries to take index 1 again for account 6.
					assert_ok!(Balances::transfer(Some(4).into(), 6, 256 * 1 + 0x69));
					assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
					assert_eq!(Balances::is_dead_account(&6), false);
				});
		}

		#[test]
		fn reward_should_work() {
			<$ext_builder>::default().monied(true).build().execute_with(|| {
				assert_eq!(Balances::total_balance(&1), 10);
				assert_ok!(Balances::deposit_into_existing(&1, 10).map(drop));
				assert_eq!(Balances::total_balance(&1), 20);
				assert_eq!(<TotalIssuance<$test>>::get(), 120);
			});
		}

		#[test]
		fn dust_account_removal_should_work() {
			<$ext_builder>::default()
				.existential_deposit(100)
				.monied(true)
				.build()
				.execute_with(|| {
					System::inc_account_nonce(&2);
					assert_eq!(System::account_nonce(&2), 1);
					assert_eq!(Balances::total_balance(&2), 2000);
					 // index 1 (account 2) becomes zombie
					assert_ok!(Balances::transfer(Some(2).into(), 5, 1901));
					assert_eq!(Balances::total_balance(&2), 0);
					assert_eq!(Balances::total_balance(&5), 1901);
					assert_eq!(System::account_nonce(&2), 0);
				});
		}

		#[test]
		fn balance_works() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 42);
				assert_eq!(Balances::free_balance(1), 42);
				assert_eq!(Balances::reserved_balance(1), 0);
				assert_eq!(Balances::total_balance(&1), 42);
				assert_eq!(Balances::free_balance(2), 0);
				assert_eq!(Balances::reserved_balance(2), 0);
				assert_eq!(Balances::total_balance(&2), 0);
			});
		}

		#[test]
		fn balance_transfer_works() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::transfer(Some(1).into(), 2, 69));
				assert_eq!(Balances::total_balance(&1), 42);
				assert_eq!(Balances::total_balance(&2), 69);
			});
		}

		#[test]
		fn force_transfer_works() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_noop!(
					Balances::force_transfer(Some(2).into(), 1, 2, 69),
					BadOrigin,
				);
				assert_ok!(Balances::force_transfer(RawOrigin::Root.into(), 1, 2, 69));
				assert_eq!(Balances::total_balance(&1), 42);
				assert_eq!(Balances::total_balance(&2), 69);
			});
		}

		#[test]
		fn reserving_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);

				assert_eq!(Balances::total_balance(&1), 111);
				assert_eq!(Balances::free_balance(1), 111);
				assert_eq!(Balances::reserved_balance(1), 0);

				assert_ok!(Balances::reserve(&1, 69));

				assert_eq!(Balances::total_balance(&1), 111);
				assert_eq!(Balances::free_balance(1), 42);
				assert_eq!(Balances::reserved_balance(1), 69);
			});
		}

		#[test]
		fn balance_transfer_when_reserved_should_not_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 69));
				assert_noop!(
					Balances::transfer(Some(1).into(), 2, 69),
					Error::<$test, _>::InsufficientBalance,
				);
			});
		}

		#[test]
		fn deducting_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 69));
				assert_eq!(Balances::free_balance(1), 42);
			});
		}

		#[test]
		fn refunding_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 42);
				Balances::mutate_account(&1, |a| a.reserved = 69);
				Balances::unreserve(&1, 69);
				assert_eq!(Balances::free_balance(1), 111);
				assert_eq!(Balances::reserved_balance(1), 0);
			});
		}

		#[test]
		fn slashing_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 69));
				assert!(Balances::slash(&1, 69).1.is_zero());
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(Balances::reserved_balance(1), 42);
				assert_eq!(<TotalIssuance<$test>>::get(), 42);
			});
		}

		#[test]
		fn slashing_incomplete_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 42);
				assert_ok!(Balances::reserve(&1, 21));
				assert_eq!(Balances::slash(&1, 69).1, 27);
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(Balances::reserved_balance(1), 0);
				assert_eq!(<TotalIssuance<$test>>::get(), 0);
			});
		}

		#[test]
		fn unreserving_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 111));
				Balances::unreserve(&1, 42);
				assert_eq!(Balances::reserved_balance(1), 69);
				assert_eq!(Balances::free_balance(1), 42);
			});
		}

		#[test]
		fn slashing_reserved_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 111));
				assert_eq!(Balances::slash_reserved(&1, 42).1, 0);
				assert_eq!(Balances::reserved_balance(1), 69);
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(<TotalIssuance<$test>>::get(), 69);
			});
		}

		#[test]
		fn slashing_incomplete_reserved_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 42));
				assert_eq!(Balances::slash_reserved(&1, 69).1, 27);
				assert_eq!(Balances::free_balance(1), 69);
				assert_eq!(Balances::reserved_balance(1), 0);
				assert_eq!(<TotalIssuance<$test>>::get(), 69);
			});
		}

		#[test]
		fn repatriating_reserved_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 110);
				let _ = Balances::deposit_creating(&2, 1);
				assert_ok!(Balances::reserve(&1, 110));
				assert_ok!(Balances::repatriate_reserved(&1, &2, 41, Status::Free), 0);
				assert_eq!(
					last_event(),
					Event::balances(RawEvent::ReserveRepatriated(1, 2, 41, Status::Free)),
				);
				assert_eq!(Balances::reserved_balance(1), 69);
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(Balances::reserved_balance(2), 0);
				assert_eq!(Balances::free_balance(2), 42);
			});
		}

		#[test]
		fn transferring_reserved_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 110);
				let _ = Balances::deposit_creating(&2, 1);
				assert_ok!(Balances::reserve(&1, 110));
				assert_ok!(Balances::repatriate_reserved(&1, &2, 41, Status::Reserved), 0);
				assert_eq!(Balances::reserved_balance(1), 69);
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(Balances::reserved_balance(2), 41);
				assert_eq!(Balances::free_balance(2), 1);
			});
		}

		#[test]
		fn transferring_reserved_balance_to_nonexistent_should_fail() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 111);
				assert_ok!(Balances::reserve(&1, 111));
				assert_noop!(Balances::repatriate_reserved(&1, &2, 42, Status::Free), Error::<$test, _>::DeadAccount);
			});
		}

		#[test]
		fn transferring_incomplete_reserved_balance_should_work() {
			<$ext_builder>::default().build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 110);
				let _ = Balances::deposit_creating(&2, 1);
				assert_ok!(Balances::reserve(&1, 41));
				assert_ok!(Balances::repatriate_reserved(&1, &2, 69, Status::Free), 28);
				assert_eq!(Balances::reserved_balance(1), 0);
				assert_eq!(Balances::free_balance(1), 69);
				assert_eq!(Balances::reserved_balance(2), 0);
				assert_eq!(Balances::free_balance(2), 42);
			});
		}

		#[test]
		fn transferring_too_high_value_should_not_panic() {
			<$ext_builder>::default().build().execute_with(|| {
				Balances::make_free_balance_be(&1, u64::max_value());
				Balances::make_free_balance_be(&2, 1);

				assert_err!(
					Balances::transfer(Some(1).into(), 2, u64::max_value()),
					Error::<$test, _>::Overflow,
				);

				assert_eq!(Balances::free_balance(1), u64::max_value());
				assert_eq!(Balances::free_balance(2), 1);
			});
		}

		#[test]
		fn account_create_on_free_too_low_with_other() {
			<$ext_builder>::default().existential_deposit(100).build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 100);
				assert_eq!(<TotalIssuance<$test>>::get(), 100);

				// No-op.
				let _ = Balances::deposit_creating(&2, 50);
				assert_eq!(Balances::free_balance(2), 0);
				assert_eq!(<TotalIssuance<$test>>::get(), 100);
			})
		}

		#[test]
		fn account_create_on_free_too_low() {
			<$ext_builder>::default().existential_deposit(100).build().execute_with(|| {
				// No-op.
				let _ = Balances::deposit_creating(&2, 50);
				assert_eq!(Balances::free_balance(2), 0);
				assert_eq!(<TotalIssuance<$test>>::get(), 0);
			})
		}

		#[test]
		fn account_removal_on_free_too_low() {
			<$ext_builder>::default().existential_deposit(100).build().execute_with(|| {
				assert_eq!(<TotalIssuance<$test>>::get(), 0);

				// Setup two accounts with free balance above the existential threshold.
				let _ = Balances::deposit_creating(&1, 110);
				let _ = Balances::deposit_creating(&2, 110);

				assert_eq!(Balances::free_balance(1), 110);
				assert_eq!(Balances::free_balance(2), 110);
				assert_eq!(<TotalIssuance<$test>>::get(), 220);

				// Transfer funds from account 1 of such amount that after this transfer
				// the balance of account 1 will be below the existential threshold.
				// This should lead to the removal of all balance of this account.
				assert_ok!(Balances::transfer(Some(1).into(), 2, 20));

				// Verify free balance removal of account 1.
				assert_eq!(Balances::free_balance(1), 0);
				assert_eq!(Balances::free_balance(2), 130);

				// Verify that TotalIssuance tracks balance removal when free balance is too low.
				assert_eq!(<TotalIssuance<$test>>::get(), 130);
			});
		}

		#[test]
		fn burn_must_work() {
			<$ext_builder>::default().monied(true).build().execute_with(|| {
				let init_total_issuance = Balances::total_issuance();
				let imbalance = Balances::burn(10);
				assert_eq!(Balances::total_issuance(), init_total_issuance - 10);
				drop(imbalance);
				assert_eq!(Balances::total_issuance(), init_total_issuance);
			});
		}

		#[test]
		fn transfer_keep_alive_works() {
			<$ext_builder>::default().existential_deposit(1).build().execute_with(|| {
				let _ = Balances::deposit_creating(&1, 100);
				assert_noop!(
					Balances::transfer_keep_alive(Some(1).into(), 2, 100),
					Error::<$test, _>::KeepAlive
				);
				assert_eq!(Balances::is_dead_account(&1), false);
				assert_eq!(Balances::total_balance(&1), 100);
				assert_eq!(Balances::total_balance(&2), 0);
			});
		}

		#[test]
		#[should_panic = "the balance of any account should always be more than existential deposit."]
		fn cannot_set_genesis_value_below_ed() {
			($existential_deposit).with(|v| *v.borrow_mut() = 11);
			let mut t = frame_system::GenesisConfig::default().build_storage::<$test>().unwrap();
			let _ = GenesisConfig::<$test> {
				balances: vec![(1, 10)],
			}.assimilate_storage(&mut t).unwrap();
		}

		#[test]
		fn dust_moves_between_free_and_reserved() {
			<$ext_builder>::default()
				.existential_deposit(100)
				.build()
				.execute_with(|| {
					// Set balance to free and reserved at the existential deposit
					assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 100, 0));
					// Check balance
					assert_eq!(Balances::free_balance(1), 100);
					assert_eq!(Balances::reserved_balance(1), 0);

					// Reserve some free balance
					assert_ok!(Balances::reserve(&1, 50));
					// Check balance, the account should be ok.
					assert_eq!(Balances::free_balance(1), 50);
					assert_eq!(Balances::reserved_balance(1), 50);

					// Reserve the rest of the free balance
					assert_ok!(Balances::reserve(&1, 50));
					// Check balance, the account should be ok.
					assert_eq!(Balances::free_balance(1), 0);
					assert_eq!(Balances::reserved_balance(1), 100);

					// Unreserve everything
					Balances::unreserve(&1, 100);
					// Check balance, all 100 should move to free_balance
					assert_eq!(Balances::free_balance(1), 100);
					assert_eq!(Balances::reserved_balance(1), 0);
				});
		}

		#[test]
		fn account_deleted_when_just_dust() {
			<$ext_builder>::default()
				.existential_deposit(100)
				.build()
				.execute_with(|| {
					// Set balance to free and reserved at the existential deposit
					assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 50, 50));
					// Check balance
					assert_eq!(Balances::free_balance(1), 50);
					assert_eq!(Balances::reserved_balance(1), 50);

					// Reserve some free balance
					let _ = Balances::slash(&1, 1);
					// The account should be dead.
					assert!(Balances::is_dead_account(&1));
					assert_eq!(Balances::free_balance(1), 0);
					assert_eq!(Balances::reserved_balance(1), 0);
				});
		}

		#[test]
		fn emit_events_with_reserve_and_unreserve() {
			<$ext_builder>::default()
				.build()
				.execute_with(|| {
					let _ = Balances::deposit_creating(&1, 100);

					System::set_block_number(2);
					let _ = Balances::reserve(&1, 10);

					assert_eq!(
						last_event(),
						Event::balances(RawEvent::Reserved(1, 10)),
					);

					System::set_block_number(3);
					let _ = Balances::unreserve(&1, 5);

					assert_eq!(
						last_event(),
						Event::balances(RawEvent::Unreserved(1, 5)),
					);

					System::set_block_number(4);
					let _ = Balances::unreserve(&1, 6);

					// should only unreserve 5
					assert_eq!(
						last_event(),
						Event::balances(RawEvent::Unreserved(1, 5)),
					);
				});
		}

		#[test]
		fn emit_events_with_existential_deposit() {
			<$ext_builder>::default()
				.existential_deposit(100)
				.build()
				.execute_with(|| {
					assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 100, 0));

					assert_eq!(
						events(),
						[
							Event::system(system::RawEvent::NewAccount(1)),
							Event::balances(RawEvent::Endowed(1, 100)),
							Event::balances(RawEvent::BalanceSet(1, 100, 0)),
						]
					);

					let _ = Balances::slash(&1, 1);

					assert_eq!(
						events(),
						[
							Event::balances(RawEvent::DustLost(1, 99)),
							Event::system(system::RawEvent::KilledAccount(1))
						]
					);
				});
		}

		#[test]
		fn emit_events_with_no_existential_deposit_suicide() {
			<$ext_builder>::default()
				.existential_deposit(0)
				.build()
				.execute_with(|| {
					assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 100, 0));

					assert_eq!(
						events(),
						[
							Event::system(system::RawEvent::NewAccount(1)),
							Event::balances(RawEvent::Endowed(1, 100)),
							Event::balances(RawEvent::BalanceSet(1, 100, 0)),
						]
					);

					let _ = Balances::slash(&1, 100);

					// no events
					assert_eq!(events(), []);

					assert_ok!(System::suicide(Origin::signed(1)));

					assert_eq!(
						events(),
						[
							Event::system(system::RawEvent::KilledAccount(1))
						]
					);
				});
		}
	}
}
