// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Tests regarding the functionality of the `Currency` trait set implementations.

use super::*;
use crate::NegativeImbalance;
use frame_support::traits::{
	BalanceStatus::{Free, Reserved},
	Currency,
	ExistenceRequirement::{self, AllowDeath},
	Hooks, LockIdentifier, LockableCurrency, NamedReservableCurrency, ReservableCurrency,
	WithdrawReasons,
};

const ID_1: LockIdentifier = *b"1       ";
const ID_2: LockIdentifier = *b"2       ";

pub const CALL: &<Test as frame_system::Config>::RuntimeCall =
	&RuntimeCall::Balances(crate::Call::transfer_allow_death { dest: 0, value: 0 });

#[test]
fn set_lock_with_amount_zero_removes_lock() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::all());
			Balances::set_lock(ID_1, &1, 0, WithdrawReasons::all());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn set_lock_with_withdraw_reasons_empty_removes_lock() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::all());
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::empty());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn basic_locking_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			Balances::set_lock(ID_1, &1, 9, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 5, AllowDeath),
				TokenError::Frozen
			);
		});
}

#[test]
fn account_should_be_reaped() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 10, AllowDeath));
			assert_eq!(System::providers(&1), 0);
			assert_eq!(System::consumers(&1), 0);
			// Check that the account is dead.
			assert!(!frame_system::Account::<Test>::contains_key(&1));
		});
}

#[test]
fn reap_failed_due_to_provider_and_consumer() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			// SCENARIO: only one provider and there are remaining consumers.
			assert_ok!(System::inc_consumers(&1));
			assert!(!System::can_dec_provider(&1));
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 10, AllowDeath),
				TokenError::Frozen
			);
			assert!(System::account_exists(&1));
			assert_eq!(Balances::free_balance(1), 10);

			// SCENARIO: more than one provider, but will not kill account due to other provider.
			assert_eq!(System::inc_providers(&1), frame_system::IncRefStatus::Existed);
			assert_eq!(System::providers(&1), 2);
			assert!(System::can_dec_provider(&1));
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 10, AllowDeath));
			assert_eq!(System::providers(&1), 1);
			assert!(System::account_exists(&1));
			assert_eq!(Balances::free_balance(1), 0);
		});
}

#[test]
fn partial_locking_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn lock_removal_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::all());
			Balances::remove_lock(ID_1, &1);
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn lock_replacement_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::all());
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn double_locking_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			Balances::set_lock(ID_2, &1, 5, WithdrawReasons::all());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn combination_locking_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, u64::MAX, WithdrawReasons::empty());
			Balances::set_lock(ID_2, &1, 0, WithdrawReasons::all());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
		});
}

#[test]
fn lock_value_extension_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			Balances::extend_lock(ID_1, &1, 2, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			Balances::extend_lock(ID_1, &1, 8, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
				TokenError::Frozen
			);
		});
}

#[test]
fn lock_should_work_reserve() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			pallet_transaction_payment::NextFeeMultiplier::<Test>::put(
				Multiplier::saturating_from_integer(1),
			);
			Balances::set_lock(ID_1, &1, 10, WithdrawReasons::RESERVE);
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath),
				TokenError::Frozen
			);
			assert_noop!(Balances::reserve(&1, 1), Error::<Test>::LiquidityRestrictions,);
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(1),
				&1,
				CALL,
				&info_from_weight(Weight::from_parts(1, 0)),
				1,
			)
			.is_err());
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(0),
				&1,
				CALL,
				&info_from_weight(Weight::from_parts(1, 0)),
				1,
			)
			.is_err());
		});
}

#[test]
fn lock_should_work_tx_fee() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 10, WithdrawReasons::TRANSACTION_PAYMENT);
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath),
				TokenError::Frozen
			);
			assert_noop!(Balances::reserve(&1, 1), Error::<Test>::LiquidityRestrictions,);
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(1),
				&1,
				CALL,
				&info_from_weight(Weight::from_parts(1, 0)),
				1,
			)
			.is_err());
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(0),
				&1,
				CALL,
				&info_from_weight(Weight::from_parts(1, 0)),
				1,
			)
			.is_err());
		});
}

#[test]
fn lock_block_number_extension_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 10, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			System::set_block_number(2);
			Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
				TokenError::Frozen
			);
		});
}

#[test]
fn lock_reasons_extension_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			Balances::set_lock(ID_1, &1, 10, WithdrawReasons::TRANSFER);
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::empty());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
			Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::RESERVE);
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
				TokenError::Frozen
			);
		});
}

#[test]
fn reserved_balance_should_prevent_reclaim_count() {
	ExtBuilder::default()
		.existential_deposit(256 * 1)
		.monied(true)
		.build_and_execute_with(|| {
			System::inc_account_nonce(&2);
			assert_eq!(Balances::total_balance(&2), 256 * 20);
			assert_eq!(System::providers(&2), 1);
			System::inc_providers(&2);
			assert_eq!(System::providers(&2), 2);

			assert_ok!(Balances::reserve(&2, 256 * 19 + 1)); // account 2 becomes mostly reserved
			assert_eq!(System::providers(&2), 1);
			assert_eq!(Balances::free_balance(2), 255); // "free" account would be deleted.
			assert_eq!(Balances::total_balance(&2), 256 * 20); // reserve still exists.
			assert_eq!(System::account_nonce(&2), 1);

			// account 4 tries to take index 1 for account 5.
			assert_ok!(Balances::transfer_allow_death(Some(4).into(), 5, 256 * 1 + 0x69));
			assert_eq!(Balances::total_balance(&5), 256 * 1 + 0x69);

			assert!(Balances::slash_reserved(&2, 256 * 19 + 1).1.is_zero()); // account 2 gets slashed

			// "reserve" account reduced to 255 (below ED) so account no longer consuming
			assert_ok!(System::dec_providers(&2));
			assert_eq!(System::providers(&2), 0);
			// account deleted
			assert_eq!(System::account_nonce(&2), 0); // nonce zero
			assert_eq!(Balances::total_balance(&2), 0);

			// account 4 tries to take index 1 again for account 6.
			assert_ok!(Balances::transfer_allow_death(Some(4).into(), 6, 256 * 1 + 0x69));
			assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
		});
}

#[test]
fn reward_should_work() {
	ExtBuilder::default().monied(true).build_and_execute_with(|| {
		assert_eq!(Balances::total_balance(&1), 10);
		assert_ok!(Balances::deposit_into_existing(&1, 10).map(drop));
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Deposit {
			who: 1,
			amount: 10,
		}));
		assert_eq!(Balances::total_balance(&1), 20);
		assert_eq!(Balances::total_issuance(), 120);
	});
}

#[test]
fn balance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 42);
		System::assert_has_event(RuntimeEvent::Balances(crate::Event::Deposit {
			who: 1,
			amount: 42,
		}));
		assert_eq!(Balances::free_balance(1), 42);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::free_balance(2), 0);
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::total_balance(&2), 0);
	});
}

#[test]
fn reserving_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
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
fn deducting_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_eq!(Balances::free_balance(1), 42);
	});
}

#[test]
fn refunding_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 42);
		assert_ok!(Balances::mutate_account(&1, |a| a.reserved = 69));
		Balances::unreserve(&1, 69);
		assert_eq!(Balances::free_balance(1), 111);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn slashing_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 112);
		assert_ok!(Balances::reserve(&1, 69));
		assert!(Balances::slash(&1, 42).1.is_zero());
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::total_issuance(), 70);
	});
}

#[test]
fn withdrawing_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&2, 111);
		let _ =
			Balances::withdraw(&2, 11, WithdrawReasons::TRANSFER, ExistenceRequirement::KeepAlive);
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Withdraw {
			who: 2,
			amount: 11,
		}));
		assert_eq!(Balances::free_balance(2), 100);
		assert_eq!(Balances::total_issuance(), 100);
	});
}

#[test]
fn withdrawing_balance_should_fail_when_not_expendable() {
	ExtBuilder::default().build_and_execute_with(|| {
		ExistentialDeposit::set(10);
		let _ = Balances::deposit_creating(&2, 20);
		assert_ok!(Balances::reserve(&2, 5));
		assert_noop!(
			Balances::withdraw(&2, 6, WithdrawReasons::TRANSFER, ExistenceRequirement::KeepAlive),
			Error::<Test>::Expendability,
		);
		assert_ok!(Balances::withdraw(
			&2,
			5,
			WithdrawReasons::TRANSFER,
			ExistenceRequirement::KeepAlive
		),);
	});
}

#[test]
fn slashing_incomplete_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 42);
		assert_ok!(Balances::reserve(&1, 21));
		assert_eq!(Balances::slash(&1, 69).1, 49);
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(1), 21);
		assert_eq!(Balances::total_issuance(), 22);
	});
}

#[test]
fn unreserving_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 110));
		Balances::unreserve(&1, 41);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 42);
	});
}

#[test]
fn slashing_reserved_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 112);
		assert_ok!(Balances::reserve(&1, 111));
		assert_eq!(Balances::slash_reserved(&1, 42).1, 0);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::total_issuance(), 70);
	});
}

#[test]
fn slashing_incomplete_reserved_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 42));
		assert_eq!(Balances::slash_reserved(&1, 69).1, 27);
		assert_eq!(Balances::free_balance(1), 69);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::total_issuance(), 69);
	});
}

#[test]
fn repatriating_reserved_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 110));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 41, Free), 0);
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::ReserveRepatriated {
			from: 1,
			to: 2,
			amount: 41,
			destination_status: Free,
		}));
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 42);
	});
}

#[test]
fn transferring_reserved_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 110));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 41, Reserved), 0);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(2), 41);
		assert_eq!(Balances::free_balance(2), 1);
	});
}

#[test]
fn transferring_reserved_balance_to_yourself_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 110);
		assert_ok!(Balances::reserve(&1, 50));
		assert_ok!(Balances::repatriate_reserved(&1, &1, 50, Free), 0);
		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::reserved_balance(1), 0);

		assert_ok!(Balances::reserve(&1, 50));
		assert_ok!(Balances::repatriate_reserved(&1, &1, 60, Free), 10);
		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn transferring_reserved_balance_to_nonexistent_should_fail() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 110));
		assert_noop!(
			Balances::repatriate_reserved(&1, &2, 42, Free),
			Error::<Test, _>::DeadAccount
		);
	});
}

#[test]
fn transferring_incomplete_reserved_balance_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 41));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 69, Free), 28);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(1), 69);
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 42);
	});
}

#[test]
fn transferring_too_high_value_should_not_panic() {
	ExtBuilder::default().build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, u64::MAX);
		Balances::make_free_balance_be(&2, 1);

		assert_err!(
			<Balances as Currency<_>>::transfer(&1, &2, u64::MAX, AllowDeath),
			ArithmeticError::Overflow,
		);

		assert_eq!(Balances::free_balance(1), u64::MAX);
		assert_eq!(Balances::free_balance(2), 1);
	});
}

#[test]
fn account_create_on_free_too_low_with_other() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 100);
		assert_eq!(Balances::total_issuance(), 100);

		// No-op.
		let _ = Balances::deposit_creating(&2, 50);
		assert_eq!(Balances::free_balance(2), 0);
		assert_eq!(Balances::total_issuance(), 100);
	})
}

#[test]
fn account_create_on_free_too_low() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// No-op.
		let _ = Balances::deposit_creating(&2, 50);
		assert_eq!(Balances::free_balance(2), 0);
		assert_eq!(Balances::total_issuance(), 0);
	})
}

#[test]
fn account_removal_on_free_too_low() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		assert_eq!(Balances::total_issuance(), 0);

		// Setup two accounts with free balance above the existential threshold.
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 110);

		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::free_balance(2), 110);
		assert_eq!(Balances::total_issuance(), 220);

		// Transfer funds from account 1 of such amount that after this transfer
		// the balance of account 1 will be below the existential threshold.
		// This should lead to the removal of all balance of this account.
		assert_ok!(Balances::transfer_allow_death(Some(1).into(), 2, 20));

		// Verify free balance removal of account 1.
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 130);

		// Verify that TotalIssuance tracks balance removal when free balance is too low.
		assert_eq!(Balances::total_issuance(), 130);
	});
}

#[test]
fn burn_must_work() {
	ExtBuilder::default().monied(true).build_and_execute_with(|| {
		let init_total_issuance = Balances::total_issuance();
		let imbalance = Balances::burn(10);
		assert_eq!(Balances::total_issuance(), init_total_issuance - 10);
		drop(imbalance);
		assert_eq!(Balances::total_issuance(), init_total_issuance);
	});
}

#[test]
#[should_panic = "the balance of any account should always be at least the existential deposit."]
fn cannot_set_genesis_value_below_ed() {
	EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = 11);
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let _ = crate::GenesisConfig::<Test> { balances: vec![(1, 10)] }
		.assimilate_storage(&mut t)
		.unwrap();
}

#[test]
#[should_panic = "duplicate balances in genesis."]
fn cannot_set_genesis_value_twice() {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let _ = crate::GenesisConfig::<Test> { balances: vec![(1, 10), (2, 20), (1, 15)] }
		.assimilate_storage(&mut t)
		.unwrap();
}

#[test]
fn existential_deposit_respected_when_reserving() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// Set balance to free and reserved at the existential deposit
		assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 101));
		// Check balance
		assert_eq!(Balances::free_balance(1), 101);
		assert_eq!(Balances::reserved_balance(1), 0);

		// Reserve some free balance
		assert_ok!(Balances::reserve(&1, 1));
		// Check balance, the account should be ok.
		assert_eq!(Balances::free_balance(1), 100);
		assert_eq!(Balances::reserved_balance(1), 1);

		// Cannot reserve any more of the free balance.
		assert_noop!(Balances::reserve(&1, 1), DispatchError::ConsumerRemaining);
	});
}

#[test]
fn slash_fails_when_account_needed() {
	ExtBuilder::default().existential_deposit(50).build_and_execute_with(|| {
		// Set balance to free and reserved at the existential deposit
		assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 52));
		assert_ok!(Balances::reserve(&1, 1));
		// Check balance
		assert_eq!(Balances::free_balance(1), 51);
		assert_eq!(Balances::reserved_balance(1), 1);

		// Slash a small amount
		let res = Balances::slash(&1, 1);
		assert_eq!(res, (NegativeImbalance::new(1), 0));

		// The account should be dead.
		assert_eq!(Balances::free_balance(1), 50);
		assert_eq!(Balances::reserved_balance(1), 1);

		// Slashing again doesn't work since we require the ED
		let res = Balances::slash(&1, 1);
		assert_eq!(res, (NegativeImbalance::new(0), 1));

		// The account should be dead.
		assert_eq!(Balances::free_balance(1), 50);
		assert_eq!(Balances::reserved_balance(1), 1);
	});
}

#[test]
fn account_deleted_when_just_dust() {
	ExtBuilder::default().existential_deposit(50).build_and_execute_with(|| {
		// Set balance to free and reserved at the existential deposit
		assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 50));
		// Check balance
		assert_eq!(Balances::free_balance(1), 50);

		// Slash a small amount
		let res = Balances::slash(&1, 1);
		assert_eq!(res, (NegativeImbalance::new(1), 0));

		// The account should be dead.
		assert_eq!(Balances::free_balance(1), 0);
	});
}

#[test]
fn emit_events_with_reserve_and_unreserve() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 100);

		System::set_block_number(2);
		assert_ok!(Balances::reserve(&1, 10));

		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Reserved {
			who: 1,
			amount: 10,
		}));

		System::set_block_number(3);
		assert!(Balances::unreserve(&1, 5).is_zero());

		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Unreserved {
			who: 1,
			amount: 5,
		}));

		System::set_block_number(4);
		assert_eq!(Balances::unreserve(&1, 6), 1);

		// should only unreserve 5
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Unreserved {
			who: 1,
			amount: 5,
		}));
	});
}

#[test]
fn emit_events_with_changing_locks() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 100);
		System::reset_events();

		// Locks = [] --> [10]
		Balances::set_lock(*b"LOCK_000", &1, 10, WithdrawReasons::TRANSFER);
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Locked { who: 1, amount: 10 })]);

		// Locks = [10] --> [15]
		Balances::set_lock(*b"LOCK_000", &1, 15, WithdrawReasons::TRANSFER);
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Locked { who: 1, amount: 5 })]);

		// Locks = [15] --> [15, 20]
		Balances::set_lock(*b"LOCK_001", &1, 20, WithdrawReasons::TRANSACTION_PAYMENT);
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Locked { who: 1, amount: 5 })]);

		// Locks = [15, 20] --> [17, 20]
		Balances::set_lock(*b"LOCK_000", &1, 17, WithdrawReasons::TRANSACTION_PAYMENT);
		for event in events() {
			match event {
				RuntimeEvent::Balances(crate::Event::Locked { .. }) => {
					assert!(false, "unexpected lock event")
				},
				RuntimeEvent::Balances(crate::Event::Unlocked { .. }) => {
					assert!(false, "unexpected unlock event")
				},
				_ => continue,
			}
		}

		// Locks = [17, 20] --> [17, 15]
		Balances::set_lock(*b"LOCK_001", &1, 15, WithdrawReasons::TRANSFER);
		assert_eq!(
			events(),
			[RuntimeEvent::Balances(crate::Event::Unlocked { who: 1, amount: 3 })]
		);

		// Locks = [17, 15] --> [15]
		Balances::remove_lock(*b"LOCK_000", &1);
		assert_eq!(
			events(),
			[RuntimeEvent::Balances(crate::Event::Unlocked { who: 1, amount: 2 })]
		);

		// Locks = [15] --> []
		Balances::remove_lock(*b"LOCK_001", &1);
		assert_eq!(
			events(),
			[RuntimeEvent::Balances(crate::Event::Unlocked { who: 1, amount: 15 })]
		);
	});
}

#[test]
fn emit_events_with_existential_deposit() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 100));

		assert_eq!(
			events(),
			[
				RuntimeEvent::System(system::Event::NewAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::Endowed { account: 1, free_balance: 100 }),
				RuntimeEvent::Balances(crate::Event::BalanceSet { who: 1, free: 100 }),
			]
		);

		let res = Balances::slash(&1, 1);
		assert_eq!(res, (NegativeImbalance::new(1), 0));

		assert_eq!(
			events(),
			[
				RuntimeEvent::System(system::Event::KilledAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::DustLost { account: 1, amount: 99 }),
				RuntimeEvent::Balances(crate::Event::Slashed { who: 1, amount: 1 }),
			]
		);
	});
}

#[test]
fn emit_events_with_no_existential_deposit_suicide() {
	ExtBuilder::default().existential_deposit(1).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 100);

		assert_eq!(
			events(),
			[
				RuntimeEvent::Balances(crate::Event::BalanceSet { who: 1, free: 100 }),
				RuntimeEvent::System(system::Event::NewAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::Endowed { account: 1, free_balance: 100 }),
			]
		);

		let res = Balances::slash(&1, 100);
		assert_eq!(res, (NegativeImbalance::new(100), 0));

		assert_eq!(
			events(),
			[
				RuntimeEvent::System(system::Event::KilledAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::Slashed { who: 1, amount: 100 }),
			]
		);
	});
}

#[test]
fn slash_over_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// SCENARIO: Over-slash will kill account, and report missing slash amount.
		Balances::make_free_balance_be(&1, 1_000);
		// Slashed full free_balance, and reports 300 not slashed
		assert_eq!(Balances::slash(&1, 1_300), (NegativeImbalance::new(1000), 300));
		// Account is dead
		assert!(!System::account_exists(&1));
	});
}

#[test]
fn slash_full_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		// Slashed completed in full
		assert_eq!(Balances::slash(&1, 1_000), (NegativeImbalance::new(1000), 0));
		// Account is still alive
		assert!(!System::account_exists(&1));
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Slashed {
			who: 1,
			amount: 1000,
		}));
	});
}

#[test]
fn slash_partial_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		// Slashed completed in full
		assert_eq!(Balances::slash(&1, 900), (NegativeImbalance::new(900), 0));
		// Account is still alive
		assert!(System::account_exists(&1));
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Slashed {
			who: 1,
			amount: 900,
		}));
	});
}

#[test]
fn slash_dusting_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		// Slashed completed in full
		assert_eq!(Balances::slash(&1, 950), (NegativeImbalance::new(950), 0));
		assert!(!System::account_exists(&1));
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Slashed {
			who: 1,
			amount: 950,
		}));
	});
}

#[test]
fn slash_does_not_take_from_reserve() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(Balances::reserve(&1, 100));
		// Slashed completed in full
		assert_eq!(Balances::slash(&1, 900), (NegativeImbalance::new(800), 100));
		assert_eq!(Balances::reserved_balance(&1), 100);
		System::assert_last_event(RuntimeEvent::Balances(crate::Event::Slashed {
			who: 1,
			amount: 800,
		}));
	});
}

#[test]
fn slash_consumed_slash_full_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(System::inc_consumers(&1)); // <-- Reference counter added here is enough for all tests
									   // Slashed completed in full
		assert_eq!(Balances::slash(&1, 900), (NegativeImbalance::new(900), 0));
		// Account is still alive
		assert!(System::account_exists(&1));
	});
}

#[test]
fn slash_consumed_slash_over_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(System::inc_consumers(&1)); // <-- Reference counter added here is enough for all tests
									   // Slashed completed in full
		assert_eq!(Balances::slash(&1, 1_000), (NegativeImbalance::new(900), 100));
		// Account is still alive
		assert!(System::account_exists(&1));
	});
}

#[test]
fn slash_consumed_slash_partial_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(System::inc_consumers(&1)); // <-- Reference counter added here is enough for all tests
									   // Slashed completed in full
		assert_eq!(Balances::slash(&1, 800), (NegativeImbalance::new(800), 0));
		// Account is still alive
		assert!(System::account_exists(&1));
	});
}

#[test]
fn slash_on_non_existant_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// Slash on non-existent account is okay.
		assert_eq!(Balances::slash(&12345, 1_300), (NegativeImbalance::new(0), 1300));
	});
}

#[test]
fn slash_reserved_slash_partial_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(Balances::reserve(&1, 900));
		// Slashed completed in full
		assert_eq!(Balances::slash_reserved(&1, 800), (NegativeImbalance::new(800), 0));
		assert_eq!(System::consumers(&1), 1);
		assert_eq!(Balances::reserved_balance(&1), 100);
		assert_eq!(Balances::free_balance(&1), 100);
	});
}

#[test]
fn slash_reserved_slash_everything_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(Balances::reserve(&1, 900));
		assert_eq!(System::consumers(&1), 1);
		// Slashed completed in full
		assert_eq!(Balances::slash_reserved(&1, 900), (NegativeImbalance::new(900), 0));
		assert_eq!(System::consumers(&1), 0);
		// Account is still alive
		assert!(System::account_exists(&1));
	});
}

#[test]
fn slash_reserved_overslash_does_not_touch_free_balance() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// SCENARIO: Over-slash doesn't touch free balance.
		Balances::make_free_balance_be(&1, 1_000);
		assert_ok!(Balances::reserve(&1, 800));
		// Slashed done
		assert_eq!(Balances::slash_reserved(&1, 900), (NegativeImbalance::new(800), 100));
		assert_eq!(Balances::free_balance(&1), 200);
	});
}

#[test]
fn slash_reserved_on_non_existant_works() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		// Slash on non-existent account is okay.
		assert_eq!(Balances::slash_reserved(&12345, 1_300), (NegativeImbalance::new(0), 1300));
	});
}

#[test]
fn operations_on_dead_account_should_not_change_state() {
	// These functions all use `mutate_account` which may introduce a storage change when
	// the account never existed to begin with, and shouldn't exist in the end.
	ExtBuilder::default().existential_deposit(1).build_and_execute_with(|| {
		assert!(!frame_system::Account::<Test>::contains_key(&1337));

		// Unreserve
		assert_storage_noop!(assert_eq!(Balances::unreserve(&1337, 42), 42));
		// Reserve
		assert_noop!(Balances::reserve(&1337, 42), Error::<Test, _>::InsufficientBalance);
		// Slash Reserve
		assert_storage_noop!(assert_eq!(Balances::slash_reserved(&1337, 42).1, 42));
		// Repatriate Reserve
		assert_noop!(
			Balances::repatriate_reserved(&1337, &1338, 42, Free),
			Error::<Test, _>::DeadAccount
		);
		// Slash
		assert_storage_noop!(assert_eq!(Balances::slash(&1337, 42).1, 42));
	});
}

#[test]
#[should_panic = "The existential deposit must be greater than zero!"]
fn zero_ed_is_prohibited() {
	// These functions all use `mutate_account` which may introduce a storage change when
	// the account never existed to begin with, and shouldn't exist in the end.
	ExtBuilder::default().existential_deposit(0).build_and_execute_with(|| {
		Balances::integrity_test();
	});
}

#[test]
fn named_reserve_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);

		let id_1 = TestId::Foo;
		let id_2 = TestId::Bar;
		let id_3 = TestId::Baz;

		// reserve

		assert_noop!(
			Balances::reserve_named(&id_1, &1, 112),
			Error::<Test, _>::InsufficientBalance
		);

		assert_ok!(Balances::reserve_named(&id_1, &1, 12));

		assert_eq!(Balances::reserved_balance(1), 12);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 12);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 0);

		assert_ok!(Balances::reserve_named(&id_1, &1, 2));

		assert_eq!(Balances::reserved_balance(1), 14);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 14);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 0);

		assert_ok!(Balances::reserve_named(&id_2, &1, 23));

		assert_eq!(Balances::reserved_balance(1), 37);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 14);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 23);

		assert_ok!(Balances::reserve(&1, 34));

		assert_eq!(Balances::reserved_balance(1), 71);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 14);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 23);

		assert_eq!(Balances::total_balance(&1), 111);
		assert_eq!(Balances::free_balance(1), 40);

		assert_noop!(Balances::reserve_named(&id_3, &1, 2), Error::<Test, _>::TooManyReserves);

		// unreserve

		assert_eq!(Balances::unreserve_named(&id_1, &1, 10), 0);

		assert_eq!(Balances::reserved_balance(1), 61);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 4);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 23);

		assert_eq!(Balances::unreserve_named(&id_1, &1, 5), 1);

		assert_eq!(Balances::reserved_balance(1), 57);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 0);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 23);

		assert_eq!(Balances::unreserve_named(&id_2, &1, 3), 0);

		assert_eq!(Balances::reserved_balance(1), 54);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 0);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 20);

		assert_eq!(Balances::total_balance(&1), 111);
		assert_eq!(Balances::free_balance(1), 57);

		// slash_reserved_named

		assert_ok!(Balances::reserve_named(&id_1, &1, 10));

		assert_eq!(Balances::slash_reserved_named(&id_1, &1, 25).1, 15);

		assert_eq!(Balances::reserved_balance(1), 54);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 0);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 20);
		assert_eq!(Balances::total_balance(&1), 101);

		assert_eq!(Balances::slash_reserved_named(&id_2, &1, 5).1, 0);

		assert_eq!(Balances::reserved_balance(1), 49);
		assert_eq!(Balances::reserved_balance_named(&id_1, &1), 0);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 15);
		assert_eq!(Balances::total_balance(&1), 96);

		// repatriate_reserved_named

		let _ = Balances::deposit_creating(&2, 100);

		assert_eq!(Balances::repatriate_reserved_named(&id_2, &1, &2, 10, Reserved).unwrap(), 0);

		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 5);
		assert_eq!(Balances::reserved_balance_named(&id_2, &2), 10);
		assert_eq!(Balances::reserved_balance(&2), 10);

		assert_eq!(Balances::repatriate_reserved_named(&id_2, &2, &1, 11, Reserved).unwrap(), 1);

		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 15);
		assert_eq!(Balances::reserved_balance_named(&id_2, &2), 0);
		assert_eq!(Balances::reserved_balance(&2), 0);

		assert_eq!(Balances::repatriate_reserved_named(&id_2, &1, &2, 10, Free).unwrap(), 0);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 5);
		assert_eq!(Balances::reserved_balance_named(&id_2, &2), 0);
		assert_eq!(Balances::free_balance(&2), 110);

		// repatriate_reserved_named to self

		assert_eq!(Balances::repatriate_reserved_named(&id_2, &1, &1, 10, Reserved).unwrap(), 5);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 5);

		assert_eq!(Balances::free_balance(&1), 47);

		assert_eq!(Balances::repatriate_reserved_named(&id_2, &1, &1, 15, Free).unwrap(), 10);
		assert_eq!(Balances::reserved_balance_named(&id_2, &1), 0);

		assert_eq!(Balances::free_balance(&1), 52);
	});
}

#[test]
fn reserve_must_succeed_if_can_reserve_does() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 1);
		let _ = Balances::deposit_creating(&2, 2);
		assert!(Balances::can_reserve(&1, 1) == Balances::reserve(&1, 1).is_ok());
		assert!(Balances::can_reserve(&2, 1) == Balances::reserve(&2, 1).is_ok());
	});
}

#[test]
fn reserved_named_to_yourself_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 110);

		let id = TestId::Foo;

		assert_ok!(Balances::reserve_named(&id, &1, 50));
		assert_ok!(Balances::repatriate_reserved_named(&id, &1, &1, 50, Free), 0);
		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::reserved_balance_named(&id, &1), 0);

		assert_ok!(Balances::reserve_named(&id, &1, 50));
		assert_ok!(Balances::repatriate_reserved_named(&id, &1, &1, 60, Free), 10);
		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::reserved_balance_named(&id, &1), 0);
	});
}

#[test]
fn ensure_reserved_named_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);

		let id = TestId::Foo;

		assert_ok!(Balances::ensure_reserved_named(&id, &1, 15));
		assert_eq!(Balances::reserved_balance_named(&id, &1), 15);

		assert_ok!(Balances::ensure_reserved_named(&id, &1, 10));
		assert_eq!(Balances::reserved_balance_named(&id, &1), 10);

		assert_ok!(Balances::ensure_reserved_named(&id, &1, 20));
		assert_eq!(Balances::reserved_balance_named(&id, &1), 20);
	});
}

#[test]
fn unreserve_all_named_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);

		let id = TestId::Foo;

		assert_ok!(Balances::reserve_named(&id, &1, 15));

		assert_eq!(Balances::unreserve_all_named(&id, &1), 15);
		assert_eq!(Balances::reserved_balance_named(&id, &1), 0);
		assert_eq!(Balances::free_balance(&1), 111);

		assert_eq!(Balances::unreserve_all_named(&id, &1), 0);
	});
}

#[test]
fn slash_all_reserved_named_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);

		let id = TestId::Foo;

		assert_ok!(Balances::reserve_named(&id, &1, 15));

		assert_eq!(Balances::slash_all_reserved_named(&id, &1).peek(), 15);
		assert_eq!(Balances::reserved_balance_named(&id, &1), 0);
		assert_eq!(Balances::free_balance(&1), 96);

		assert_eq!(Balances::slash_all_reserved_named(&id, &1).peek(), 0);
	});
}

#[test]
fn repatriate_all_reserved_named_should_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		let _ = Balances::deposit_creating(&2, 10);
		let _ = Balances::deposit_creating(&3, 10);

		let id = TestId::Foo;

		assert_ok!(Balances::reserve_named(&id, &1, 15));

		assert_ok!(Balances::repatriate_all_reserved_named(&id, &1, &2, Reserved));
		assert_eq!(Balances::reserved_balance_named(&id, &1), 0);
		assert_eq!(Balances::reserved_balance_named(&id, &2), 15);

		assert_ok!(Balances::repatriate_all_reserved_named(&id, &2, &3, Free));
		assert_eq!(Balances::reserved_balance_named(&id, &2), 0);
		assert_eq!(Balances::free_balance(&3), 25);
	});
}

#[test]
fn freezing_and_locking_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(<Balances as fungible::MutateFreeze<_>>::set_freeze(&TestId::Foo, &1, 4));
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			assert_eq!(System::consumers(&1), 2);
			assert_eq!(Balances::account(&1).frozen, 5);
			assert_ok!(<Balances as fungible::MutateFreeze<_>>::set_freeze(&TestId::Foo, &1, 6));
			assert_eq!(Balances::account(&1).frozen, 6);
			assert_ok!(<Balances as fungible::MutateFreeze<_>>::set_freeze(&TestId::Foo, &1, 4));
			assert_eq!(Balances::account(&1).frozen, 5);
			Balances::set_lock(ID_1, &1, 3, WithdrawReasons::all());
			assert_eq!(Balances::account(&1).frozen, 4);
			Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
			assert_eq!(Balances::account(&1).frozen, 5);
			Balances::remove_lock(ID_1, &1);
			assert_eq!(Balances::account(&1).frozen, 4);
			assert_eq!(System::consumers(&1), 1);
		});
}
