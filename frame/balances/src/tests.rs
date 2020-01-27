// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the module.

use super::*;
use mock::{Balances, ExtBuilder, Test, System, info_from_weight, CALL};
use sp_runtime::{Fixed64, traits::{SignedExtension, BadOrigin}};
use frame_support::{
	assert_noop, assert_ok, assert_err,
	traits::{LockableCurrency, LockIdentifier, WithdrawReason, WithdrawReasons,
	Currency, ReservableCurrency, ExistenceRequirement::AllowDeath}
};
use pallet_transaction_payment::ChargeTransactionPayment;
use frame_system::RawOrigin;

const ID_1: LockIdentifier = *b"1       ";
const ID_2: LockIdentifier = *b"2       ";

#[test]
fn basic_locking_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		assert_eq!(Balances::free_balance(1), 10);
		Balances::set_lock(ID_1, &1, 9, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 5, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
	});
}

#[test]
fn partial_locking_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
	});
}

#[test]
fn lock_removal_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::all());
		Balances::remove_lock(ID_1, &1);
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
	});
}

#[test]
fn lock_replacement_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::all());
		Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
	});
}

#[test]
fn double_locking_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
		Balances::set_lock(ID_2, &1, 5, WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
	});
}

#[test]
fn combination_locking_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, u64::max_value(), WithdrawReasons::none());
		Balances::set_lock(ID_2, &1, 0, WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
	});
}

#[test]
fn lock_value_extension_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, 5, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		Balances::extend_lock(ID_1, &1, 2, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		Balances::extend_lock(ID_1, &1, 8, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
	});
}

#[test]
fn lock_reasons_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build()
		.execute_with(|| {
			pallet_transaction_payment::NextFeeMultiplier::put(Fixed64::from_natural(1));
			Balances::set_lock(ID_1, &1, 10, WithdrawReason::Reserve.into());
			assert_noop!(
				<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath),
				Error::<Test, _>::LiquidityRestrictions
			);
			assert_noop!(
				<Balances as ReservableCurrency<_>>::reserve(&1, 1),
				Error::<Test, _>::LiquidityRestrictions
			);
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(1),
				&1,
				CALL,
				info_from_weight(1),
				1,
			).is_err());
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(0),
				&1,
				CALL,
				info_from_weight(1),
				1,
			).is_ok());

			Balances::set_lock(ID_1, &1, 10, WithdrawReason::TransactionPayment.into());
			assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1, AllowDeath));
			assert_ok!(<Balances as ReservableCurrency<_>>::reserve(&1, 1));
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(1),
				&1,
				CALL,
				info_from_weight(1),
				1,
			).is_err());
			assert!(<ChargeTransactionPayment<Test> as SignedExtension>::pre_dispatch(
				ChargeTransactionPayment::from(0),
				&1,
				CALL,
				info_from_weight(1),
				1,
			).is_err());
		});
}

#[test]
fn lock_block_number_extension_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, 10, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		System::set_block_number(2);
		Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::all());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 3, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
	});
}

#[test]
fn lock_reasons_extension_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build().execute_with(|| {
		Balances::set_lock(ID_1, &1, 10, WithdrawReason::Transfer.into());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		Balances::extend_lock(ID_1, &1, 10, WithdrawReasons::none());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
		Balances::extend_lock(ID_1, &1, 10, WithdrawReason::Reserve.into());
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 6, AllowDeath),
			Error::<Test, _>::LiquidityRestrictions
		);
	});
}

#[test]
fn default_indexing_on_new_accounts_should_not_work2() {
	ExtBuilder::default()
		.existential_deposit(10)
		.creation_fee(50)
		.monied(true)
		.build()
		.execute_with(|| {
			assert_eq!(Balances::is_dead_account(&5), true); // account 5 should not exist
			// ext_deposit is 10, value is 9, not satisfies for ext_deposit
			assert_noop!(
				Balances::transfer(Some(1).into(), 5, 9),
				Error::<Test, _>::ExistentialDeposit,
			);
			assert_eq!(Balances::is_dead_account(&5), true); // account 5 should not exist
			assert_eq!(Balances::free_balance(1), 100);
		});
}

#[test]
fn reserved_balance_should_prevent_reclaim_count() {
	ExtBuilder::default()
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
			assert_eq!(System::account_nonce(&2), 0);	// nonce zero
			assert_eq!(Balances::is_dead_account(&2), true);

			// account 4 tries to take index 1 again for account 6.
			assert_ok!(Balances::transfer(Some(4).into(), 6, 256 * 1 + 0x69));
			assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
			assert_eq!(Balances::is_dead_account(&6), false);
		});
}


#[test]
fn reward_should_work() {
	ExtBuilder::default().monied(true).build().execute_with(|| {
		assert_eq!(Balances::total_balance(&1), 10);
		assert_ok!(Balances::deposit_into_existing(&1, 10).map(drop));
		assert_eq!(Balances::total_balance(&1), 20);
		assert_eq!(<TotalIssuance<Test>>::get(), 120);
	});
}

#[test]
fn dust_account_removal_should_work() {
	ExtBuilder::default()
		.existential_deposit(100)
		.monied(true)
		.build()
		.execute_with(|| {
			System::inc_account_nonce(&2);
			assert_eq!(System::account_nonce(&2), 1);
			assert_eq!(Balances::total_balance(&2), 2000);

			assert_ok!(Balances::transfer(Some(2).into(), 5, 1901)); // index 1 (account 2) becomes zombie
			assert_eq!(Balances::total_balance(&2), 0);
			assert_eq!(Balances::total_balance(&5), 1901);
			assert_eq!(System::account_nonce(&2), 0);
		});
}

#[test]
fn dust_account_removal_should_work2() {
	ExtBuilder::default()
		.existential_deposit(100)
		.creation_fee(50)
		.monied(true)
		.build()
		.execute_with(|| {
			System::inc_account_nonce(&2);
			assert_eq!(System::account_nonce(&2), 1);
			assert_eq!(Balances::total_balance(&2), 2000);
			// index 1 (account 2) becomes zombie for 256*10 + 50(fee) < 256 * 10 (ext_deposit)
			assert_ok!(Balances::transfer(Some(2).into(), 5, 1851));
			assert_eq!(Balances::total_balance(&2), 0);
			assert_eq!(Balances::total_balance(&5), 1851);
			assert_eq!(System::account_nonce(&2), 0);
		});
}

#[test]
fn balance_works() {
	ExtBuilder::default().build().execute_with(|| {
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
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::transfer(Some(1).into(), 2, 69));
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::total_balance(&2), 69);
	});
}

#[test]
fn force_transfer_works() {
	ExtBuilder::default().build().execute_with(|| {
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
	ExtBuilder::default().build().execute_with(|| {
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
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_noop!(
			Balances::transfer(Some(1).into(), 2, 69),
			Error::<Test, _>::InsufficientBalance,
		);
	});
}

#[test]
fn deducting_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_eq!(Balances::free_balance(1), 42);
	});
}

#[test]
fn refunding_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 42);
		let account = Balances::account(&1);
		Balances::set_account(&1, &AccountData { reserved: 69, ..account }, &account);
		Balances::unreserve(&1, 69);
		assert_eq!(Balances::free_balance(1), 111);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn slashing_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert!(Balances::slash(&1, 69).1.is_zero());
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::reserved_balance(1), 42);
		assert_eq!(<TotalIssuance<Test>>::get(), 42);
	});
}

#[test]
fn slashing_incomplete_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 42);
		assert_ok!(Balances::reserve(&1, 21));
		assert_eq!(Balances::slash(&1, 69).1, 27);
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(<TotalIssuance<Test>>::get(), 0);
	});
}

#[test]
fn unreserving_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		Balances::unreserve(&1, 42);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 42);
	});
}

#[test]
fn slashing_reserved_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		assert_eq!(Balances::slash_reserved(&1, 42).1, 0);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(<TotalIssuance<Test>>::get(), 69);
	});
}

#[test]
fn slashing_incomplete_reserved_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 42));
		assert_eq!(Balances::slash_reserved(&1, 69).1, 27);
		assert_eq!(Balances::free_balance(1), 69);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(<TotalIssuance<Test>>::get(), 69);
	});
}

#[test]
fn transferring_reserved_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 110));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 41), 0);
		assert_eq!(Balances::reserved_balance(1), 69);
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 42);
	});
}

#[test]
fn transferring_reserved_balance_to_nonexistent_should_fail() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		assert_noop!(Balances::repatriate_reserved(&1, &2, 42), Error::<Test, _>::DeadAccount);
	});
}

#[test]
fn transferring_incomplete_reserved_balance_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 41));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 69), 28);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(1), 69);
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 42);
	});
}

#[test]
fn transferring_too_high_value_should_not_panic() {
	ExtBuilder::default().build().execute_with(|| {
		Account::<Test>::insert(1, AccountData { free: u64::max_value(), .. Default::default() });
		Account::<Test>::insert(2, AccountData { free: 1, .. Default::default() });

		assert_err!(
			Balances::transfer(Some(1).into(), 2, u64::max_value()),
			Error::<Test, _>::Overflow,
		);

		assert_eq!(Balances::free_balance(1), u64::max_value());
		assert_eq!(Balances::free_balance(2), 1);
	});
}

#[test]
fn account_create_on_free_too_low_with_other() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 100);
		assert_eq!(<TotalIssuance<Test>>::get(), 100);

		// No-op.
		let _ = Balances::deposit_creating(&2, 50);
		assert_eq!(Balances::free_balance(2), 0);
		assert_eq!(<TotalIssuance<Test>>::get(), 100);
	})
}


#[test]
fn account_create_on_free_too_low() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// No-op.
		let _ = Balances::deposit_creating(&2, 50);
		assert_eq!(Balances::free_balance(2), 0);
		assert_eq!(<TotalIssuance<Test>>::get(), 0);
	})
}

#[test]
fn account_removal_on_free_too_low() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		assert_eq!(<TotalIssuance<Test>>::get(), 0);

		// Setup two accounts with free balance above the existential threshold.
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 110);

		assert_eq!(Balances::free_balance(1), 110);
		assert_eq!(Balances::free_balance(2), 110);
		assert_eq!(<TotalIssuance<Test>>::get(), 220);

		// Transfer funds from account 1 of such amount that after this transfer
		// the balance of account 1 will be below the existential threshold.
		// This should lead to the removal of all balance of this account.
		assert_ok!(Balances::transfer(Some(1).into(), 2, 20));

		// Verify free balance removal of account 1.
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 130);

		// Verify that TotalIssuance tracks balance removal when free balance is too low.
		assert_eq!(<TotalIssuance<Test>>::get(), 130);
	});
}

#[test]
fn transfer_overflow_isnt_exploitable() {
	ExtBuilder::default().creation_fee(50).build().execute_with(|| {
		// Craft a value that will overflow if summed with `creation_fee`.
		let evil_value = u64::max_value() - 49;

		assert_err!(
			Balances::transfer(Some(1).into(), 5, evil_value),
			Error::<Test, _>::Overflow,
		);
	});
}

#[test]
fn burn_must_work() {
	ExtBuilder::default().monied(true).build().execute_with(|| {
		let init_total_issuance = Balances::total_issuance();
		let imbalance = Balances::burn(10);
		assert_eq!(Balances::total_issuance(), init_total_issuance - 10);
		drop(imbalance);
		assert_eq!(Balances::total_issuance(), init_total_issuance);
	});
}

#[test]
fn transfer_keep_alive_works() {
	ExtBuilder::default().existential_deposit(1).build().execute_with(|| {
		let _ = Balances::deposit_creating(&1, 100);
		assert_err!(
			Balances::transfer_keep_alive(Some(1).into(), 2, 100),
			Error::<Test, _>::KeepAlive
		);
		assert_eq!(Balances::is_dead_account(&1), false);
		assert_eq!(Balances::total_balance(&1), 100);
		assert_eq!(Balances::total_balance(&2), 0);
	});
}

#[test]
#[should_panic="the balance of any account should always be more than existential deposit."]
fn cannot_set_genesis_value_below_ed() {
	mock::EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = 11);
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let _ = GenesisConfig::<Test> {
		balances: vec![(1, 10)],
	}.assimilate_storage(&mut t).unwrap();
}

#[test]
fn dust_moves_between_free_and_reserved() {
	ExtBuilder::default()
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
	ExtBuilder::default()
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
