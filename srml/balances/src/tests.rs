// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use super::*;
use mock::{Balances, ExtBuilder, Runtime, System};
use runtime_io::with_externalities;
use srml_support::{
	assert_noop, assert_ok, assert_err,
	traits::{LockableCurrency, LockIdentifier, WithdrawReason, WithdrawReasons,
	Currency, MakePayment, ReservableCurrency}
};

const ID_1: LockIdentifier = *b"1       ";
const ID_2: LockIdentifier = *b"2       ";
const ID_3: LockIdentifier = *b"3       ";

#[test]
fn basic_locking_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		assert_eq!(Balances::free_balance(&1), 10);
		Balances::set_lock(ID_1, &1, 9, u64::max_value(), WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 5), "account liquidity restrictions prevent withdrawal");
	});
}

#[test]
fn partial_locking_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 5, u64::max_value(), WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn lock_removal_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, u64::max_value(), u64::max_value(), WithdrawReasons::all());
		Balances::remove_lock(ID_1, &1);
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn lock_replacement_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, u64::max_value(), u64::max_value(), WithdrawReasons::all());
		Balances::set_lock(ID_1, &1, 5, u64::max_value(), WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn double_locking_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 5, u64::max_value(), WithdrawReasons::all());
		Balances::set_lock(ID_2, &1, 5, u64::max_value(), WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn combination_locking_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, u64::max_value(), 0, WithdrawReasons::none());
		Balances::set_lock(ID_2, &1, 0, u64::max_value(), WithdrawReasons::none());
		Balances::set_lock(ID_3, &1, 0, 0, WithdrawReasons::all());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn lock_value_extension_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 5, u64::max_value(), WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		Balances::extend_lock(ID_1, &1, 2, u64::max_value(), WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		Balances::extend_lock(ID_1, &1, 8, u64::max_value(), WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 3), "account liquidity restrictions prevent withdrawal");
	});
}

#[test]
fn lock_reasons_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).transaction_fees(0, 1).build(), || {
		Balances::set_lock(ID_1, &1, 10, u64::max_value(), WithdrawReason::Transfer.into());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 1), "account liquidity restrictions prevent withdrawal");
		assert_ok!(<Balances as ReservableCurrency<_>>::reserve(&1, 1));
		assert_ok!(<Balances as MakePayment<_>>::make_payment(&1, 1));

		Balances::set_lock(ID_1, &1, 10, u64::max_value(), WithdrawReason::Reserve.into());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
		assert_noop!(<Balances as ReservableCurrency<_>>::reserve(&1, 1), "account liquidity restrictions prevent withdrawal");
		assert_ok!(<Balances as MakePayment<_>>::make_payment(&1, 1));

		Balances::set_lock(ID_1, &1, 10, u64::max_value(), WithdrawReason::TransactionPayment.into());
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
		assert_ok!(<Balances as ReservableCurrency<_>>::reserve(&1, 1));
		assert_noop!(<Balances as MakePayment<_>>::make_payment(&1, 1), "account liquidity restrictions prevent withdrawal");
	});
}

#[test]
fn lock_block_number_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 10, 2, WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 1), "account liquidity restrictions prevent withdrawal");

		System::set_block_number(2);
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 1));
	});
}

#[test]
fn lock_block_number_extension_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 10, 2, WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		Balances::extend_lock(ID_1, &1, 10, 1, WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		System::set_block_number(2);
		Balances::extend_lock(ID_1, &1, 10, 8, WithdrawReasons::all());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 3), "account liquidity restrictions prevent withdrawal");
	});
}

#[test]
fn lock_reasons_extension_should_work() {
	with_externalities(&mut ExtBuilder::default().existential_deposit(1).monied(true).build(), || {
		Balances::set_lock(ID_1, &1, 10, 10, WithdrawReason::Transfer.into());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		Balances::extend_lock(ID_1, &1, 10, 10, WithdrawReasons::none());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
		Balances::extend_lock(ID_1, &1, 10, 10, WithdrawReason::Reserve.into());
		assert_noop!(<Balances as Currency<_>>::transfer(&1, &2, 6), "account liquidity restrictions prevent withdrawal");
	});
}

#[test]
fn default_indexing_on_new_accounts_should_not_work2() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(10)
			.creation_fee(50)
			.monied(true)
			.build(),
		|| {
			assert_eq!(Balances::is_dead_account(&5), true); // account 5 should not exist
			// account 1 has 256 * 10 = 2560, account 5 is not exist, ext_deposit is 10, value is 9, not satisfies for ext_deposit
			assert_noop!(
				Balances::transfer(Some(1).into(), 5, 9),
				"value too low to create account"
			);
			assert_eq!(Balances::is_dead_account(&5), true); // account 5 should not exist
			assert_eq!(Balances::free_balance(&1), 100);
		},
	);
}

#[test]
fn reserved_balance_should_prevent_reclaim_count() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(256 * 1)
			.monied(true)
			.build(),
		|| {
			System::inc_account_nonce(&2);
			assert_eq!(Balances::is_dead_account(&2), false);
			assert_eq!(Balances::is_dead_account(&5), true);
			assert_eq!(Balances::total_balance(&2), 256 * 20);

			assert_ok!(Balances::reserve(&2, 256 * 19 + 1)); // account 2 becomes mostly reserved
			assert_eq!(Balances::free_balance(&2), 0); // "free" account deleted."
			assert_eq!(Balances::total_balance(&2), 256 * 19 + 1); // reserve still exists.
			assert_eq!(Balances::is_dead_account(&2), false);
			assert_eq!(System::account_nonce(&2), 1);

			assert_ok!(Balances::transfer(Some(4).into(), 5, 256 * 1 + 0x69)); // account 4 tries to take index 1 for account 5.
			assert_eq!(Balances::total_balance(&5), 256 * 1 + 0x69);
			assert_eq!(Balances::is_dead_account(&5), false);

			assert!(Balances::slash(&2, 256 * 18 + 2).1.is_zero()); // account 2 gets slashed
			assert_eq!(Balances::total_balance(&2), 0); // "reserve" account reduced to 255 (below ED) so account deleted
			assert_eq!(System::account_nonce(&2), 0);	// nonce zero
			assert_eq!(Balances::is_dead_account(&2), true);

			assert_ok!(Balances::transfer(Some(4).into(), 6, 256 * 1 + 0x69)); // account 4 tries to take index 1 again for account 6.
			assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
			assert_eq!(Balances::is_dead_account(&6), false);
		},
	);
}


#[test]
fn reward_should_work() {
	with_externalities(&mut ExtBuilder::default().monied(true).build(), || {
		assert_eq!(Balances::total_balance(&1), 10);
		assert_ok!(Balances::deposit_into_existing(&1, 10).map(drop));
		assert_eq!(Balances::total_balance(&1), 20);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 110);
	});
}

#[test]
fn dust_account_removal_should_work() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(100)
			.monied(true)
			.build(),
		|| {
			System::inc_account_nonce(&2);
			assert_eq!(System::account_nonce(&2), 1);
			assert_eq!(Balances::total_balance(&2), 2000);

			assert_ok!(Balances::transfer(Some(2).into(), 5, 1901)); // index 1 (account 2) becomes zombie
			assert_eq!(Balances::total_balance(&2), 0);
			assert_eq!(Balances::total_balance(&5), 1901);
			assert_eq!(System::account_nonce(&2), 0);
		},
	);
}

#[test]
fn dust_account_removal_should_work2() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(100)
			.creation_fee(50)
			.monied(true)
			.build(),
		|| {
			System::inc_account_nonce(&2);
			assert_eq!(System::account_nonce(&2), 1);
			assert_eq!(Balances::total_balance(&2), 2000);
			assert_ok!(Balances::transfer(Some(2).into(), 5, 1851)); // index 1 (account 2) becomes zombie for 256*10 + 50(fee) < 256 * 10 (ext_deposit)
			assert_eq!(Balances::total_balance(&2), 0);
			assert_eq!(Balances::total_balance(&5), 1851);
			assert_eq!(System::account_nonce(&2), 0);
		},
	);
}

#[test]
fn balance_works() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 42);
		assert_eq!(Balances::free_balance(&1), 42);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::free_balance(&2), 0);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::total_balance(&2), 0);
	});
}

#[test]
fn balance_transfer_works() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::transfer(Some(1).into(), 2, 69));
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::total_balance(&2), 69);
	});
}

#[test]
fn reserving_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);

		assert_eq!(Balances::total_balance(&1), 111);
		assert_eq!(Balances::free_balance(&1), 111);
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert_ok!(Balances::reserve(&1, 69));

		assert_eq!(Balances::total_balance(&1), 111);
		assert_eq!(Balances::free_balance(&1), 42);
		assert_eq!(Balances::reserved_balance(&1), 69);
	});
}

#[test]
fn balance_transfer_when_reserved_should_not_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_noop!(Balances::transfer(Some(1).into(), 2, 69), "balance too low to send value");
	});
}

#[test]
fn deducting_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_eq!(Balances::free_balance(&1), 42);
	});
}

#[test]
fn refunding_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 42);
		Balances::set_reserved_balance(&1, 69);
		Balances::unreserve(&1, 69);
		assert_eq!(Balances::free_balance(&1), 111);
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn slashing_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert!(Balances::slash(&1, 69).1.is_zero());
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&1), 42);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 42);
	});
}

#[test]
fn slashing_incomplete_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 42);
		assert_ok!(Balances::reserve(&1, 21));
		assert_eq!(Balances::slash(&1, 69).1, 27);
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 0);
	});
}

#[test]
fn unreserving_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		Balances::unreserve(&1, 42);
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 42);
	});
}

#[test]
fn slashing_reserved_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		assert_eq!(Balances::slash_reserved(&1, 42).1, 0);
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 69);
	});
}

#[test]
fn slashing_incomplete_reserved_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 42));
		assert_eq!(Balances::slash_reserved(&1, 69).1, 27);
		assert_eq!(Balances::free_balance(&1), 69);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 69);
	});
}

#[test]
fn transferring_reserved_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 110));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 41), 0);
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::free_balance(&2), 42);
	});
}

#[test]
fn transferring_reserved_balance_to_nonexistent_should_fail() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		assert_noop!(Balances::repatriate_reserved(&1, &2, 42), "beneficiary account must pre-exist");
	});
}

#[test]
fn transferring_incomplete_reserved_balance_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		let _ = Balances::deposit_creating(&1, 110);
		let _ = Balances::deposit_creating(&2, 1);
		assert_ok!(Balances::reserve(&1, 41));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 69), 28);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(Balances::free_balance(&1), 69);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::free_balance(&2), 42);
	});
}

#[test]
fn transferring_too_high_value_should_not_panic() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		<FreeBalance<Runtime>>::insert(1, u64::max_value());
		<FreeBalance<Runtime>>::insert(2, 1);

		assert_err!(
			Balances::transfer(Some(1).into(), 2, u64::max_value()),
			"destination balance too high to receive value"
		);

		assert_eq!(Balances::free_balance(&1), u64::max_value());
		assert_eq!(Balances::free_balance(&2), 1);
	});
}

#[test]
fn account_create_on_free_too_low_with_other() {
	with_externalities(
		&mut ExtBuilder::default().existential_deposit(100).build(),
		|| {
			let _ = Balances::deposit_creating(&1, 100);
			assert_eq!(<TotalIssuance<Runtime>>::get(), 100);

			// No-op.
			let _ = Balances::deposit_creating(&2, 50);
			assert_eq!(Balances::free_balance(&2), 0);
			assert_eq!(<TotalIssuance<Runtime>>::get(), 100);
		}
	)
}


#[test]
fn account_create_on_free_too_low() {
	with_externalities(
		&mut ExtBuilder::default().existential_deposit(100).build(),
		|| {
			// No-op.
			let _ = Balances::deposit_creating(&2, 50);
			assert_eq!(Balances::free_balance(&2), 0);
			assert_eq!(<TotalIssuance<Runtime>>::get(), 0);
		}
	)
}

#[test]
fn account_removal_on_free_too_low() {
	with_externalities(
		&mut ExtBuilder::default().existential_deposit(100).build(),
		|| {
			assert_eq!(<TotalIssuance<Runtime>>::get(), 0);

			// Setup two accounts with free balance above the existential threshold.
			let _ = Balances::deposit_creating(&1, 110);
			let _ = Balances::deposit_creating(&2, 110);

			assert_eq!(Balances::free_balance(&1), 110);
			assert_eq!(Balances::free_balance(&2), 110);
			assert_eq!(<TotalIssuance<Runtime>>::get(), 220);

			// Transfer funds from account 1 of such amount that after this transfer
			// the balance of account 1 will be below the existential threshold.
			// This should lead to the removal of all balance of this account.
			assert_ok!(Balances::transfer(Some(1).into(), 2, 20));

			// Verify free balance removal of account 1.
			assert_eq!(Balances::free_balance(&1), 0);
			assert_eq!(Balances::free_balance(&2), 130);

			// Verify that TotalIssuance tracks balance removal when free balance is too low.
			assert_eq!(<TotalIssuance<Runtime>>::get(), 130);
		},
	);
}

#[test]
fn transfer_overflow_isnt_exploitable() {
	with_externalities(
		&mut ExtBuilder::default().creation_fee(50).build(),
		|| {
			// Craft a value that will overflow if summed with `creation_fee`.
			let evil_value = u64::max_value() - 49;

			assert_err!(
				Balances::transfer(Some(1).into(), 5, evil_value),
				"got overflow after adding a fee to value"
			);
		}
	);
}

#[test]
fn check_vesting_status() {
		with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(256)
			.monied(true)
			.vesting(true)
			.build(),
		|| {
			assert_eq!(System::block_number(), 1);
			let user1_free_balance = Balances::free_balance(&1);
			let user2_free_balance = Balances::free_balance(&2);
			assert_eq!(user1_free_balance, 256 * 10); // Account 1 has free balance
			assert_eq!(user2_free_balance, 256 * 20); // Account 2 has free balance
			let user1_vesting_schedule = VestingSchedule {
				offset: 256 * 10,
				per_block: 256,
			};
			let user2_vesting_schedule = VestingSchedule {
				offset: 256 * 30,
				per_block: 256,
			};
			assert_eq!(Balances::vesting(&1), Some(user1_vesting_schedule)); // Account 1 has a vesting schedule
			assert_eq!(Balances::vesting(&2), Some(user2_vesting_schedule)); // Account 2 has a vesting schedule

			assert_eq!(Balances::vesting_balance(&1), user1_free_balance - 256); // Account 1 has only 256 units vested at block 1

			System::set_block_number(10);
			assert_eq!(System::block_number(), 10);

			assert_eq!(Balances::vesting_balance(&1), 0); // Account 1 has fully vested by block 10
			assert_eq!(Balances::vesting_balance(&2), user2_free_balance); // Account 2 has started vesting by block 10

			System::set_block_number(30);
			assert_eq!(System::block_number(), 30);

			assert_eq!(Balances::vesting_balance(&1), 0); // Account 1 is still fully vested, and not negative
			assert_eq!(Balances::vesting_balance(&2), 0); // Account 2 has fully vested by block 30

		}
	);
}

#[test]
fn unvested_balance_should_not_transfer() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(10)
			.monied(true)
			.vesting(true)
			.build(),
		|| {
			assert_eq!(System::block_number(), 1);
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 100); // Account 1 has free balance
			assert_eq!(Balances::vesting_balance(&1), 90); // Account 1 has only 10 units vested at block 1
			assert_noop!(
				Balances::transfer(Some(1).into(), 2, 11),
				"vesting balance too high to send value"
			); // Account 1 cannot send more than vested amount
		}
	);
}

#[test]
fn vested_balance_should_transfer() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(10)
			.monied(true)
			.vesting(true)
			.build(),
		|| {
			assert_eq!(System::block_number(), 1);
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 100); // Account 1 has free balance
			assert_eq!(Balances::vesting_balance(&1), 90); // Account 1 has only 10 units vested at block 1
			assert_ok!(Balances::transfer(Some(1).into(), 2, 10));
		}
	);
}

#[test]
fn extra_balance_should_transfer() {
	with_externalities(
		&mut ExtBuilder::default()
			.existential_deposit(10)
			.monied(true)
			.vesting(true)
			.build(),
		|| {
			assert_eq!(System::block_number(), 1);
			assert_ok!(Balances::transfer(Some(3).into(), 1, 100));
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 200); // Account 1 has 100 more free balance than normal

			assert_eq!(Balances::vesting_balance(&1), 90); // Account 1 has 90 units vested at block 1
			assert_ok!(Balances::transfer(Some(1).into(), 2, 105)); // Account 1 can send extra units gained
		}
	);
}
