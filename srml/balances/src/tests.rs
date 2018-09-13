// Copyright 2017 Parity Technologies (UK) Ltd.
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
use runtime_io::with_externalities;
use mock::{Balances, System, Runtime, new_test_ext, new_test_ext2};

#[test]
fn reward_should_work() {
	with_externalities(&mut new_test_ext(0, true), || {
		assert_eq!(Balances::total_balance(&1), 10);
		assert_ok!(Balances::reward(&1, 10));
		assert_eq!(Balances::total_balance(&1), 20);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 110);
	});
}

#[test]
fn indexing_lookup_should_work() {
	with_externalities(&mut new_test_ext(10, true), || {
		assert_eq!(Balances::lookup_index(0), Some(1));
		assert_eq!(Balances::lookup_index(1), Some(2));
		assert_eq!(Balances::lookup_index(2), Some(3));
		assert_eq!(Balances::lookup_index(3), Some(4));
		assert_eq!(Balances::lookup_index(4), None);
	});
}

#[test]
fn default_indexing_on_new_accounts_should_work() {
	with_externalities(&mut new_test_ext(10, true), || {
		assert_eq!(Balances::lookup_index(4), None);
		assert_ok!(Balances::transfer(Some(1).into(), 5.into(), 10));
		assert_eq!(Balances::lookup_index(4), Some(5));
	});
}

#[test]
fn default_indexing_on_new_accounts_should_work2() {
	with_externalities(&mut new_test_ext2(10, true), || {
		assert_eq!(Balances::lookup_index(4), None);
		// account 1 has 256 * 10 = 2560, account 5 is not exist, ext_deposit is 10, value is 10
		assert_ok!(Balances::transfer(Some(1).into(), 5.into(), 10));
		assert_eq!(Balances::lookup_index(4), Some(5));

		assert_eq!(Balances::free_balance(&1), 256 * 10 - 10 - 50); // 10 is value, 50 is creation_free
	});
}

#[test]
fn default_indexing_on_new_accounts_should_not_work2() {
	with_externalities(&mut new_test_ext2(10, true), || {
		assert_eq!(Balances::lookup_index(4), None);
		// account 1 has 256 * 10 = 2560, account 5 is not exist, ext_deposit is 10, value is 9, not satisfies for ext_deposit
		assert_noop!(Balances::transfer(Some(1).into(), 5.into(), 9), "value too low to create account");
		assert_eq!(Balances::lookup_index(4), None); // account 5 should not exist
		assert_eq!(Balances::free_balance(&1), 256 * 10);
	});
}

#[test]
fn dust_account_removal_should_work() {
	with_externalities(&mut new_test_ext(256 * 10, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(System::account_nonce(&2), 1);
		assert_eq!(Balances::total_balance(&2), 256 * 20);

		assert_ok!(Balances::transfer(Some(2).into(), 5.into(), 256 * 10 + 1));	// index 1 (account 2) becomes zombie
		assert_eq!(Balances::total_balance(&2), 0);
		assert_eq!(Balances::total_balance(&5), 256 * 10 + 1);
		assert_eq!(System::account_nonce(&2), 0);
	});
}

#[test]
fn dust_account_removal_should_work2() {
	with_externalities(&mut new_test_ext2(256 * 10, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(System::account_nonce(&2), 1);
		assert_eq!(Balances::total_balance(&2), 256 * 20);
		assert_ok!(Balances::transfer(Some(2).into(), 5.into(), 256 * 10));	// index 1 (account 2) becomes zombie for 256*10 + 50(fee) < 256 * 10 (ext_deposit)
		assert_eq!(Balances::total_balance(&2), 0);
		assert_eq!(Balances::total_balance(&5), 256 * 10);
		assert_eq!(System::account_nonce(&2), 0);
	});
}

#[test]
fn reclaim_indexing_on_new_accounts_should_work() {
	with_externalities(&mut new_test_ext(256 * 1, true), || {
		assert_eq!(Balances::lookup_index(1), Some(2));
		assert_eq!(Balances::lookup_index(4), None);
		assert_eq!(Balances::total_balance(&2), 256 * 20);

		assert_ok!(Balances::transfer(Some(2).into(), 5.into(), 256 * 20));	// account 2 becomes zombie freeing index 1 for reclaim)
		assert_eq!(Balances::total_balance(&2), 0);

		assert_ok!(Balances::transfer(Some(5).into(), 6.into(), 256 * 1 + 0x69));	// account 6 takes index 1.
		assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(6));
	});
}

#[test]
fn reclaim_indexing_on_new_accounts_should_work2() {
	with_externalities(&mut new_test_ext2(256 * 1, true), || {
		assert_eq!(Balances::lookup_index(1), Some(2));
		assert_eq!(Balances::lookup_index(4), None);
		assert_eq!(Balances::total_balance(&2), 256 * 20);

		assert_ok!(Balances::transfer(Some(2).into(), 5.into(), 256 * 20 - 50));	// account 2 becomes zombie freeing index 1 for reclaim) 50 is creation fee
		assert_eq!(Balances::total_balance(&2), 0);

		assert_ok!(Balances::transfer(Some(5).into(), 6.into(), 256 * 1 + 0x69));	// account 6 takes index 1.
		assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(6));
	});
}

#[test]
fn reserved_balance_should_prevent_reclaim_count() {
	with_externalities(&mut new_test_ext(256 * 1, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(Balances::lookup_index(1), Some(2));
		assert_eq!(Balances::lookup_index(4), None);
		assert_eq!(Balances::total_balance(&2), 256 * 20);

		assert_ok!(Balances::reserve(&2, 256 * 19 + 1));					// account 2 becomes mostly reserved
		assert_eq!(Balances::free_balance(&2), 0);						// "free" account deleted."
		assert_eq!(Balances::total_balance(&2), 256 * 19 + 1);			// reserve still exists.
		assert_eq!(System::account_nonce(&2), 1);

		assert_ok!(Balances::transfer(Some(4).into(), 5.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 for account 5.
		assert_eq!(Balances::total_balance(&5), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(2));					// but fails.
		assert_eq!(System::account_nonce(&2), 1);

		assert_eq!(Balances::slash(&2, 256 * 18 + 2), None);				// account 2 gets slashed
		assert_eq!(Balances::total_balance(&2), 0);						// "free" account deleted."
		assert_eq!(System::account_nonce(&2), 0);

		assert_ok!(Balances::transfer(Some(4).into(), 6.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 again for account 6.
		assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(6));					// and succeeds.
	});
}

#[test]
fn reserved_balance_should_prevent_reclaim_count2() {
	with_externalities(&mut new_test_ext2(256 * 1, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(Balances::lookup_index(1), Some(2));
		assert_eq!(Balances::lookup_index(4), None);
		assert_eq!(Balances::total_balance(&2), 256 * 20);

		assert_ok!(Balances::reserve(&2, 256 * 19 + 1));					// account 2 becomes mostly reserved
		assert_eq!(Balances::free_balance(&2), 0);						// "free" account deleted."
		assert_eq!(Balances::total_balance(&2), 256 * 19 + 1);			// reserve still exists.
		assert_eq!(System::account_nonce(&2), 1);

		assert_ok!(Balances::transfer(Some(4).into(), 5.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 for account 5.
		assert_eq!(Balances::total_balance(&5), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(2));					// but fails.
		assert_eq!(System::account_nonce(&2), 1);

		assert_eq!(Balances::slash(&2, 256 * 18 + 2), None);				// account 2 gets slashed
		assert_eq!(Balances::total_balance(&2), 0);						// "free" account deleted."
		assert_eq!(System::account_nonce(&2), 0);

		assert_ok!(Balances::transfer(Some(4).into(), 6.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 again for account 6.
		assert_eq!(Balances::total_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Balances::lookup_index(1), Some(6));					// and succeeds.
	});
}

#[test]
fn balance_works() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 42);
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
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		Balances::increase_total_stake_by(111);
		assert_ok!(Balances::transfer(Some(1).into(), 2.into(), 69));
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::total_balance(&2), 69);
	});
}

#[test]
fn reserving_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);

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
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_noop!(Balances::transfer(Some(1).into(), 2.into(), 69), "balance too low to send value");
	});
}

#[test]
fn deducting_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		assert_ok!(Balances::reserve(&1, 69));
		assert_eq!(Balances::free_balance(&1), 42);
	});
}

#[test]
fn refunding_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 42);
		Balances::set_reserved_balance(&1, 69);
		Balances::unreserve(&1, 69);
		assert_eq!(Balances::free_balance(&1), 111);
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn slashing_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		Balances::increase_total_stake_by(111);
		assert_ok!(Balances::reserve(&1, 69));
		assert!(Balances::slash(&1, 69).is_none());
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&1), 42);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 44);
	});
}

#[test]
fn slashing_incomplete_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 42);
		Balances::increase_total_stake_by(42);
		assert_ok!(Balances::reserve(&1, 21));
		assert!(Balances::slash(&1, 69).is_some());
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 2);
	});
}

#[test]
fn unreserving_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		Balances::unreserve(&1, 42);
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 42);
	});
}

#[test]
fn slashing_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		Balances::increase_total_stake_by(111);
		assert_ok!(Balances::reserve(&1, 111));
		assert!(Balances::slash_reserved(&1, 42).is_none());
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 71);
	});
}

#[test]
fn slashing_incomplete_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		Balances::increase_total_stake_by(111);
		assert_ok!(Balances::reserve(&1, 42));
		assert!(Balances::slash_reserved(&1, 69).is_some());
		assert_eq!(Balances::free_balance(&1), 69);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(<TotalIssuance<Runtime>>::get(), 71);
	});
}

#[test]
fn transferring_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 110);
		Balances::set_free_balance(&2, 1);
		assert_ok!(Balances::reserve(&1, 110));
		assert_ok!(Balances::repatriate_reserved(&1, &2, 41), None);
		assert_eq!(Balances::reserved_balance(&1), 69);
		assert_eq!(Balances::free_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::free_balance(&2), 42);
	});
}

#[test]
fn transferring_reserved_balance_to_nonexistent_should_fail() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 111);
		assert_ok!(Balances::reserve(&1, 111));
		assert_noop!(Balances::repatriate_reserved(&1, &2, 42), "beneficiary account must pre-exist");
	});
}

#[test]
fn transferring_incomplete_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, false), || {
		Balances::set_free_balance(&1, 110);
		Balances::set_free_balance(&2, 1);
		assert_ok!(Balances::reserve(&1, 41));
		assert!(Balances::repatriate_reserved(&1, &2, 69).unwrap().is_some());
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(Balances::free_balance(&1), 69);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::free_balance(&2), 42);
	});
}

#[test]
fn transferring_too_high_value_should_not_panic() {
	with_externalities(&mut new_test_ext(0, false), || {
		<FreeBalance<Runtime>>::insert(1, u64::max_value());
		<FreeBalance<Runtime>>::insert(2, 1);

		assert_err!(
			Balances::transfer(Some(1).into(), 2.into(), u64::max_value()),
			"destination balance too high to receive value"
		);

		assert_eq!(Balances::free_balance(&1), u64::max_value());
		assert_eq!(Balances::free_balance(&2), 1);
		});
}

#[test]
fn account_removal_on_free_too_low() {
	with_externalities(&mut new_test_ext(100, false), || {
		// Setup two accounts with free balance above the exsistential threshold.
		{
			Balances::set_free_balance(&1, 110);
			Balances::increase_total_stake_by(110);

			Balances::set_free_balance(&2, 110);
			Balances::increase_total_stake_by(110);

			assert_eq!(<TotalIssuance<Runtime>>::get(), 732);
		}

		// Transfer funds from account 1 of such amount that after this transfer
		// the balance of account 1 will be below the exsistential threshold.
		// This should lead to the removal of all balance of this account.
		assert_ok!(Balances::transfer(Some(1).into(), 2.into(), 20));

		// Verify free balance removal of account 1.
		assert_eq!(Balances::free_balance(&1), 0);
		
		// Verify that TotalIssuance tracks balance removal when free balance is too low.
		assert_eq!(<TotalIssuance<Runtime>>::get(), 642);
	});
}
