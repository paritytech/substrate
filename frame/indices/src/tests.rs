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

#![cfg(test)]

use super::*;
use super::mock::*;
use frame_support::{assert_ok, assert_noop};
use pallet_balances::Error as BalancesError;

#[test]
fn claiming_should_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(Indices::claim(Some(0).into(), 0), BalancesError::<Test, _>::InsufficientBalance);
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_noop!(Indices::claim(Some(2).into(), 0), Error::<Test>::InUse);
		assert_eq!(Balances::reserved_balance(1), 1);
	});
}

#[test]
fn freeing_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_ok!(Indices::claim(Some(2).into(), 1));
		assert_noop!(Indices::free(Some(0).into(), 0), Error::<Test>::NotOwner);
		assert_noop!(Indices::free(Some(1).into(), 1), Error::<Test>::NotOwner);
		assert_noop!(Indices::free(Some(1).into(), 2), Error::<Test>::NotAssigned);
		assert_ok!(Indices::free(Some(1).into(), 0));
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_noop!(Indices::free(Some(1).into(), 0), Error::<Test>::NotAssigned);
	});
}

#[test]
fn indexing_lookup_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_ok!(Indices::claim(Some(2).into(), 1));
		assert_eq!(Indices::lookup_index(0), Some(1));
		assert_eq!(Indices::lookup_index(1), Some(2));
		assert_eq!(Indices::lookup_index(2), None);
	});
}

#[test]
fn reclaim_index_on_accounts_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_ok!(Indices::free(Some(1).into(), 0));
		assert_ok!(Indices::claim(Some(2).into(), 0));
		assert_eq!(Indices::lookup_index(0), Some(2));
		assert_eq!(Balances::reserved_balance(2), 1);
	});
}

#[test]
fn transfer_index_on_accounts_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_noop!(Indices::transfer(Some(1).into(), 2, 1), Error::<Test>::NotAssigned);
		assert_noop!(Indices::transfer(Some(2).into(), 3, 0), Error::<Test>::NotOwner);
		assert_ok!(Indices::transfer(Some(1).into(), 3, 0));
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::reserved_balance(3), 1);
		assert_eq!(Indices::lookup_index(0), Some(3));
	});
}

#[test]
fn force_transfer_index_on_preowned_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::claim(Some(1).into(), 0));
		assert_ok!(Indices::force_transfer(Origin::ROOT, 3, 0));
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::reserved_balance(3), 0);
		assert_eq!(Indices::lookup_index(0), Some(3));
	});
}

#[test]
fn force_transfer_index_on_free_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Indices::force_transfer(Origin::ROOT, 3, 0));
		assert_eq!(Balances::reserved_balance(3), 0);
		assert_eq!(Indices::lookup_index(0), Some(3));
	});
}
