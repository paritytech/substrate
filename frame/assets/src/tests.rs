// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for Assets pallet.

use super::*;
use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop, traits::Currency};
use pallet_balances::Error as BalancesError;

fn last_event() -> mock::Event {
	frame_system::Module::<Test>::events().pop().expect("Event expected").event
}

#[test]
fn basic_minting_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::mint(Origin::signed(1), 0, 2, 100));
		assert_eq!(Assets::balance(0, 2), 100);
	});
}

#[test]
fn approval_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Balances::reserved_balance(&1), 1);
		assert_ok!(Assets::transfer_approved(Origin::signed(2), 0, 1, 3, 40));
		assert_ok!(Assets::cancel_approval(Origin::signed(1), 0, 2));
		assert_eq!(Assets::balance(0, 1), 60);
		assert_eq!(Assets::balance(0, 3), 40);
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn approval_deposits_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		let e = BalancesError::<Test>::InsufficientBalance;
		assert_noop!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50), e);

		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Balances::reserved_balance(&1), 1);

		assert_ok!(Assets::transfer_approved(Origin::signed(2), 0, 1, 3, 50));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_ok!(Assets::cancel_approval(Origin::signed(1), 0, 2));
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn cannot_transfer_more_than_approved() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		let e = Error::<Test>::Unapproved;
		assert_noop!(Assets::transfer_approved(Origin::signed(2), 0, 1, 3, 51), e);
	});
}

#[test]
fn cannot_transfer_more_than_exists() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 101));
		let e = Error::<Test>::BalanceLow;
		assert_noop!(Assets::transfer_approved(Origin::signed(2), 0, 1, 3, 101), e);
	});
}

#[test]
fn cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_noop!(Assets::cancel_approval(Origin::signed(1), 1, 2), Error::<Test>::Unknown);
		assert_noop!(Assets::cancel_approval(Origin::signed(2), 0, 2), Error::<Test>::Unknown);
		assert_noop!(Assets::cancel_approval(Origin::signed(1), 0, 3), Error::<Test>::Unknown);
		assert_ok!(Assets::cancel_approval(Origin::signed(1), 0, 2));
		assert_noop!(Assets::cancel_approval(Origin::signed(1), 0, 2), Error::<Test>::Unknown);
	});
}

#[test]
fn force_cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Assets::approve_transfer(Origin::signed(1), 0, 2, 50));
		let e = Error::<Test>::NoPermission;
		assert_noop!(Assets::force_cancel_approval(Origin::signed(2), 0, 1, 2), e);
		assert_noop!(Assets::force_cancel_approval(Origin::signed(1), 1, 1, 2), Error::<Test>::Unknown);
		assert_noop!(Assets::force_cancel_approval(Origin::signed(1), 0, 2, 2), Error::<Test>::Unknown);
		assert_noop!(Assets::force_cancel_approval(Origin::signed(1), 0, 1, 3), Error::<Test>::Unknown);
		assert_ok!(Assets::force_cancel_approval(Origin::signed(1), 0, 1, 2));
		assert_noop!(Assets::force_cancel_approval(Origin::signed(1), 0, 1, 2), Error::<Test>::Unknown);
	});
}

#[test]
fn lifecycle_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));
		assert_eq!(Balances::reserved_balance(&1), 1);
		assert!(Asset::<Test>::contains_key(0));

		assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0], vec![0], 12));
		assert_eq!(Balances::reserved_balance(&1), 4);
		assert!(Metadata::<Test>::contains_key(0));

		Balances::make_free_balance_be(&10, 100);
		assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
		Balances::make_free_balance_be(&20, 100);
		assert_ok!(Assets::mint(Origin::signed(1), 0, 20, 100));
		assert_eq!(Account::<Test>::iter_prefix(0).count(), 2);

		let w = Asset::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Assets::destroy(Origin::signed(1), 0, w));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert!(!Asset::<Test>::contains_key(0));
		assert!(!Metadata::<Test>::contains_key(0));
		assert_eq!(Account::<Test>::iter_prefix(0).count(), 0);

		assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));
		assert_eq!(Balances::reserved_balance(&1), 1);
		assert!(Asset::<Test>::contains_key(0));

		assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0], vec![0], 12));
		assert_eq!(Balances::reserved_balance(&1), 4);
		assert!(Metadata::<Test>::contains_key(0));

		assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 20, 100));
		assert_eq!(Account::<Test>::iter_prefix(0).count(), 2);

		let w = Asset::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Assets::destroy(Origin::root(), 0, w));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert!(!Asset::<Test>::contains_key(0));
		assert!(!Metadata::<Test>::contains_key(0));
		assert_eq!(Account::<Test>::iter_prefix(0).count(), 0);
	});
}

#[test]
fn destroy_with_bad_witness_should_not_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		let w = Asset::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
		assert_noop!(Assets::destroy(Origin::signed(1), 0, w), Error::<Test>::BadWitness);
	});
}

#[test]
fn non_providing_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, false, 1));

		Balances::make_free_balance_be(&0, 100);
		assert_ok!(Assets::mint(Origin::signed(1), 0, 0, 100));

		// Cannot mint into account 2 since it doesn't (yet) exist...
		assert_noop!(Assets::mint(Origin::signed(1), 0, 1, 100), Error::<Test>::NoProvider);
		// ...or transfer...
		assert_noop!(Assets::transfer(Origin::signed(0), 0, 1, 50), Error::<Test>::NoProvider);
		// ...or force-transfer
		assert_noop!(Assets::force_transfer(Origin::signed(1), 0, 0, 1, 50), Error::<Test>::NoProvider);

		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);
		assert_ok!(Assets::transfer(Origin::signed(0), 0, 1, 25));
		assert_ok!(Assets::force_transfer(Origin::signed(1), 0, 0, 2, 25));
	});
}

#[test]
fn min_balance_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 10));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

		// Cannot create a new account with a balance that is below minimum...
		assert_noop!(Assets::mint(Origin::signed(1), 0, 2, 9), Error::<Test>::BalanceLow);
		assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 9), Error::<Test>::BalanceLow);
		assert_noop!(Assets::force_transfer(Origin::signed(1), 0, 1, 2, 9), Error::<Test>::BalanceLow);

		// When deducting from an account to below minimum, it should be reaped.

		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 91));
		assert!(Assets::balance(0, 1).is_zero());
		assert_eq!(Assets::balance(0, 2), 100);
		assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

		assert_ok!(Assets::force_transfer(Origin::signed(1), 0, 2, 1, 91));
		assert!(Assets::balance(0, 2).is_zero());
		assert_eq!(Assets::balance(0, 1), 100);
		assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

		assert_ok!(Assets::burn(Origin::signed(1), 0, 1, 91));
		assert!(Assets::balance(0, 1).is_zero());
		assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 0);
	});
}

#[test]
fn querying_total_supply_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Assets::balance(0, 1), 50);
		assert_eq!(Assets::balance(0, 2), 50);
		assert_ok!(Assets::transfer(Origin::signed(2), 0, 3, 31));
		assert_eq!(Assets::balance(0, 1), 50);
		assert_eq!(Assets::balance(0, 2), 19);
		assert_eq!(Assets::balance(0, 3), 31);
		assert_ok!(Assets::burn(Origin::signed(1), 0, 3, u64::max_value()));
		assert_eq!(Assets::total_supply(0), 69);
	});
}

#[test]
fn transferring_amount_below_available_balance_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Assets::balance(0, 1), 50);
		assert_eq!(Assets::balance(0, 2), 50);
	});
}

#[test]
fn transferring_enough_to_kill_source_when_keep_alive_should_fail() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 10));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_noop!(Assets::transfer_keep_alive(Origin::signed(1), 0, 2, 91), Error::<Test>::WouldDie);
		assert_ok!(Assets::transfer_keep_alive(Origin::signed(1), 0, 2, 90));
		assert_eq!(Assets::balance(0, 1), 10);
		assert_eq!(Assets::balance(0, 2), 90);
	});
}

#[test]
fn transferring_frozen_user_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::freeze(Origin::signed(1), 0, 1));
		assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 50), Error::<Test>::Frozen);
		assert_ok!(Assets::thaw(Origin::signed(1), 0, 1));
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
	});
}

#[test]
fn transferring_frozen_asset_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::freeze_asset(Origin::signed(1), 0));
		assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 50), Error::<Test>::Frozen);
		assert_ok!(Assets::thaw_asset(Origin::signed(1), 0));
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
	});
}

#[test]
fn origin_guards_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_noop!(Assets::transfer_ownership(Origin::signed(2), 0, 2), Error::<Test>::NoPermission);
		assert_noop!(Assets::set_team(Origin::signed(2), 0, 2, 2, 2), Error::<Test>::NoPermission);
		assert_noop!(Assets::freeze(Origin::signed(2), 0, 1), Error::<Test>::NoPermission);
		assert_noop!(Assets::thaw(Origin::signed(2), 0, 2), Error::<Test>::NoPermission);
		assert_noop!(Assets::mint(Origin::signed(2), 0, 2, 100), Error::<Test>::NoPermission);
		assert_noop!(Assets::burn(Origin::signed(2), 0, 1, 100), Error::<Test>::NoPermission);
		assert_noop!(Assets::force_transfer(Origin::signed(2), 0, 1, 2, 100), Error::<Test>::NoPermission);
		let w = Asset::<Test>::get(0).unwrap().destroy_witness();
		assert_noop!(Assets::destroy(Origin::signed(2), 0, w), Error::<Test>::NoPermission);
	});
}

#[test]
fn transfer_owner_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);
		assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));

		assert_eq!(Balances::reserved_balance(&1), 1);

		assert_ok!(Assets::transfer_ownership(Origin::signed(1), 0, 2));
		assert_eq!(Balances::reserved_balance(&2), 1);
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert_noop!(Assets::transfer_ownership(Origin::signed(1), 0, 1), Error::<Test>::NoPermission);

		// Set metadata now and make sure that deposit gets transferred back.
		assert_ok!(Assets::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12));
		assert_ok!(Assets::transfer_ownership(Origin::signed(2), 0, 1));
		assert_eq!(Balances::reserved_balance(&1), 22);
		assert_eq!(Balances::reserved_balance(&2), 0);
	});
}

#[test]
fn set_team_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::set_team(Origin::signed(1), 0, 2, 3, 4));

		assert_ok!(Assets::mint(Origin::signed(2), 0, 2, 100));
		assert_ok!(Assets::freeze(Origin::signed(4), 0, 2));
		assert_ok!(Assets::thaw(Origin::signed(3), 0, 2));
		assert_ok!(Assets::force_transfer(Origin::signed(3), 0, 2, 3, 100));
		assert_ok!(Assets::burn(Origin::signed(3), 0, 3, 100));
	});
}

#[test]
fn transferring_to_frozen_account_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 2, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_eq!(Assets::balance(0, 2), 100);
		assert_ok!(Assets::freeze(Origin::signed(1), 0, 2));
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Assets::balance(0, 2), 150);
	});
}

#[test]
fn transferring_amount_more_than_available_balance_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Assets::balance(0, 1), 50);
		assert_eq!(Assets::balance(0, 2), 50);
		assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
		assert_eq!(Assets::balance(0, 1), 0);
		assert_noop!(Assets::transfer(Origin::signed(1), 0, 1, 50), Error::<Test>::BalanceLow);
		assert_noop!(Assets::transfer(Origin::signed(2), 0, 1, 51), Error::<Test>::BalanceLow);
	});
}

#[test]
fn transferring_less_than_one_unit_is_fine() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 0));
		assert_eq!(
			last_event(),
			mock::Event::pallet_assets(crate::Event::Transferred(0, 1, 2, 0)),
		);
	});
}

#[test]
fn transferring_more_units_than_total_supply_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 101), Error::<Test>::BalanceLow);
	});
}

#[test]
fn burning_asset_balance_with_positive_balance_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 1), 100);
		assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
		assert_eq!(Assets::balance(0, 1), 0);
	});
}

#[test]
fn burning_asset_balance_with_zero_balance_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		assert_eq!(Assets::balance(0, 2), 0);
		assert_noop!(Assets::burn(Origin::signed(1), 0, 2, u64::max_value()), Error::<Test>::BalanceZero);
	});
}

#[test]
fn set_metadata_should_work() {
	new_test_ext().execute_with(|| {
		// Cannot add metadata to unknown asset
		assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::Unknown,
			);
		assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		// Cannot add metadata to unowned asset
		assert_noop!(
				Assets::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::NoPermission,
			);

		// Cannot add oversized metadata
		assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 100], vec![0u8; 10], 12),
				Error::<Test>::BadMetadata,
			);
		assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 100], 12),
				Error::<Test>::BadMetadata,
			);

		// Successfully add metadata and take deposit
		Balances::make_free_balance_be(&1, 30);
		assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12));
		assert_eq!(Balances::free_balance(&1), 9);

		// Update deposit
		assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 5], 12));
		assert_eq!(Balances::free_balance(&1), 14);
		assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 15], 12));
		assert_eq!(Balances::free_balance(&1), 4);

		// Cannot over-reserve
		assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 20], vec![0u8; 20], 12),
				BalancesError::<Test, _>::InsufficientBalance,
			);

		// Clear Metadata
		assert!(Metadata::<Test>::contains_key(0));
		assert_noop!(Assets::clear_metadata(Origin::signed(2), 0), Error::<Test>::NoPermission);
		assert_noop!(Assets::clear_metadata(Origin::signed(1), 1), Error::<Test>::Unknown);
		assert_ok!(Assets::clear_metadata(Origin::signed(1), 0));
		assert!(!Metadata::<Test>::contains_key(0));
	});
}

// TODO: tests for force_set_metadata, force_clear_metadata, force_asset_status
