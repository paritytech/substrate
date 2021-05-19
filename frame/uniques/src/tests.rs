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

//! Tests for Uniques pallet.

use super::*;
use crate::mock::*;
use frame_support::{assert_ok, assert_noop, traits::Currency};
/*
fn last_event() -> mock::Event {
	frame_system::Pallet::<Test>::events().pop().expect("Event expected").event
}
*/
fn assets() -> Vec<(u64, u32, u32)> {
	let mut r: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
	r.sort();
	let mut s: Vec<_> = Asset::<Test>::iter().map(|x| (x.2.owner, x.0, x.1)).collect();
	s.sort();
	assert_eq!(r, s);
	for class in Asset::<Test>::iter()
		.map(|x| x.0)
		.scan(None, |s, item| if s.map_or(false, |last| last == item) {
				*s = Some(item);
				Some(None)
			} else {
				Some(Some(item))
			}
		).filter_map(|item| item)
	{
		let details = Class::<Test>::get(class).unwrap();
		let instances = Asset::<Test>::iter_prefix(class).count() as u32;
		assert_eq!(details.instances, instances);
		let free_holds = Asset::<Test>::iter_prefix(class)
			.filter(|(_, item)| item.deposit.is_zero())
			.count() as u32;
		assert_eq!(details.free_holds, free_holds);
	}
	r
}

#[test]
fn basic_setup_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(assets(), vec![]);
	});
}

#[test]
fn basic_minting_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(assets(), vec![(1, 0, 42)]);

		assert_ok!(Uniques::force_create(Origin::root(), 1, 2, true));
		assert_ok!(Uniques::mint(Origin::signed(2), 1, 69, 1));
		assert_eq!(assets(), vec![(1, 0, 42), (1, 1, 69)]);
	});
}

#[test]
fn lifecycle_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1));
		assert_eq!(Balances::reserved_balance(&1), 2);

		assert_ok!(Uniques::set_class_metadata(Origin::signed(1), 0, vec![0], vec![0], false));
		assert_eq!(Balances::reserved_balance(&1), 5);
		assert!(ClassMetadataOf::<Test>::contains_key(0));

		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 10));
		assert_eq!(Balances::reserved_balance(&1), 6);
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 69, 20));
		assert_eq!(Balances::reserved_balance(&1), 7);
		assert_eq!(assets(), vec![(10, 0, 42), (20, 0, 69)]);

		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, vec![42], vec![42], false));
		assert_eq!(Balances::reserved_balance(&1), 10);
		assert!(InstanceMetadataOf::<Test>::contains_key(0, 42));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 69, vec![69], vec![69], false));
		assert_eq!(Balances::reserved_balance(&1), 13);
		assert!(InstanceMetadataOf::<Test>::contains_key(0, 69));

		let w = Class::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Uniques::destroy(Origin::signed(1), 0, w));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert!(!Class::<Test>::contains_key(0));
		assert!(!Asset::<Test>::contains_key(0, 42));
		assert!(!Asset::<Test>::contains_key(0, 69));
		assert!(!ClassMetadataOf::<Test>::contains_key(0));
		assert!(!InstanceMetadataOf::<Test>::contains_key(0, 42));
		assert!(!InstanceMetadataOf::<Test>::contains_key(0, 69));
		assert_eq!(assets(), vec![]);
	});
}

#[test]
fn destroy_with_bad_witness_should_not_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1));

		let w = Class::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_noop!(Uniques::destroy(Origin::signed(1), 0, w), Error::<Test>::BadWitness);
	});
}

#[test]
fn mint_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::owner(0, 42).unwrap(), 1);
		assert_eq!(assets(), vec![(1, 0, 42)]);
	});
}

#[test]
fn transfer_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));

		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 42, 3));
		assert_eq!(assets(), vec![(3, 0, 42)]);
		assert_noop!(Uniques::transfer(Origin::signed(2), 0, 42, 4), Error::<Test>::NoPermission);

		assert_ok!(Uniques::approve_transfer(Origin::signed(3), 0, 42, 2));
		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 42, 4));
	});
}

#[test]
fn freezing_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_ok!(Uniques::freeze(Origin::signed(1), 0, 42));
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 42, 2), Error::<Test>::Frozen);

		assert_ok!(Uniques::thaw(Origin::signed(1), 0, 42));
		assert_ok!(Uniques::freeze_class(Origin::signed(1), 0));
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 42, 2), Error::<Test>::Frozen);

		assert_ok!(Uniques::thaw_class(Origin::signed(1), 0));
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 42, 2));
	});
}

#[test]
fn origin_guards_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_noop!(Uniques::transfer_ownership(Origin::signed(2), 0, 2), Error::<Test>::NoPermission);
		assert_noop!(Uniques::set_team(Origin::signed(2), 0, 2, 2, 2), Error::<Test>::NoPermission);
		assert_noop!(Uniques::freeze(Origin::signed(2), 0, 42), Error::<Test>::NoPermission);
		assert_noop!(Uniques::thaw(Origin::signed(2), 0, 42), Error::<Test>::NoPermission);
		assert_noop!(Uniques::mint(Origin::signed(2), 0, 69, 2), Error::<Test>::NoPermission);
		assert_noop!(Uniques::burn(Origin::signed(2), 0, 42, None), Error::<Test>::NoPermission);
		let w = Class::<Test>::get(0).unwrap().destroy_witness();
		assert_noop!(Uniques::destroy(Origin::signed(2), 0, w), Error::<Test>::NoPermission);
	});
}
/*
#[test]
fn transfer_owner_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1, 1));

		assert_eq!(Balances::reserved_balance(&1), 1);

		assert_ok!(Uniques::transfer_ownership(Origin::signed(1), 0, 2));
		assert_eq!(Balances::reserved_balance(&2), 1);
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert_noop!(Uniques::transfer_ownership(Origin::signed(1), 0, 1), Error::<Test>::NoPermission);

		// Set metadata now and make sure that deposit gets transferred back.
		assert_ok!(Uniques::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12));
		assert_ok!(Uniques::transfer_ownership(Origin::signed(2), 0, 1));
		assert_eq!(Balances::reserved_balance(&1), 22);
		assert_eq!(Balances::reserved_balance(&2), 0);
	});
}

#[test]
fn set_team_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::set_team(Origin::signed(1), 0, 2, 3, 4));

		assert_ok!(Uniques::mint(Origin::signed(2), 0, 2, 100));
		assert_ok!(Uniques::freeze(Origin::signed(4), 0, 2));
		assert_ok!(Uniques::thaw(Origin::signed(3), 0, 2));
		assert_ok!(Uniques::force_transfer(Origin::signed(3), 0, 2, 3, 100));
		assert_ok!(Uniques::burn(Origin::signed(3), 0, 3, 100));
	});
}

#[test]
fn transferring_to_frozen_account_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 2, 100));
		assert_eq!(Uniques::balance(0, 1), 100);
		assert_eq!(Uniques::balance(0, 2), 100);
		assert_ok!(Uniques::freeze(Origin::signed(1), 0, 2));
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Uniques::balance(0, 2), 150);
	});
}

#[test]
fn transferring_amount_more_than_available_balance_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 1), 100);
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Uniques::balance(0, 1), 50);
		assert_eq!(Uniques::balance(0, 2), 50);
		assert_ok!(Uniques::burn(Origin::signed(1), 0, 1, u64::max_value()));
		assert_eq!(Uniques::balance(0, 1), 0);
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 1, 50), Error::<Test>::BalanceLow);
		assert_noop!(Uniques::transfer(Origin::signed(2), 0, 1, 51), Error::<Test>::BalanceLow);
	});
}

#[test]
fn transferring_less_than_one_unit_is_fine() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 1), 100);
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 0));
		assert_eq!(
			last_event(),
			mock::Event::pallet_assets(crate::Event::Transferred(0, 1, 2, 0)),
		);
	});
}

#[test]
fn transferring_more_units_than_total_supply_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 1), 100);
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 2, 101), Error::<Test>::BalanceLow);
	});
}

#[test]
fn burning_asset_balance_with_positive_balance_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 1), 100);
		assert_ok!(Uniques::burn(Origin::signed(1), 0, 1, u64::max_value()));
		assert_eq!(Uniques::balance(0, 1), 0);
	});
}

#[test]
fn burning_asset_balance_with_zero_balance_does_nothing() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 2), 0);
		assert_ok!(Uniques::burn(Origin::signed(1), 0, 2, u64::max_value()));
		assert_eq!(Uniques::balance(0, 2), 0);
		assert_eq!(Uniques::total_supply(0), 100);
	});
}

#[test]
fn set_metadata_should_work() {
	new_test_ext().execute_with(|| {
		// Cannot add metadata to unknown asset
		assert_noop!(
				Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::Unknown,
			);
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		// Cannot add metadata to unowned asset
		assert_noop!(
				Uniques::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::NoPermission,
			);

		// Cannot add oversized metadata
		assert_noop!(
				Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 100], vec![0u8; 10], 12),
				Error::<Test>::BadMetadata,
			);
		assert_noop!(
				Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 100], 12),
				Error::<Test>::BadMetadata,
			);

		// Successfully add metadata and take deposit
		Balances::make_free_balance_be(&1, 30);
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12));
		assert_eq!(Balances::free_balance(&1), 9);

		// Update deposit
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 5], 12));
		assert_eq!(Balances::free_balance(&1), 14);
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 15], 12));
		assert_eq!(Balances::free_balance(&1), 4);

		// Cannot over-reserve
		assert_noop!(
				Uniques::set_metadata(Origin::signed(1), 0, vec![0u8; 20], vec![0u8; 20], 12),
				BalancesError::<Test, _>::InsufficientBalance,
			);

		// Clear Metadata
		assert!(Metadata::<Test>::contains_key(0));
		assert_noop!(Uniques::clear_metadata(Origin::signed(2), 0), Error::<Test>::NoPermission);
		assert_noop!(Uniques::clear_metadata(Origin::signed(1), 1), Error::<Test>::Unknown);
		assert_ok!(Uniques::clear_metadata(Origin::signed(1), 0));
		assert!(!Metadata::<Test>::contains_key(0));
	});
}

#[test]
fn freezer_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true, 10));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(Uniques::balance(0, 1), 100);


		// freeze 50 of it.
		set_frozen_balance(0, 1, 50);

		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 20));
		// cannot transfer another 21 away as this would take the non-frozen balance (30) to below
		// the minimum balance (10).
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 2, 21), Error::<Test>::BalanceLow);

		// create an approved transfer...
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		let e = Error::<Test>::BalanceLow;
		// ...but that wont work either:
		assert_noop!(Uniques::transfer_approved(Origin::signed(2), 0, 1, 2, 21), e);
		// a force transfer won't work also.
		let e = Error::<Test>::BalanceLow;
		assert_noop!(Uniques::force_transfer(Origin::signed(1), 0, 1, 2, 21), e);

		// reduce it to only 49 frozen...
		set_frozen_balance(0, 1, 49);
		// ...and it's all good:
		assert_ok!(Uniques::force_transfer(Origin::signed(1), 0, 1, 2, 21));

		// and if we clear it, we can remove the account completely.
		clear_frozen_balance(0, 1);
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(hooks(), vec![Hook::Died(0, 1)]);
	});
}

#[test]
fn imbalances_should_work() {
	use frame_support::traits::tokens::fungibles::Balanced;

	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));

		let imb = Uniques::issue(0, 100);
		assert_eq!(Uniques::total_supply(0), 100);
		assert_eq!(imb.peek(), 100);

		let (imb1, imb2) = imb.split(30);
		assert_eq!(imb1.peek(), 30);
		assert_eq!(imb2.peek(), 70);

		drop(imb2);
		assert_eq!(Uniques::total_supply(0), 30);

		assert!(Uniques::resolve(&1, imb1).is_ok());
		assert_eq!(Uniques::balance(0, 1), 30);
		assert_eq!(Uniques::total_supply(0), 30);
	});
}

#[test]
fn force_metadata_should_work() {
	new_test_ext().execute_with(|| {
		//force set metadata works
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::force_set_metadata(Origin::root(), 0, vec![0u8; 10], vec![0u8; 10], 8, false));
		assert!(Metadata::<Test>::contains_key(0));

		//overwrites existing metadata
		let asset_original_metadata = Metadata::<Test>::get(0);
		assert_ok!(Uniques::force_set_metadata(Origin::root(), 0, vec![1u8; 10], vec![1u8; 10], 8, false));
		assert_ne!(Metadata::<Test>::get(0), asset_original_metadata);

		//attempt to set metadata for non-existent asset class
		assert_noop!(
			Uniques::force_set_metadata(Origin::root(), 1, vec![0u8; 10], vec![0u8; 10], 8, false),
			Error::<Test>::Unknown
		);

		//string length limit check
		let limit = StringLimit::get() as usize;
		assert_noop!(
			Uniques::force_set_metadata(Origin::root(), 0, vec![0u8; limit + 1], vec![0u8; 10], 8, false),
			Error::<Test>::BadMetadata
		);
		assert_noop!(
			Uniques::force_set_metadata(Origin::root(), 0, vec![0u8; 10], vec![0u8; limit + 1], 8, false),
			Error::<Test>::BadMetadata
		);

		//force clear metadata works
		assert!(Metadata::<Test>::contains_key(0));
		assert_ok!(Uniques::force_clear_metadata(Origin::root(), 0));
		assert!(!Metadata::<Test>::contains_key(0));

		//Error handles clearing non-existent asset class
		assert_noop!(Uniques::force_clear_metadata(Origin::root(), 1), Error::<Test>::Unknown);
	});
}

#[test]
fn force_asset_status_should_work(){
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 10);
		Balances::make_free_balance_be(&2, 10);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1, 30));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 1, 50));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 2, 150));

		//force asset status to change min_balance > balance
		assert_ok!(Uniques::force_asset_status(Origin::root(), 0, 1, 1, 1, 1, 100, true, false));
		assert_eq!(Uniques::balance(0, 1), 50);

		//account can recieve assets for balance < min_balance
		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 1, 1));
		assert_eq!(Uniques::balance(0, 1), 51);

		//account on outbound transfer will cleanup for balance < min_balance
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 2, 1));
		assert_eq!(Uniques::balance(0,1), 0);

		//won't create new account with balance below min_balance
		assert_noop!(Uniques::transfer(Origin::signed(2), 0, 3, 50), TokenError::BelowMinimum);

		//force asset status will not execute for non-existent class
		assert_noop!(
			Uniques::force_asset_status(Origin::root(), 1, 1, 1, 1, 1, 90, true, false),
			Error::<Test>::Unknown
		);

		//account drains to completion when funds dip below min_balance
		assert_ok!(Uniques::force_asset_status(Origin::root(), 0, 1, 1, 1, 1, 110, true, false));
		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 1, 110));
		assert_eq!(Uniques::balance(0, 1), 200);
		assert_eq!(Uniques::balance(0, 2), 0);
		assert_eq!(Uniques::total_supply(0), 200);
	});
}

#[test]
fn approval_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Balances::reserved_balance(&1), 1);
		assert_ok!(Uniques::transfer_approved(Origin::signed(2), 0, 1, 3, 40));
		assert_ok!(Uniques::cancel_approval(Origin::signed(1), 0, 2));
		assert_eq!(Uniques::balance(0, 1), 60);
		assert_eq!(Uniques::balance(0, 3), 40);
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn approval_deposits_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		let e = BalancesError::<Test>::InsufficientBalance;
		assert_noop!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50), e);

		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_eq!(Balances::reserved_balance(&1), 1);

		assert_ok!(Uniques::transfer_approved(Origin::signed(2), 0, 1, 3, 50));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_ok!(Uniques::cancel_approval(Origin::signed(1), 0, 2));
		assert_eq!(Balances::reserved_balance(&1), 0);
	});
}

#[test]
fn cannot_transfer_more_than_approved() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		let e = Error::<Test>::Unapproved;
		assert_noop!(Uniques::transfer_approved(Origin::signed(2), 0, 1, 3, 51), e);
	});
}

#[test]
fn cannot_transfer_more_than_exists() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 101));
		let e = Error::<Test>::BalanceLow;
		assert_noop!(Uniques::transfer_approved(Origin::signed(2), 0, 1, 3, 101), e);
	});
}

#[test]
fn cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		assert_noop!(Uniques::cancel_approval(Origin::signed(1), 1, 2), Error::<Test>::Unknown);
		assert_noop!(Uniques::cancel_approval(Origin::signed(2), 0, 2), Error::<Test>::Unknown);
		assert_noop!(Uniques::cancel_approval(Origin::signed(1), 0, 3), Error::<Test>::Unknown);
		assert_ok!(Uniques::cancel_approval(Origin::signed(1), 0, 2));
		assert_noop!(Uniques::cancel_approval(Origin::signed(1), 0, 2), Error::<Test>::Unknown);
	});
}

#[test]
fn force_cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		Balances::make_free_balance_be(&1, 1);
		assert_ok!(Uniques::approve_transfer(Origin::signed(1), 0, 2, 50));
		let e = Error::<Test>::NoPermission;
		assert_noop!(Uniques::force_cancel_approval(Origin::signed(2), 0, 1, 2), e);
		assert_noop!(Uniques::force_cancel_approval(Origin::signed(1), 1, 1, 2), Error::<Test>::Unknown);
		assert_noop!(Uniques::force_cancel_approval(Origin::signed(1), 0, 2, 2), Error::<Test>::Unknown);
		assert_noop!(Uniques::force_cancel_approval(Origin::signed(1), 0, 1, 3), Error::<Test>::Unknown);
		assert_ok!(Uniques::force_cancel_approval(Origin::signed(1), 0, 1, 2));
		assert_noop!(Uniques::force_cancel_approval(Origin::signed(1), 0, 1, 2), Error::<Test>::Unknown);
	});
}
*/
