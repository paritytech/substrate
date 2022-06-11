// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use crate::{mock::*, Event, *};
use frame_support::{assert_noop, assert_ok, traits::Currency};
use pallet_balances::Error as BalancesError;
use sp_std::prelude::*;

fn items() -> Vec<(u64, u32, u32)> {
	let mut r: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
	r.sort();
	let mut s: Vec<_> = Item::<Test>::iter().map(|x| (x.2.owner, x.0, x.1)).collect();
	s.sort();
	assert_eq!(r, s);
	for collection in Item::<Test>::iter()
		.map(|x| x.0)
		.scan(None, |s, item| {
			if s.map_or(false, |last| last == item) {
				*s = Some(item);
				Some(None)
			} else {
				Some(Some(item))
			}
		})
		.flatten()
	{
		let details = Collection::<Test>::get(collection).unwrap();
		let items = Item::<Test>::iter_prefix(collection).count() as u32;
		assert_eq!(details.items, items);
	}
	r
}

fn collections() -> Vec<(u64, u32)> {
	let mut r: Vec<_> = CollectionAccount::<Test>::iter().map(|x| (x.0, x.1)).collect();
	r.sort();
	let mut s: Vec<_> = Collection::<Test>::iter().map(|x| (x.1.owner, x.0)).collect();
	s.sort();
	assert_eq!(r, s);
	r
}

macro_rules! bvec {
	($( $x:tt )*) => {
		vec![$( $x )*].try_into().unwrap()
	}
}

fn attributes(collection: u32) -> Vec<(Option<u32>, Vec<u8>, Vec<u8>)> {
	let mut s: Vec<_> = Attribute::<Test>::iter_prefix((collection,))
		.map(|(k, v)| (k.0, k.1.into(), v.0.into()))
		.collect();
	s.sort();
	s
}

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let mock::Event::Uniques(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();

	System::reset_events();

	result
}

#[test]
fn basic_setup_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(items(), vec![]);
	});
}

#[test]
fn basic_minting_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_eq!(collections(), vec![(1, 0)]);
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_eq!(items(), vec![(1, 0, 42)]);

		assert_ok!(Uniques::force_create(Origin::root(), 1, 2, true));
		assert_eq!(collections(), vec![(1, 0), (2, 1)]);
		assert_ok!(Uniques::mint(Origin::signed(2), 1, 69, 1));
		assert_eq!(items(), vec![(1, 0, 42), (1, 1, 69)]);
	});
}

#[test]
fn lifecycle_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1));
		assert_eq!(Balances::reserved_balance(&1), 2);
		assert_eq!(collections(), vec![(1, 0)]);
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0, 0], false));
		assert_eq!(Balances::reserved_balance(&1), 5);
		assert!(CollectionMetadataOf::<Test>::contains_key(0));

		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 10));
		assert_eq!(Balances::reserved_balance(&1), 6);
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 69, 20));
		assert_eq!(Balances::reserved_balance(&1), 7);
		assert_eq!(items(), vec![(10, 0, 42), (20, 0, 69)]);
		assert_eq!(Collection::<Test>::get(0).unwrap().items, 2);
		assert_eq!(Collection::<Test>::get(0).unwrap().item_metadatas, 0);

		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![42, 42], false));
		assert_eq!(Balances::reserved_balance(&1), 10);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 42));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 69, bvec![69, 69], false));
		assert_eq!(Balances::reserved_balance(&1), 13);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 69));

		let w = Collection::<Test>::get(0).unwrap().destroy_witness();
		assert_eq!(w.items, 2);
		assert_eq!(w.item_metadatas, 2);
		assert_ok!(Uniques::destroy(Origin::signed(1), 0, w));
		assert_eq!(Balances::reserved_balance(&1), 0);

		assert!(!Collection::<Test>::contains_key(0));
		assert!(!Item::<Test>::contains_key(0, 42));
		assert!(!Item::<Test>::contains_key(0, 69));
		assert!(!CollectionMetadataOf::<Test>::contains_key(0));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 42));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 69));
		assert_eq!(collections(), vec![]);
		assert_eq!(items(), vec![]);
	});
}

#[test]
fn destroy_with_bad_witness_should_not_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1));

		let w = Collection::<Test>::get(0).unwrap().destroy_witness();
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
		assert_eq!(collections(), vec![(1, 0)]);
		assert_eq!(items(), vec![(1, 0, 42)]);
	});
}

#[test]
fn transfer_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));

		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 42, 3));
		assert_eq!(items(), vec![(3, 0, 42)]);
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
		assert_ok!(Uniques::freeze_collection(Origin::signed(1), 0));
		assert_noop!(Uniques::transfer(Origin::signed(1), 0, 42, 2), Error::<Test>::Frozen);

		assert_ok!(Uniques::thaw_collection(Origin::signed(1), 0));
		assert_ok!(Uniques::transfer(Origin::signed(1), 0, 42, 2));
	});
}

#[test]
fn origin_guards_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));

		Balances::make_free_balance_be(&2, 100);
		assert_ok!(Uniques::set_accept_ownership(Origin::signed(2), Some(0)));
		assert_noop!(
			Uniques::transfer_ownership(Origin::signed(2), 0, 2),
			Error::<Test>::NoPermission
		);
		assert_noop!(Uniques::set_team(Origin::signed(2), 0, 2, 2, 2), Error::<Test>::NoPermission);
		assert_noop!(Uniques::freeze(Origin::signed(2), 0, 42), Error::<Test>::NoPermission);
		assert_noop!(Uniques::thaw(Origin::signed(2), 0, 42), Error::<Test>::NoPermission);
		assert_noop!(Uniques::mint(Origin::signed(2), 0, 69, 2), Error::<Test>::NoPermission);
		assert_noop!(Uniques::burn(Origin::signed(2), 0, 42, None), Error::<Test>::NoPermission);
		let w = Collection::<Test>::get(0).unwrap().destroy_witness();
		assert_noop!(Uniques::destroy(Origin::signed(2), 0, w), Error::<Test>::NoPermission);
	});
}

#[test]
fn transfer_owner_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);
		Balances::make_free_balance_be(&3, 100);
		assert_ok!(Uniques::create(Origin::signed(1), 0, 1));
		assert_eq!(collections(), vec![(1, 0)]);
		assert_noop!(
			Uniques::transfer_ownership(Origin::signed(1), 0, 2),
			Error::<Test>::Unaccepted
		);
		assert_ok!(Uniques::set_accept_ownership(Origin::signed(2), Some(0)));
		assert_ok!(Uniques::transfer_ownership(Origin::signed(1), 0, 2));

		assert_eq!(collections(), vec![(2, 0)]);
		assert_eq!(Balances::total_balance(&1), 98);
		assert_eq!(Balances::total_balance(&2), 102);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&2), 2);

		assert_ok!(Uniques::set_accept_ownership(Origin::signed(1), Some(0)));
		assert_noop!(
			Uniques::transfer_ownership(Origin::signed(1), 0, 1),
			Error::<Test>::NoPermission
		);

		// Mint and set metadata now and make sure that deposit gets transferred back.
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(2), 0, bvec![0u8; 20], false));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_ok!(Uniques::set_metadata(Origin::signed(2), 0, 42, bvec![0u8; 20], false));
		assert_ok!(Uniques::set_accept_ownership(Origin::signed(3), Some(0)));
		assert_ok!(Uniques::transfer_ownership(Origin::signed(2), 0, 3));
		assert_eq!(collections(), vec![(3, 0)]);
		assert_eq!(Balances::total_balance(&2), 57);
		assert_eq!(Balances::total_balance(&3), 145);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_eq!(Balances::reserved_balance(&3), 45);

		// 2's acceptence from before is reset when it became owner, so it cannot be transfered
		// without a fresh acceptance.
		assert_noop!(
			Uniques::transfer_ownership(Origin::signed(3), 0, 2),
			Error::<Test>::Unaccepted
		);
	});
}

#[test]
fn set_team_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::set_team(Origin::signed(1), 0, 2, 3, 4));

		assert_ok!(Uniques::mint(Origin::signed(2), 0, 42, 2));
		assert_ok!(Uniques::freeze(Origin::signed(4), 0, 42));
		assert_ok!(Uniques::thaw(Origin::signed(3), 0, 42));
		assert_ok!(Uniques::transfer(Origin::signed(3), 0, 42, 3));
		assert_ok!(Uniques::burn(Origin::signed(3), 0, 42, None));
	});
}

#[test]
fn set_collection_metadata_should_work() {
	new_test_ext().execute_with(|| {
		// Cannot add metadata to unknown item
		assert_noop!(
			Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 20], false),
			Error::<Test>::UnknownCollection,
		);
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));
		// Cannot add metadata to unowned item
		assert_noop!(
			Uniques::set_collection_metadata(Origin::signed(2), 0, bvec![0u8; 20], false),
			Error::<Test>::NoPermission,
		);

		// Successfully add metadata and take deposit
		Balances::make_free_balance_be(&1, 30);
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 20], false));
		assert_eq!(Balances::free_balance(&1), 9);
		assert!(CollectionMetadataOf::<Test>::contains_key(0));

		// Force origin works, too.
		assert_ok!(Uniques::set_collection_metadata(Origin::root(), 0, bvec![0u8; 18], false));

		// Update deposit
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 15], false));
		assert_eq!(Balances::free_balance(&1), 14);
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 25], false));
		assert_eq!(Balances::free_balance(&1), 4);

		// Cannot over-reserve
		assert_noop!(
			Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 40], false),
			BalancesError::<Test, _>::InsufficientBalance,
		);

		// Can't set or clear metadata once frozen
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 15], true));
		assert_noop!(
			Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0u8; 15], false),
			Error::<Test, _>::Frozen,
		);
		assert_noop!(
			Uniques::clear_collection_metadata(Origin::signed(1), 0),
			Error::<Test>::Frozen
		);

		// Clear Metadata
		assert_ok!(Uniques::set_collection_metadata(Origin::root(), 0, bvec![0u8; 15], false));
		assert_noop!(
			Uniques::clear_collection_metadata(Origin::signed(2), 0),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Uniques::clear_collection_metadata(Origin::signed(1), 1),
			Error::<Test>::UnknownCollection
		);
		assert_ok!(Uniques::clear_collection_metadata(Origin::signed(1), 0));
		assert!(!CollectionMetadataOf::<Test>::contains_key(0));
	});
}

#[test]
fn set_item_metadata_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 30);

		// Cannot add metadata to unknown item
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		// Cannot add metadata to unowned item
		assert_noop!(
			Uniques::set_metadata(Origin::signed(2), 0, 42, bvec![0u8; 20], false),
			Error::<Test>::NoPermission,
		);

		// Successfully add metadata and take deposit
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 20], false));
		assert_eq!(Balances::free_balance(&1), 8);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 42));

		// Force origin works, too.
		assert_ok!(Uniques::set_metadata(Origin::root(), 0, 42, bvec![0u8; 18], false));

		// Update deposit
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 15], false));
		assert_eq!(Balances::free_balance(&1), 13);
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 25], false));
		assert_eq!(Balances::free_balance(&1), 3);

		// Cannot over-reserve
		assert_noop!(
			Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 40], false),
			BalancesError::<Test, _>::InsufficientBalance,
		);

		// Can't set or clear metadata once frozen
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 15], true));
		assert_noop!(
			Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0u8; 15], false),
			Error::<Test, _>::Frozen,
		);
		assert_noop!(Uniques::clear_metadata(Origin::signed(1), 0, 42), Error::<Test>::Frozen);

		// Clear Metadata
		assert_ok!(Uniques::set_metadata(Origin::root(), 0, 42, bvec![0u8; 15], false));
		assert_noop!(
			Uniques::clear_metadata(Origin::signed(2), 0, 42),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Uniques::clear_metadata(Origin::signed(1), 1, 42),
			Error::<Test>::UnknownCollection
		);
		assert_ok!(Uniques::clear_metadata(Origin::signed(1), 0, 42));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 42));
	});
}

#[test]
fn set_attribute_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);

		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));

		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, None, bvec![0], bvec![0]));
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(0), bvec![0], bvec![0]));
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(0), bvec![1], bvec![0]));
		assert_eq!(
			attributes(0),
			vec![
				(None, bvec![0], bvec![0]),
				(Some(0), bvec![0], bvec![0]),
				(Some(0), bvec![1], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(1), 9);

		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, None, bvec![0], bvec![0; 10]));
		assert_eq!(
			attributes(0),
			vec![
				(None, bvec![0], bvec![0; 10]),
				(Some(0), bvec![0], bvec![0]),
				(Some(0), bvec![1], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(1), 18);

		assert_ok!(Uniques::clear_attribute(Origin::signed(1), 0, Some(0), bvec![1]));
		assert_eq!(
			attributes(0),
			vec![(None, bvec![0], bvec![0; 10]), (Some(0), bvec![0], bvec![0]),]
		);
		assert_eq!(Balances::reserved_balance(1), 15);

		let w = Collection::<Test>::get(0).unwrap().destroy_witness();
		assert_ok!(Uniques::destroy(Origin::signed(1), 0, w));
		assert_eq!(attributes(0), vec![]);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn set_attribute_should_respect_freeze() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);

		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));

		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, None, bvec![0], bvec![0]));
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(0), bvec![0], bvec![0]));
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(1), bvec![0], bvec![0]));
		assert_eq!(
			attributes(0),
			vec![
				(None, bvec![0], bvec![0]),
				(Some(0), bvec![0], bvec![0]),
				(Some(1), bvec![0], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(1), 9);

		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![], true));
		let e = Error::<Test>::Frozen;
		assert_noop!(Uniques::set_attribute(Origin::signed(1), 0, None, bvec![0], bvec![0]), e);
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(0), bvec![0], bvec![1]));

		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 0, bvec![], true));
		let e = Error::<Test>::Frozen;
		assert_noop!(Uniques::set_attribute(Origin::signed(1), 0, Some(0), bvec![0], bvec![1]), e);
		assert_ok!(Uniques::set_attribute(Origin::signed(1), 0, Some(1), bvec![0], bvec![1]));
	});
}

#[test]
fn force_item_status_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);

		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 1));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 69, 2));
		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0; 20], false));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0; 20], false));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 69, bvec![0; 20], false));
		assert_eq!(Balances::reserved_balance(1), 65);

		// force item status to be free holding
		assert_ok!(Uniques::force_item_status(Origin::root(), 0, 1, 1, 1, 1, true, false));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 142, 1));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 169, 2));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 142, bvec![0; 20], false));
		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 169, bvec![0; 20], false));
		assert_eq!(Balances::reserved_balance(1), 65);

		assert_ok!(Uniques::redeposit(Origin::signed(1), 0, bvec![0, 42, 50, 69, 100]));
		assert_eq!(Balances::reserved_balance(1), 63);

		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 42, bvec![0; 20], false));
		assert_eq!(Balances::reserved_balance(1), 42);

		assert_ok!(Uniques::set_metadata(Origin::signed(1), 0, 69, bvec![0; 20], false));
		assert_eq!(Balances::reserved_balance(1), 21);

		assert_ok!(Uniques::set_collection_metadata(Origin::signed(1), 0, bvec![0; 20], false));
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn burn_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 100);
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, false));
		assert_ok!(Uniques::set_team(Origin::signed(1), 0, 2, 3, 4));

		assert_noop!(
			Uniques::burn(Origin::signed(5), 0, 42, Some(5)),
			Error::<Test>::UnknownCollection
		);

		assert_ok!(Uniques::mint(Origin::signed(2), 0, 42, 5));
		assert_ok!(Uniques::mint(Origin::signed(2), 0, 69, 5));
		assert_eq!(Balances::reserved_balance(1), 2);

		assert_noop!(Uniques::burn(Origin::signed(0), 0, 42, None), Error::<Test>::NoPermission);
		assert_noop!(Uniques::burn(Origin::signed(5), 0, 42, Some(6)), Error::<Test>::WrongOwner);

		assert_ok!(Uniques::burn(Origin::signed(5), 0, 42, Some(5)));
		assert_ok!(Uniques::burn(Origin::signed(3), 0, 69, Some(5)));
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn approval_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));
		assert_ok!(Uniques::approve_transfer(Origin::signed(2), 0, 42, 3));
		assert_ok!(Uniques::transfer(Origin::signed(3), 0, 42, 4));
		assert_noop!(Uniques::transfer(Origin::signed(3), 0, 42, 3), Error::<Test>::NoPermission);
		assert!(Item::<Test>::get(0, 42).unwrap().approved.is_none());

		assert_ok!(Uniques::approve_transfer(Origin::signed(4), 0, 42, 2));
		assert_ok!(Uniques::transfer(Origin::signed(2), 0, 42, 2));
	});
}

#[test]
fn cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));

		assert_ok!(Uniques::approve_transfer(Origin::signed(2), 0, 42, 3));
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(2), 1, 42, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(2), 0, 43, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(3), 0, 42, None),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(2), 0, 42, Some(4)),
			Error::<Test>::WrongDelegate
		);

		assert_ok!(Uniques::cancel_approval(Origin::signed(2), 0, 42, Some(3)));
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(2), 0, 42, None),
			Error::<Test>::NoDelegate
		);
	});
}

#[test]
fn cancel_approval_works_with_admin() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));

		assert_ok!(Uniques::approve_transfer(Origin::signed(2), 0, 42, 3));
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(1), 1, 42, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(1), 0, 43, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(1), 0, 42, Some(4)),
			Error::<Test>::WrongDelegate
		);

		assert_ok!(Uniques::cancel_approval(Origin::signed(1), 0, 42, Some(3)));
		assert_noop!(
			Uniques::cancel_approval(Origin::signed(1), 0, 42, None),
			Error::<Test>::NoDelegate
		);
	});
}

#[test]
fn cancel_approval_works_with_force() {
	new_test_ext().execute_with(|| {
		assert_ok!(Uniques::force_create(Origin::root(), 0, 1, true));
		assert_ok!(Uniques::mint(Origin::signed(1), 0, 42, 2));

		assert_ok!(Uniques::approve_transfer(Origin::signed(2), 0, 42, 3));
		assert_noop!(
			Uniques::cancel_approval(Origin::root(), 1, 42, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::root(), 0, 43, None),
			Error::<Test>::UnknownCollection
		);
		assert_noop!(
			Uniques::cancel_approval(Origin::root(), 0, 42, Some(4)),
			Error::<Test>::WrongDelegate
		);

		assert_ok!(Uniques::cancel_approval(Origin::root(), 0, 42, Some(3)));
		assert_noop!(
			Uniques::cancel_approval(Origin::root(), 0, 42, None),
			Error::<Test>::NoDelegate
		);
	});
}

#[test]
fn max_supply_should_work() {
	new_test_ext().execute_with(|| {
		let collection_id = 0;
		let user_id = 1;
		let max_supply = 2;

		// validate set_collection_max_supply
		assert_ok!(Uniques::force_create(Origin::root(), collection_id, user_id, true));
		assert!(!CollectionMaxSupply::<Test>::contains_key(collection_id));

		assert_ok!(Uniques::set_collection_max_supply(
			Origin::signed(user_id),
			collection_id,
			max_supply
		));
		assert_eq!(CollectionMaxSupply::<Test>::get(collection_id).unwrap(), max_supply);

		assert!(events().contains(&Event::<Test>::CollectionMaxSupplySet {
			collection: collection_id,
			max_supply,
		}));

		assert_noop!(
			Uniques::set_collection_max_supply(
				Origin::signed(user_id),
				collection_id,
				max_supply + 1
			),
			Error::<Test>::MaxSupplyAlreadySet
		);

		// validate we can't mint more to max supply
		assert_ok!(Uniques::mint(Origin::signed(user_id), collection_id, 0, user_id));
		assert_ok!(Uniques::mint(Origin::signed(user_id), collection_id, 1, user_id));
		assert_noop!(
			Uniques::mint(Origin::signed(user_id), collection_id, 2, user_id),
			Error::<Test>::MaxSupplyReached
		);

		// validate we remove the CollectionMaxSupply record when we destroy the collection
		assert_ok!(Uniques::destroy(
			Origin::signed(user_id),
			collection_id,
			Collection::<Test>::get(collection_id).unwrap().destroy_witness()
		));
		assert!(!CollectionMaxSupply::<Test>::contains_key(collection_id));
	});
}
