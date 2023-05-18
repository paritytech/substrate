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

//! Tests for Nfts pallet.

use crate::{mock::*, Event, *};
use enumflags2::BitFlags;
use frame_support::{
	assert_noop, assert_ok,
	dispatch::Dispatchable,
	traits::{
		tokens::nonfungibles_v2::{Destroy, Mutate},
		Currency, Get,
	},
};
use pallet_balances::Error as BalancesError;
use sp_core::{bounded::BoundedVec, Pair};
use sp_runtime::{traits::IdentifyAccount, MultiSignature, MultiSigner};
use sp_std::prelude::*;

type AccountIdOf<Test> = <Test as frame_system::Config>::AccountId;

fn account(id: u8) -> AccountIdOf<Test> {
	[id; 32].into()
}

fn items() -> Vec<(AccountIdOf<Test>, u32, u32)> {
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

fn collections() -> Vec<(AccountIdOf<Test>, u32)> {
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

fn attributes(
	collection: u32,
) -> Vec<(Option<u32>, AttributeNamespace<AccountIdOf<Test>>, Vec<u8>, Vec<u8>)> {
	let mut s: Vec<_> = Attribute::<Test>::iter_prefix((collection,))
		.map(|(k, v)| (k.0, k.1, k.2.into(), v.0.into()))
		.collect();
	s.sort_by_key(|k: &(Option<u32>, AttributeNamespace<AccountIdOf<Test>>, Vec<u8>, Vec<u8>)| k.0);
	s.sort_by_key(|k: &(Option<u32>, AttributeNamespace<AccountIdOf<Test>>, Vec<u8>, Vec<u8>)| {
		k.2.clone()
	});
	s
}

fn approvals(collection_id: u32, item_id: u32) -> Vec<(AccountIdOf<Test>, Option<u64>)> {
	let item = Item::<Test>::get(collection_id, item_id).unwrap();
	let s: Vec<_> = item.approvals.into_iter().collect();
	s
}

fn item_attributes_approvals(collection_id: u32, item_id: u32) -> Vec<AccountIdOf<Test>> {
	let approvals = ItemAttributesApprovalsOf::<Test>::get(collection_id, item_id);
	let s: Vec<_> = approvals.into_iter().collect();
	s
}

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let mock::RuntimeEvent::Nfts(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();

	System::reset_events();

	result
}

fn collection_config_from_disabled_settings(
	settings: BitFlags<CollectionSetting>,
) -> CollectionConfigFor<Test> {
	CollectionConfig {
		settings: CollectionSettings::from_disabled(settings),
		max_supply: None,
		mint_settings: MintSettings::default(),
	}
}

fn collection_config_with_all_settings_enabled() -> CollectionConfigFor<Test> {
	CollectionConfig {
		settings: CollectionSettings::all_enabled(),
		max_supply: None,
		mint_settings: MintSettings::default(),
	}
}

fn default_collection_config() -> CollectionConfigFor<Test> {
	collection_config_from_disabled_settings(CollectionSetting::DepositRequired.into())
}

fn default_item_config() -> ItemConfig {
	ItemConfig { settings: ItemSettings::all_enabled() }
}

fn item_config_from_disabled_settings(settings: BitFlags<ItemSetting>) -> ItemConfig {
	ItemConfig { settings: ItemSettings::from_disabled(settings) }
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
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_eq!(collections(), vec![(account(1), 0)]);
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		assert_eq!(items(), vec![(account(1), 0, 42)]);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(2),
			default_collection_config()
		));
		assert_eq!(collections(), vec![(account(1), 0), (account(2), 1)]);
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(2)), 1, 69, account(1), None));
		assert_eq!(items(), vec![(account(1), 0, 42), (account(1), 1, 69)]);
	});
}

#[test]
fn lifecycle_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		Balances::make_free_balance_be(&account(2), 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(account(1)),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_eq!(Balances::reserved_balance(&account(1)), 2);
		assert_eq!(collections(), vec![(account(1), 0)]);
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0, 0]
		));
		assert_eq!(Balances::reserved_balance(&account(1)), 5);
		assert!(CollectionMetadataOf::<Test>::contains_key(0));

		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(10),
			default_item_config()
		));
		assert_eq!(Balances::reserved_balance(&account(1)), 6);
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			69,
			account(20),
			default_item_config()
		));
		assert_eq!(Balances::reserved_balance(&account(1)), 7);
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 70, account(1), None));
		assert_eq!(items(), vec![(account(1), 0, 70), (account(10), 0, 42), (account(20), 0, 69)]);
		assert_eq!(Collection::<Test>::get(0).unwrap().items, 3);
		assert_eq!(Collection::<Test>::get(0).unwrap().item_metadatas, 0);
		assert_eq!(Collection::<Test>::get(0).unwrap().item_configs, 3);

		assert_eq!(Balances::reserved_balance(&account(1)), 8);
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(1)), 0, 70, account(2)));
		assert_eq!(Balances::reserved_balance(&account(1)), 8);
		assert_eq!(Balances::reserved_balance(&account(2)), 0);

		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![42, 42]));
		assert_eq!(Balances::reserved_balance(&account(1)), 11);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 42));
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 69, bvec![69, 69]));
		assert_eq!(Balances::reserved_balance(&account(1)), 14);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 69));
		assert!(ItemConfigOf::<Test>::contains_key(0, 69));
		let w = Nfts::get_destroy_witness(&0).unwrap();
		assert_eq!(w.item_metadatas, 2);
		assert_eq!(w.item_configs, 3);
		assert_noop!(
			Nfts::destroy(RuntimeOrigin::signed(account(1)), 0, w),
			Error::<Test>::CollectionNotEmpty
		);

		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(69),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(10)), 0, 42));
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(20)), 0, 69));
		assert_ok!(Nfts::burn(RuntimeOrigin::root(), 0, 70));

		let w = Nfts::get_destroy_witness(&0).unwrap();
		assert_eq!(w.attributes, 1);
		assert_eq!(w.item_metadatas, 0);
		assert_eq!(w.item_configs, 0);
		assert_ok!(Nfts::destroy(RuntimeOrigin::signed(account(1)), 0, w));
		assert_eq!(Balances::reserved_balance(&account(1)), 0);

		assert!(!Collection::<Test>::contains_key(0));
		assert!(!CollectionConfigOf::<Test>::contains_key(0));
		assert!(!Item::<Test>::contains_key(0, 42));
		assert!(!Item::<Test>::contains_key(0, 69));
		assert!(!CollectionMetadataOf::<Test>::contains_key(0));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 42));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 69));
		assert!(!ItemConfigOf::<Test>::contains_key(0, 69));
		assert_eq!(attributes(0), vec![]);
		assert_eq!(collections(), vec![]);
		assert_eq!(items(), vec![]);
	});
}

#[test]
fn destroy_with_bad_witness_should_not_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(account(1)),
			account(1),
			collection_config_with_all_settings_enabled()
		));

		let w = Collection::<Test>::get(0).unwrap().destroy_witness();
		assert_noop!(
			Nfts::destroy(
				RuntimeOrigin::signed(account(1)),
				0,
				DestroyWitness { item_configs: 1, ..w }
			),
			Error::<Test>::BadWitness
		);
	});
}

#[test]
fn destroy_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(account(1)),
			account(1),
			collection_config_with_all_settings_enabled()
		));

		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(2), None));
		assert_noop!(
			Nfts::destroy(
				RuntimeOrigin::signed(account(1)),
				0,
				Nfts::get_destroy_witness(&0).unwrap()
			),
			Error::<Test>::CollectionNotEmpty
		);
		assert_ok!(Nfts::lock_item_transfer(RuntimeOrigin::signed(account(1)), 0, 42));
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(2)), 0, 42));
		assert_eq!(Collection::<Test>::get(0).unwrap().item_configs, 1);
		assert_eq!(ItemConfigOf::<Test>::iter_prefix(0).count() as u32, 1);
		assert!(ItemConfigOf::<Test>::contains_key(0, 42));
		assert_ok!(Nfts::destroy(
			RuntimeOrigin::signed(account(1)),
			0,
			Nfts::get_destroy_witness(&0).unwrap()
		));
		assert!(!ItemConfigOf::<Test>::contains_key(0, 42));
		assert_eq!(ItemConfigOf::<Test>::iter_prefix(0).count() as u32, 0);
	});
}

#[test]
fn mint_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		assert_eq!(Nfts::owner(0, 42).unwrap(), account(1));
		assert_eq!(collections(), vec![(account(1), 0)]);
		assert_eq!(items(), vec![(account(1), 0, 42)]);

		// validate minting start and end settings
		assert_ok!(Nfts::update_mint_settings(
			RuntimeOrigin::signed(account(1)),
			0,
			MintSettings {
				start_block: Some(2),
				end_block: Some(3),
				mint_type: MintType::Public,
				..Default::default()
			}
		));

		System::set_block_number(1);
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(account(2)), 0, 43, account(1), None),
			Error::<Test>::MintNotStarted
		);
		System::set_block_number(4);
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(account(2)), 0, 43, account(1), None),
			Error::<Test>::MintEnded
		);

		// validate price
		assert_ok!(Nfts::update_mint_settings(
			RuntimeOrigin::signed(account(1)),
			0,
			MintSettings { mint_type: MintType::Public, price: Some(1), ..Default::default() }
		));
		Balances::make_free_balance_be(&account(2), 100);
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(2)), 0, 43, account(2), None));
		assert_eq!(Balances::total_balance(&account(2)), 99);

		// validate types
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::update_mint_settings(
			RuntimeOrigin::signed(account(1)),
			1,
			MintSettings { mint_type: MintType::HolderOf(0), ..Default::default() }
		));
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(account(3)), 1, 42, account(3), None),
			Error::<Test>::BadWitness
		);
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(account(2)), 1, 42, account(2), None),
			Error::<Test>::BadWitness
		);
		assert_noop!(
			Nfts::mint(
				RuntimeOrigin::signed(account(2)),
				1,
				42,
				account(2),
				Some(MintWitness { owned_item: 42 })
			),
			Error::<Test>::BadWitness
		);
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(account(2)),
			1,
			42,
			account(2),
			Some(MintWitness { owned_item: 43 })
		));

		// can't mint twice
		assert_noop!(
			Nfts::mint(
				RuntimeOrigin::signed(account(2)),
				1,
				46,
				account(2),
				Some(MintWitness { owned_item: 43 })
			),
			Error::<Test>::AlreadyClaimed
		);
	});
}

#[test]
fn transfer_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(2)), 0, 42, account(3)));
		assert_eq!(items(), vec![(account(3), 0, 42)]);
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(2)), 0, 42, account(4)),
			Error::<Test>::NoPermission
		);

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(3)),
			0,
			42,
			account(2),
			None
		));
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(2)), 0, 42, account(4)));

		// validate we can't transfer non-transferable items
		let collection_id = 1;
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_from_disabled_settings(
				CollectionSetting::TransferableItems | CollectionSetting::DepositRequired
			)
		));

		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			1,
			1,
			account(42),
			default_item_config()
		));

		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(1)), collection_id, 42, account(3)),
			Error::<Test>::ItemsNonTransferable
		);
	});
}

#[test]
fn locking_transfer_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		assert_ok!(Nfts::lock_item_transfer(RuntimeOrigin::signed(account(1)), 0, 42));
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(1)), 0, 42, account(2)),
			Error::<Test>::ItemLocked
		);

		assert_ok!(Nfts::unlock_item_transfer(RuntimeOrigin::signed(account(1)), 0, 42));
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(account(1)),
			0,
			CollectionSettings::from_disabled(CollectionSetting::TransferableItems.into())
		));
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(1)), 0, 42, account(2)),
			Error::<Test>::ItemsNonTransferable
		);

		assert_ok!(Nfts::force_collection_config(
			RuntimeOrigin::root(),
			0,
			collection_config_with_all_settings_enabled(),
		));
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(1)), 0, 42, account(2)));
	});
}

#[test]
fn origin_guards_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));

		Balances::make_free_balance_be(&account(2), 100);
		assert_ok!(Nfts::set_accept_ownership(RuntimeOrigin::signed(account(2)), Some(0)));
		assert_noop!(
			Nfts::transfer_ownership(RuntimeOrigin::signed(account(2)), 0, account(2)),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::set_team(
				RuntimeOrigin::signed(account(2)),
				0,
				Some(account(2)),
				Some(account(2)),
				Some(account(2)),
			),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::lock_item_transfer(RuntimeOrigin::signed(account(2)), 0, 42),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::unlock_item_transfer(RuntimeOrigin::signed(account(2)), 0, 42),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(account(2)), 0, 69, account(2), None),
			Error::<Test>::NoPermission
		);
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 43, account(2), None));
		assert_noop!(
			Nfts::burn(RuntimeOrigin::signed(account(1)), 0, 43),
			Error::<Test>::NoPermission
		);
		let w = Nfts::get_destroy_witness(&0).unwrap();
		assert_noop!(
			Nfts::destroy(RuntimeOrigin::signed(account(2)), 0, w),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn transfer_owner_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		Balances::make_free_balance_be(&account(2), 100);
		Balances::make_free_balance_be(&account(3), 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(account(1)),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_eq!(collections(), vec![(account(1), 0)]);
		assert_noop!(
			Nfts::transfer_ownership(RuntimeOrigin::signed(account(1)), 0, account(2)),
			Error::<Test>::Unaccepted
		);
		assert_ok!(Nfts::set_accept_ownership(RuntimeOrigin::signed(account(2)), Some(0)));
		assert_ok!(Nfts::transfer_ownership(RuntimeOrigin::signed(account(1)), 0, account(2)));

		assert_eq!(collections(), vec![(account(2), 0)]);
		assert_eq!(Balances::total_balance(&account(1)), 98);
		assert_eq!(Balances::total_balance(&account(2)), 102);
		assert_eq!(Balances::reserved_balance(&account(1)), 0);
		assert_eq!(Balances::reserved_balance(&account(2)), 2);

		assert_ok!(Nfts::set_accept_ownership(RuntimeOrigin::signed(account(1)), Some(0)));
		assert_noop!(
			Nfts::transfer_ownership(RuntimeOrigin::signed(account(1)), 0, account(1)),
			Error::<Test>::NoPermission
		);

		// Mint and set metadata now and make sure that deposit gets transferred back.
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0u8; 20],
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		assert_eq!(Balances::reserved_balance(&account(1)), 1);
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 20]));
		assert_ok!(Nfts::set_accept_ownership(RuntimeOrigin::signed(account(3)), Some(0)));
		assert_ok!(Nfts::transfer_ownership(RuntimeOrigin::signed(account(2)), 0, account(3)));
		assert_eq!(collections(), vec![(account(3), 0)]);
		assert_eq!(Balances::total_balance(&account(2)), 58);
		assert_eq!(Balances::total_balance(&account(3)), 144);
		assert_eq!(Balances::reserved_balance(&account(2)), 0);
		assert_eq!(Balances::reserved_balance(&account(3)), 44);

		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(1)), 0, 42, account(2)));
		// reserved_balance of accounts 1 & 2 should be unchanged:
		assert_eq!(Balances::reserved_balance(&account(1)), 1);
		assert_eq!(Balances::reserved_balance(&account(2)), 0);

		// 2's acceptance from before is reset when it became an owner, so it cannot be transferred
		// without a fresh acceptance.
		assert_noop!(
			Nfts::transfer_ownership(RuntimeOrigin::signed(account(3)), 0, account(2)),
			Error::<Test>::Unaccepted
		);
	});
}

#[test]
fn set_team_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config(),
		));
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(account(2)),
			Some(account(3)),
			Some(account(4)),
		));

		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(2)), 0, 42, account(2), None));

		// admin can't transfer/burn items he doesn't own
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(3)),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::burn(RuntimeOrigin::signed(account(3)), 0, 42),
			Error::<Test>::NoPermission
		);

		assert_ok!(Nfts::lock_item_transfer(RuntimeOrigin::signed(account(4)), 0, 42));
		assert_ok!(Nfts::unlock_item_transfer(RuntimeOrigin::signed(account(4)), 0, 42));

		// validate we can set any role to None
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(account(2)),
			Some(account(3)),
			None,
		));
		assert_noop!(
			Nfts::lock_item_transfer(RuntimeOrigin::signed(account(4)), 0, 42),
			Error::<Test>::NoPermission
		);

		// set all the roles to None
		assert_ok!(Nfts::set_team(RuntimeOrigin::signed(account(1)), 0, None, None, None,));

		// validate we can't set the roles back
		assert_noop!(
			Nfts::set_team(
				RuntimeOrigin::signed(account(1)),
				0,
				Some(account(2)),
				Some(account(3)),
				None,
			),
			Error::<Test>::NoPermission
		);

		// only the root account can change the roles from None to Some()
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::root(),
			0,
			Some(account(2)),
			Some(account(3)),
			None,
		));
	});
}

#[test]
fn set_collection_metadata_should_work() {
	new_test_ext().execute_with(|| {
		// Cannot add metadata to unknown item
		assert_noop!(
			Nfts::set_collection_metadata(RuntimeOrigin::signed(account(1)), 0, bvec![0u8; 20]),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		// Cannot add metadata to unowned item
		assert_noop!(
			Nfts::set_collection_metadata(RuntimeOrigin::signed(account(2)), 0, bvec![0u8; 20]),
			Error::<Test>::NoPermission,
		);

		// Successfully add metadata and take deposit
		Balances::make_free_balance_be(&account(1), 30);
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0u8; 20]
		));
		assert_eq!(Balances::free_balance(&account(1)), 9);
		assert!(CollectionMetadataOf::<Test>::contains_key(0));

		// Force origin works, too.
		assert_ok!(Nfts::set_collection_metadata(RuntimeOrigin::root(), 0, bvec![0u8; 18]));

		// Update deposit
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0u8; 15]
		));
		assert_eq!(Balances::free_balance(&account(1)), 14);
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0u8; 25]
		));
		assert_eq!(Balances::free_balance(&account(1)), 4);

		// Cannot over-reserve
		assert_noop!(
			Nfts::set_collection_metadata(RuntimeOrigin::signed(account(1)), 0, bvec![0u8; 40]),
			BalancesError::<Test, _>::InsufficientBalance,
		);

		// Can't set or clear metadata once frozen
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0u8; 15]
		));
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(account(1)),
			0,
			CollectionSettings::from_disabled(CollectionSetting::UnlockedMetadata.into())
		));
		assert_noop!(
			Nfts::set_collection_metadata(RuntimeOrigin::signed(account(1)), 0, bvec![0u8; 15]),
			Error::<Test, _>::LockedCollectionMetadata,
		);
		assert_noop!(
			Nfts::clear_collection_metadata(RuntimeOrigin::signed(account(1)), 0),
			Error::<Test>::LockedCollectionMetadata
		);

		// Clear Metadata
		assert_ok!(Nfts::set_collection_metadata(RuntimeOrigin::root(), 0, bvec![0u8; 15]));
		assert_noop!(
			Nfts::clear_collection_metadata(RuntimeOrigin::signed(account(2)), 0),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::clear_collection_metadata(RuntimeOrigin::signed(account(1)), 1),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::clear_collection_metadata(RuntimeOrigin::signed(account(1)), 0),
			Error::<Test>::LockedCollectionMetadata
		);
		assert_ok!(Nfts::clear_collection_metadata(RuntimeOrigin::root(), 0));
		assert!(!CollectionMetadataOf::<Test>::contains_key(0));
	});
}

#[test]
fn set_item_metadata_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 30);

		// Cannot add metadata to unknown item
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		// Cannot add metadata to unowned item
		assert_noop!(
			Nfts::set_metadata(RuntimeOrigin::signed(account(2)), 0, 42, bvec![0u8; 20]),
			Error::<Test>::NoPermission,
		);

		// Successfully add metadata and take deposit
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 20]));
		assert_eq!(Balances::free_balance(&account(1)), 8);
		assert!(ItemMetadataOf::<Test>::contains_key(0, 42));

		// Force origin works, too.
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::root(), 0, 42, bvec![0u8; 18]));

		// Update deposit
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 15]));
		assert_eq!(Balances::free_balance(&account(1)), 13);
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 25]));
		assert_eq!(Balances::free_balance(&account(1)), 3);

		// Cannot over-reserve
		assert_noop!(
			Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 40]),
			BalancesError::<Test, _>::InsufficientBalance,
		);

		// Can't set or clear metadata once frozen
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 15]));
		assert_ok!(Nfts::lock_item_properties(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			true,
			false
		));
		assert_noop!(
			Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0u8; 15]),
			Error::<Test, _>::LockedItemMetadata,
		);
		assert_noop!(
			Nfts::clear_metadata(RuntimeOrigin::signed(account(1)), 0, 42),
			Error::<Test>::LockedItemMetadata,
		);

		// Clear Metadata
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::root(), 0, 42, bvec![0u8; 15]));
		assert_noop!(
			Nfts::clear_metadata(RuntimeOrigin::signed(account(2)), 0, 42),
			Error::<Test>::NoPermission,
		);
		assert_noop!(
			Nfts::clear_metadata(RuntimeOrigin::signed(account(1)), 1, 42),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Nfts::clear_metadata(RuntimeOrigin::root(), 0, 42));
		assert!(!ItemMetadataOf::<Test>::contains_key(0, 42));
	});
}

#[test]
fn set_collection_owner_attributes_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 0, account(1), None));

		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			None,
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![1],
			bvec![0],
		));
		assert_eq!(
			attributes(0),
			vec![
				(None, AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![1], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(1)), 10);
		assert_eq!(Collection::<Test>::get(0).unwrap().owner_deposit, 9);

		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			None,
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0; 10],
		));
		assert_eq!(
			attributes(0),
			vec![
				(None, AttributeNamespace::CollectionOwner, bvec![0], bvec![0; 10]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![1], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(1)), 19);
		assert_eq!(Collection::<Test>::get(0).unwrap().owner_deposit, 18);

		assert_ok!(Nfts::clear_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![1],
		));
		assert_eq!(
			attributes(0),
			vec![
				(None, AttributeNamespace::CollectionOwner, bvec![0], bvec![0; 10]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(1)), 16);

		assert_ok!(Nfts::burn(RuntimeOrigin::root(), 0, 0));
		let w = Nfts::get_destroy_witness(&0).unwrap();
		assert_ok!(Nfts::destroy(RuntimeOrigin::signed(account(1)), 0, w));
		assert_eq!(attributes(0), vec![]);
		assert_eq!(Balances::reserved_balance(account(1)), 0);
	});
}

#[test]
fn set_item_owner_attributes_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		Balances::make_free_balance_be(&account(2), 100);
		Balances::make_free_balance_be(&account(3), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			account(2),
			default_item_config()
		));

		// can't set for the collection
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(2)),
				0,
				None,
				AttributeNamespace::ItemOwner,
				bvec![0],
				bvec![0],
			),
			Error::<Test>::NoPermission,
		);
		// can't set for the non-owned item
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(1)),
				0,
				Some(0),
				AttributeNamespace::ItemOwner,
				bvec![0],
				bvec![0],
			),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![1],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![2],
			bvec![0],
		));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::ItemOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![1], bvec![0]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![2], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(2)), 9);

		// validate an attribute can be updated
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![0],
			bvec![0; 10],
		));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::ItemOwner, bvec![0], bvec![0; 10]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![1], bvec![0]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![2], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(2)), 18);

		// validate only item's owner (or the root) can remove an attribute
		assert_noop!(
			Nfts::clear_attribute(
				RuntimeOrigin::signed(account(1)),
				0,
				Some(0),
				AttributeNamespace::ItemOwner,
				bvec![1],
			),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Nfts::clear_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![1],
		));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::ItemOwner, bvec![0], bvec![0; 10]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![2], bvec![0])
			]
		);
		assert_eq!(Balances::reserved_balance(account(2)), 15);

		// transfer item
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(2)), 0, 0, account(3)));

		// validate the attribute are still here & the deposit belongs to the previous owner
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::ItemOwner, bvec![0], bvec![0; 10]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![2], bvec![0])
			]
		);
		let key: BoundedVec<_, _> = bvec![0];
		let (_, deposit) =
			Attribute::<Test>::get((0, Some(0), AttributeNamespace::ItemOwner, &key)).unwrap();
		assert_eq!(deposit.account, Some(account(2)));
		assert_eq!(deposit.amount, 12);

		// on attribute update the deposit should be returned to the previous owner
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(3)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![0],
			bvec![0; 11],
		));
		let (_, deposit) =
			Attribute::<Test>::get((0, Some(0), AttributeNamespace::ItemOwner, &key)).unwrap();
		assert_eq!(deposit.account, Some(account(3)));
		assert_eq!(deposit.amount, 13);
		assert_eq!(Balances::reserved_balance(account(2)), 3);
		assert_eq!(Balances::reserved_balance(account(3)), 13);

		// validate attributes on item deletion
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(3)), 0, 0));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::ItemOwner, bvec![0], bvec![0; 11]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![2], bvec![0])
			]
		);
		assert_ok!(Nfts::clear_attribute(
			RuntimeOrigin::signed(account(3)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![0],
		));
		assert_ok!(Nfts::clear_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![2],
		));
		assert_eq!(Balances::reserved_balance(account(2)), 0);
		assert_eq!(Balances::reserved_balance(account(3)), 0);
	});
}

#[test]
fn set_external_account_attributes_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		Balances::make_free_balance_be(&account(2), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			account(1),
			default_item_config()
		));
		assert_ok!(Nfts::approve_item_attributes(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			account(2)
		));

		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(2)),
				0,
				Some(0),
				AttributeNamespace::Account(account(1)),
				bvec![0],
				bvec![0],
			),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::Account(account(2)),
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::Account(account(2)),
			bvec![1],
			bvec![0],
		));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::Account(account(2)), bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::Account(account(2)), bvec![1], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(2)), 6);

		// remove permission to set attributes
		assert_ok!(Nfts::cancel_item_attributes_approval(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			account(2),
			CancelAttributesApprovalWitness { account_attributes: 2 },
		));
		assert_eq!(attributes(0), vec![]);
		assert_eq!(Balances::reserved_balance(account(2)), 0);
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(2)),
				0,
				Some(0),
				AttributeNamespace::Account(account(2)),
				bvec![0],
				bvec![0],
			),
			Error::<Test>::NoPermission,
		);
	});
}

#[test]
fn validate_deposit_required_setting() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		Balances::make_free_balance_be(&account(2), 100);
		Balances::make_free_balance_be(&account(3), 100);

		// with the disabled DepositRequired setting, only the collection's owner can set the
		// attributes for free.
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			account(2),
			default_item_config()
		));
		assert_ok!(Nfts::approve_item_attributes(
			RuntimeOrigin::signed(account(2)),
			0,
			0,
			account(3)
		));

		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(2)),
			0,
			Some(0),
			AttributeNamespace::ItemOwner,
			bvec![1],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(3)),
			0,
			Some(0),
			AttributeNamespace::Account(account(3)),
			bvec![2],
			bvec![0],
		));
		assert_ok!(<Nfts as Mutate<<Test as SystemConfig>::AccountId, ItemConfig>>::set_attribute(
			&0,
			&0,
			&[3],
			&[0],
		));
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![1], bvec![0]),
				(Some(0), AttributeNamespace::Account(account(3)), bvec![2], bvec![0]),
				(Some(0), AttributeNamespace::Pallet, bvec![3], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(1)), 0);
		assert_eq!(Balances::reserved_balance(account(2)), 3);
		assert_eq!(Balances::reserved_balance(account(3)), 3);

		assert_ok!(
			<Nfts as Mutate<<Test as SystemConfig>::AccountId, ItemConfig>>::clear_attribute(
				&0,
				&0,
				&[3],
			)
		);
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::ItemOwner, bvec![1], bvec![0]),
				(Some(0), AttributeNamespace::Account(account(3)), bvec![2], bvec![0]),
			]
		);
	});
}

#[test]
fn set_attribute_should_respect_lock() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled(),
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 0, account(1), None));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 1, account(1), None));

		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			None,
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(1),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![0],
		));
		assert_eq!(
			attributes(0),
			vec![
				(None, AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
				(Some(1), AttributeNamespace::CollectionOwner, bvec![0], bvec![0]),
			]
		);
		assert_eq!(Balances::reserved_balance(account(1)), 11);

		assert_ok!(Nfts::set_collection_metadata(RuntimeOrigin::signed(account(1)), 0, bvec![]));
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(account(1)),
			0,
			CollectionSettings::from_disabled(CollectionSetting::UnlockedAttributes.into())
		));

		let e = Error::<Test>::LockedCollectionAttributes;
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(1)),
				0,
				None,
				AttributeNamespace::CollectionOwner,
				bvec![0],
				bvec![0],
			),
			e
		);
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![1],
		));

		assert_ok!(Nfts::lock_item_properties(
			RuntimeOrigin::signed(account(1)),
			0,
			0,
			false,
			true
		));
		let e = Error::<Test>::LockedItemAttributes;
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(account(1)),
				0,
				Some(0),
				AttributeNamespace::CollectionOwner,
				bvec![0],
				bvec![1],
			),
			e
		);
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(1),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![1],
		));
	});
}

#[test]
fn preserve_config_for_frozen_items() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 0, account(1), None));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 1, account(1), None));

		// if the item is not locked/frozen then the config gets deleted on item burn
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(1)), 0, 1));
		assert!(!ItemConfigOf::<Test>::contains_key(0, 1));

		// lock the item and ensure the config stays unchanged
		assert_ok!(Nfts::lock_item_properties(RuntimeOrigin::signed(account(1)), 0, 0, true, true));

		let expect_config = item_config_from_disabled_settings(
			ItemSetting::UnlockedAttributes | ItemSetting::UnlockedMetadata,
		);
		let config = ItemConfigOf::<Test>::get(0, 0).unwrap();
		assert_eq!(config, expect_config);

		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(1)), 0, 0));
		let config = ItemConfigOf::<Test>::get(0, 0).unwrap();
		assert_eq!(config, expect_config);

		// can't mint with the different config
		assert_noop!(
			Nfts::force_mint(
				RuntimeOrigin::signed(account(1)),
				0,
				0,
				account(2),
				default_item_config()
			),
			Error::<Test>::InconsistentItemConfig
		);

		assert_ok!(Nfts::update_mint_settings(
			RuntimeOrigin::signed(account(1)),
			0,
			MintSettings {
				default_item_settings: ItemSettings::from_disabled(
					ItemSetting::UnlockedAttributes | ItemSetting::UnlockedMetadata
				),
				..Default::default()
			}
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 0, account(1), None));
	});
}

#[test]
fn force_update_collection_should_work() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			69,
			account(2),
			default_item_config(),
		));
		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(1)),
			0,
			bvec![0; 20]
		));
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 42, bvec![0; 20]));
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 69, bvec![0; 20]));
		assert_eq!(Balances::reserved_balance(account(1)), 65);

		// force item status to be free holding
		assert_ok!(Nfts::force_collection_config(
			RuntimeOrigin::root(),
			0,
			collection_config_from_disabled_settings(CollectionSetting::DepositRequired.into()),
		));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 142, account(1), None));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			169,
			account(2),
			default_item_config(),
		));
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 142, bvec![0; 20]));
		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(1)), 0, 169, bvec![0; 20]));

		Balances::make_free_balance_be(&account(5), 100);
		assert_ok!(Nfts::force_collection_owner(RuntimeOrigin::root(), 0, account(5)));
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::root(),
			0,
			Some(account(2)),
			Some(account(5)),
			Some(account(4)),
		));
		assert_eq!(collections(), vec![(account(5), 0)]);
		assert_eq!(Balances::reserved_balance(account(1)), 2);
		assert_eq!(Balances::reserved_balance(account(5)), 63);

		assert_ok!(Nfts::redeposit(
			RuntimeOrigin::signed(account(5)),
			0,
			bvec![0, 42, 50, 69, 100]
		));
		assert_eq!(Balances::reserved_balance(account(1)), 0);

		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(5)), 0, 42, bvec![0; 20]));
		assert_eq!(Balances::reserved_balance(account(5)), 42);

		assert_ok!(Nfts::set_metadata(RuntimeOrigin::signed(account(5)), 0, 69, bvec![0; 20]));
		assert_eq!(Balances::reserved_balance(account(5)), 21);

		assert_ok!(Nfts::set_collection_metadata(
			RuntimeOrigin::signed(account(5)),
			0,
			bvec![0; 20]
		));
		assert_eq!(Balances::reserved_balance(account(5)), 0);

		// validate new roles
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::root(),
			0,
			Some(account(2)),
			Some(account(3)),
			Some(account(4)),
		));
		assert_eq!(
			CollectionRoleOf::<Test>::get(0, account(2)).unwrap(),
			CollectionRoles(CollectionRole::Issuer.into())
		);
		assert_eq!(
			CollectionRoleOf::<Test>::get(0, account(3)).unwrap(),
			CollectionRoles(CollectionRole::Admin.into())
		);
		assert_eq!(
			CollectionRoleOf::<Test>::get(0, account(4)).unwrap(),
			CollectionRoles(CollectionRole::Freezer.into())
		);

		assert_ok!(Nfts::set_team(
			RuntimeOrigin::root(),
			0,
			Some(account(3)),
			Some(account(2)),
			Some(account(3)),
		));

		assert_eq!(
			CollectionRoleOf::<Test>::get(0, account(2)).unwrap(),
			CollectionRoles(CollectionRole::Admin.into())
		);
		assert_eq!(
			CollectionRoleOf::<Test>::get(0, account(3)).unwrap(),
			CollectionRoles(CollectionRole::Issuer | CollectionRole::Freezer)
		);
	});
}

#[test]
fn burn_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&account(1), 100);
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_with_all_settings_enabled()
		));
		assert_ok!(Nfts::set_team(
			RuntimeOrigin::signed(account(1)),
			0,
			Some(account(2)),
			Some(account(3)),
			Some(account(4)),
		));

		assert_noop!(
			Nfts::burn(RuntimeOrigin::signed(account(5)), 0, 42),
			Error::<Test>::UnknownItem
		);

		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(5),
			default_item_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(2)),
			0,
			69,
			account(5),
			default_item_config()
		));
		assert_eq!(Balances::reserved_balance(account(1)), 2);

		assert_noop!(
			Nfts::burn(RuntimeOrigin::signed(account(0)), 0, 42),
			Error::<Test>::NoPermission
		);

		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(5)), 0, 42));
		assert_ok!(Nfts::burn(RuntimeOrigin::signed(account(5)), 0, 69));
		assert_eq!(Balances::reserved_balance(account(1)), 0);
	});
}

#[test]
fn approval_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(4)));
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(3)),
			Error::<Test>::NoPermission
		);
		assert!(Item::<Test>::get(0, 42).unwrap().approvals.is_empty());

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(4)),
			0,
			42,
			account(2),
			None
		));
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(2)), 0, 42, account(2)));

		// ensure we can't buy an item when the collection has a NonTransferableItems flag
		let collection_id = 1;
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_from_disabled_settings(
				CollectionSetting::TransferableItems | CollectionSetting::DepositRequired
			)
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(account(1)),
			1,
			collection_id,
			account(1),
			None,
		));

		assert_noop!(
			Nfts::approve_transfer(
				RuntimeOrigin::signed(account(1)),
				collection_id,
				1,
				account(2),
				None
			),
			Error::<Test>::ItemsNonTransferable
		);
	});
}

#[test]
fn cancel_approval_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 1, 42, account(3)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 43, account(3)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(3)), 0, 42, account(3)),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(4)),
			Error::<Test>::NotDelegate
		);

		assert_ok!(Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(3)));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(3)),
			Error::<Test>::NotDelegate
		);

		let current_block = 1;
		System::set_block_number(current_block);
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			69,
			account(2),
			default_item_config()
		));
		// approval expires after 2 blocks.
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			Some(2)
		));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(5)), 0, 42, account(3)),
			Error::<Test>::NoPermission
		);

		System::set_block_number(current_block + 3);
		// 5 can cancel the approval since the deadline has passed.
		assert_ok!(Nfts::cancel_approval(RuntimeOrigin::signed(account(5)), 0, 42, account(3)));
		assert_eq!(approvals(0, 69), vec![]);
	});
}

#[test]
fn approving_multiple_accounts_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		let current_block = 1;
		System::set_block_number(current_block);
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(4),
			None
		));
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(5),
			Some(2)
		));
		assert_eq!(
			approvals(0, 42),
			vec![(account(3), None), (account(4), None), (account(5), Some(current_block + 2))]
		);

		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(4)), 0, 42, account(6)));
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(7)),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(5)), 0, 42, account(8)),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn approvals_limit_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		for i in 3..13 {
			assert_ok!(Nfts::approve_transfer(
				RuntimeOrigin::signed(account(2)),
				0,
				42,
				account(i),
				None
			));
		}
		// the limit is 10
		assert_noop!(
			Nfts::approve_transfer(RuntimeOrigin::signed(account(2)), 0, 42, account(14), None),
			Error::<Test>::ReachedApprovalLimit
		);
	});
}

#[test]
fn approval_deadline_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert!(System::block_number().is_zero());

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			collection_config_from_disabled_settings(CollectionSetting::DepositRequired.into())
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		// the approval expires after the 2nd block.
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			Some(2)
		));

		System::set_block_number(3);
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(4)),
			Error::<Test>::ApprovalExpired
		);
		System::set_block_number(1);
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(4)));

		assert_eq!(System::block_number(), 1);
		// make a new approval with a deadline after 4 blocks, so it will expire after the 5th
		// block.
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(4)),
			0,
			42,
			account(6),
			Some(4)
		));
		// this should still work.
		System::set_block_number(5);
		assert_ok!(Nfts::transfer(RuntimeOrigin::signed(account(6)), 0, 42, account(5)));
	});
}

#[test]
fn cancel_approval_works_with_admin() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 1, 42, account(1)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 43, account(1)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(4)),
			Error::<Test>::NotDelegate
		);

		assert_ok!(Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(3)));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::signed(account(2)), 0, 42, account(1)),
			Error::<Test>::NotDelegate
		);
	});
}

#[test]
fn cancel_approval_works_with_force() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::root(), 1, 42, account(1)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::root(), 0, 43, account(1)),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::root(), 0, 42, account(4)),
			Error::<Test>::NotDelegate
		);

		assert_ok!(Nfts::cancel_approval(RuntimeOrigin::root(), 0, 42, account(3)));
		assert_noop!(
			Nfts::cancel_approval(RuntimeOrigin::root(), 0, 42, account(1)),
			Error::<Test>::NotDelegate
		);
	});
}

#[test]
fn clear_all_transfer_approvals_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2),
			default_item_config()
		));

		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(3),
			None
		));
		assert_ok!(Nfts::approve_transfer(
			RuntimeOrigin::signed(account(2)),
			0,
			42,
			account(4),
			None
		));

		assert_noop!(
			Nfts::clear_all_transfer_approvals(RuntimeOrigin::signed(account(3)), 0, 42),
			Error::<Test>::NoPermission
		);

		assert_ok!(Nfts::clear_all_transfer_approvals(RuntimeOrigin::signed(account(2)), 0, 42));

		assert!(events().contains(&Event::<Test>::AllApprovalsCancelled {
			collection: 0,
			item: 42,
			owner: account(2),
		}));
		assert_eq!(approvals(0, 42), vec![]);

		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(3)), 0, 42, account(5)),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(account(4)), 0, 42, account(5)),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn max_supply_should_work() {
	new_test_ext().execute_with(|| {
		let collection_id = 0;
		let user_id = account(1);
		let max_supply = 1;

		// validate set_collection_max_supply
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			default_collection_config()
		));
		assert_eq!(CollectionConfigOf::<Test>::get(collection_id).unwrap().max_supply, None);

		assert_ok!(Nfts::set_collection_max_supply(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			max_supply
		));
		assert_eq!(
			CollectionConfigOf::<Test>::get(collection_id).unwrap().max_supply,
			Some(max_supply)
		);

		assert!(events().contains(&Event::<Test>::CollectionMaxSupplySet {
			collection: collection_id,
			max_supply,
		}));

		assert_ok!(Nfts::set_collection_max_supply(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			max_supply + 1
		));
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			CollectionSettings::from_disabled(CollectionSetting::UnlockedMaxSupply.into())
		));
		assert_noop!(
			Nfts::set_collection_max_supply(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				max_supply + 2
			),
			Error::<Test>::MaxSupplyLocked
		);

		// validate we can't mint more to max supply
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			0,
			user_id.clone(),
			None
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			1,
			user_id.clone(),
			None
		));
		assert_noop!(
			Nfts::mint(RuntimeOrigin::signed(user_id.clone()), collection_id, 2, user_id, None),
			Error::<Test>::MaxSupplyReached
		);
	});
}

#[test]
fn mint_settings_should_work() {
	new_test_ext().execute_with(|| {
		let collection_id = 0;
		let user_id = account(1);
		let item_id = 0;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			default_collection_config()
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_id,
			user_id.clone(),
			None,
		));
		assert_eq!(
			ItemConfigOf::<Test>::get(collection_id, item_id)
				.unwrap()
				.settings
				.get_disabled(),
			ItemSettings::all_enabled().get_disabled()
		);

		let collection_id = 1;
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			CollectionConfig {
				mint_settings: MintSettings {
					default_item_settings: ItemSettings::from_disabled(
						ItemSetting::Transferable | ItemSetting::UnlockedMetadata
					),
					..Default::default()
				},
				..default_collection_config()
			}
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_id,
			user_id.clone(),
			None,
		));
		assert_eq!(
			ItemConfigOf::<Test>::get(collection_id, item_id)
				.unwrap()
				.settings
				.get_disabled(),
			ItemSettings::from_disabled(ItemSetting::Transferable | ItemSetting::UnlockedMetadata)
				.get_disabled()
		);
	});
}

#[test]
fn set_price_should_work() {
	new_test_ext().execute_with(|| {
		let user_id = account(1);
		let collection_id = 0;
		let item_1 = 1;
		let item_2 = 2;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			default_collection_config()
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			user_id.clone(),
			None,
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_2,
			user_id.clone(),
			None,
		));

		assert_ok!(Nfts::set_price(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			Some(1),
			None,
		));

		assert_ok!(Nfts::set_price(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_2,
			Some(2),
			Some(account(3)),
		));

		let item = ItemPriceOf::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(item.0, 1);
		assert_eq!(item.1, None);

		let item = ItemPriceOf::<Test>::get(collection_id, item_2).unwrap();
		assert_eq!(item.0, 2);
		assert_eq!(item.1, Some(account(3)));

		assert!(events().contains(&Event::<Test>::ItemPriceSet {
			collection: collection_id,
			item: item_1,
			price: 1,
			whitelisted_buyer: None,
		}));

		// validate we can unset the price
		assert_ok!(Nfts::set_price(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_2,
			None,
			None
		));
		assert!(events().contains(&Event::<Test>::ItemPriceRemoved {
			collection: collection_id,
			item: item_2
		}));
		assert!(!ItemPriceOf::<Test>::contains_key(collection_id, item_2));

		// ensure we can't set price when the items are non-transferable
		let collection_id = 1;
		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			collection_config_from_disabled_settings(
				CollectionSetting::TransferableItems | CollectionSetting::DepositRequired
			)
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			user_id.clone(),
			None,
		));

		assert_noop!(
			Nfts::set_price(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_1,
				Some(2),
				None
			),
			Error::<Test>::ItemsNonTransferable
		);
	});
}

#[test]
fn buy_item_should_work() {
	new_test_ext().execute_with(|| {
		let user_1 = account(1);
		let user_2 = account(2);
		let user_3 = account(3);
		let collection_id = 0;
		let item_1 = 1;
		let item_2 = 2;
		let item_3 = 3;
		let price_1 = 20;
		let price_2 = 30;
		let initial_balance = 100;

		Balances::make_free_balance_be(&user_1, initial_balance);
		Balances::make_free_balance_be(&user_2, initial_balance);
		Balances::make_free_balance_be(&user_3, initial_balance);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_1.clone(),
			default_collection_config()
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_1,
			user_1.clone(),
			None
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_2,
			user_1.clone(),
			None
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_3,
			user_1.clone(),
			None
		));

		assert_ok!(Nfts::set_price(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_1,
			Some(price_1),
			None,
		));

		assert_ok!(Nfts::set_price(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_2,
			Some(price_2),
			Some(user_3.clone()),
		));

		// can't buy for less
		assert_noop!(
			Nfts::buy_item(RuntimeOrigin::signed(user_2.clone()), collection_id, item_1, 1),
			Error::<Test>::BidTooLow
		);

		// pass the higher price to validate it will still deduct correctly
		assert_ok!(Nfts::buy_item(
			RuntimeOrigin::signed(user_2.clone()),
			collection_id,
			item_1,
			price_1 + 1,
		));

		// validate the new owner & balances
		let item = Item::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(item.owner, user_2.clone());
		assert_eq!(Balances::total_balance(&user_1.clone()), initial_balance + price_1);
		assert_eq!(Balances::total_balance(&user_2.clone()), initial_balance - price_1);

		// can't buy from yourself
		assert_noop!(
			Nfts::buy_item(RuntimeOrigin::signed(user_1.clone()), collection_id, item_2, price_2),
			Error::<Test>::NoPermission
		);

		// can't buy when the item is listed for a specific buyer
		assert_noop!(
			Nfts::buy_item(RuntimeOrigin::signed(user_2.clone()), collection_id, item_2, price_2),
			Error::<Test>::NoPermission
		);

		// can buy when I'm a whitelisted buyer
		assert_ok!(Nfts::buy_item(
			RuntimeOrigin::signed(user_3.clone()),
			collection_id,
			item_2,
			price_2
		));

		assert!(events().contains(&Event::<Test>::ItemBought {
			collection: collection_id,
			item: item_2,
			price: price_2,
			seller: user_1.clone(),
			buyer: user_3.clone(),
		}));

		// ensure we reset the buyer field
		assert!(!ItemPriceOf::<Test>::contains_key(collection_id, item_2));

		// can't buy when item is not for sale
		assert_noop!(
			Nfts::buy_item(RuntimeOrigin::signed(user_2.clone()), collection_id, item_3, price_2),
			Error::<Test>::NotForSale
		);

		// ensure we can't buy an item when the collection or an item are frozen
		{
			assert_ok!(Nfts::set_price(
				RuntimeOrigin::signed(user_1.clone()),
				collection_id,
				item_3,
				Some(price_1),
				None,
			));

			// lock the collection
			assert_ok!(Nfts::lock_collection(
				RuntimeOrigin::signed(user_1.clone()),
				collection_id,
				CollectionSettings::from_disabled(CollectionSetting::TransferableItems.into())
			));

			let buy_item_call = mock::RuntimeCall::Nfts(crate::Call::<Test>::buy_item {
				collection: collection_id,
				item: item_3,
				bid_price: price_1,
			});
			assert_noop!(
				buy_item_call.dispatch(RuntimeOrigin::signed(user_2.clone())),
				Error::<Test>::ItemsNonTransferable
			);

			// unlock the collection
			assert_ok!(Nfts::force_collection_config(
				RuntimeOrigin::root(),
				collection_id,
				collection_config_with_all_settings_enabled(),
			));

			// lock the transfer
			assert_ok!(Nfts::lock_item_transfer(
				RuntimeOrigin::signed(user_1.clone()),
				collection_id,
				item_3,
			));

			let buy_item_call = mock::RuntimeCall::Nfts(crate::Call::<Test>::buy_item {
				collection: collection_id,
				item: item_3,
				bid_price: price_1,
			});
			assert_noop!(
				buy_item_call.dispatch(RuntimeOrigin::signed(user_2)),
				Error::<Test>::ItemLocked
			);
		}
	});
}

#[test]
fn pay_tips_should_work() {
	new_test_ext().execute_with(|| {
		let user_1 = account(1);
		let user_2 = account(2);
		let user_3 = account(3);
		let collection_id = 0;
		let item_id = 1;
		let tip = 2;
		let initial_balance = 100;

		Balances::make_free_balance_be(&user_1, initial_balance);
		Balances::make_free_balance_be(&user_2, initial_balance);
		Balances::make_free_balance_be(&user_3, initial_balance);

		assert_ok!(Nfts::pay_tips(
			RuntimeOrigin::signed(user_1.clone()),
			bvec![
				ItemTip {
					collection: collection_id,
					item: item_id,
					receiver: user_2.clone(),
					amount: tip
				},
				ItemTip {
					collection: collection_id,
					item: item_id,
					receiver: user_3.clone(),
					amount: tip
				},
			]
		));

		assert_eq!(Balances::total_balance(&user_1), initial_balance - tip * 2);
		assert_eq!(Balances::total_balance(&user_2), initial_balance + tip);
		assert_eq!(Balances::total_balance(&user_3), initial_balance + tip);

		let events = events();
		assert!(events.contains(&Event::<Test>::TipSent {
			collection: collection_id,
			item: item_id,
			sender: user_1.clone(),
			receiver: user_2.clone(),
			amount: tip,
		}));
		assert!(events.contains(&Event::<Test>::TipSent {
			collection: collection_id,
			item: item_id,
			sender: user_1.clone(),
			receiver: user_3.clone(),
			amount: tip,
		}));
	});
}

#[test]
fn create_cancel_swap_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let user_id = account(1);
		let collection_id = 0;
		let item_1 = 1;
		let item_2 = 2;
		let price = 1;
		let price_direction = PriceDirection::Receive;
		let price_with_direction = PriceWithDirection { amount: price, direction: price_direction };
		let duration = 2;
		let expect_deadline = 3;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			default_collection_config()
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			user_id.clone(),
			None,
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_2,
			user_id.clone(),
			None,
		));

		// validate desired item and the collection exists
		assert_noop!(
			Nfts::create_swap(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_1,
				collection_id,
				Some(item_2 + 1),
				Some(price_with_direction.clone()),
				duration,
			),
			Error::<Test>::UnknownItem
		);
		assert_noop!(
			Nfts::create_swap(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_1,
				collection_id + 1,
				None,
				Some(price_with_direction.clone()),
				duration,
			),
			Error::<Test>::UnknownCollection
		);

		let max_duration: u64 = <Test as Config>::MaxDeadlineDuration::get();
		assert_noop!(
			Nfts::create_swap(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_1,
				collection_id,
				Some(item_2),
				Some(price_with_direction.clone()),
				max_duration.saturating_add(1),
			),
			Error::<Test>::WrongDuration
		);

		assert_ok!(Nfts::create_swap(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			collection_id,
			Some(item_2),
			Some(price_with_direction.clone()),
			duration,
		));

		let swap = PendingSwapOf::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(swap.desired_collection, collection_id);
		assert_eq!(swap.desired_item, Some(item_2));
		assert_eq!(swap.price, Some(price_with_direction.clone()));
		assert_eq!(swap.deadline, expect_deadline);

		assert!(events().contains(&Event::<Test>::SwapCreated {
			offered_collection: collection_id,
			offered_item: item_1,
			desired_collection: collection_id,
			desired_item: Some(item_2),
			price: Some(price_with_direction.clone()),
			deadline: expect_deadline,
		}));

		// validate we can cancel the swap
		assert_ok!(Nfts::cancel_swap(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1
		));
		assert!(events().contains(&Event::<Test>::SwapCancelled {
			offered_collection: collection_id,
			offered_item: item_1,
			desired_collection: collection_id,
			desired_item: Some(item_2),
			price: Some(price_with_direction.clone()),
			deadline: expect_deadline,
		}));
		assert!(!PendingSwapOf::<Test>::contains_key(collection_id, item_1));

		// validate anyone can cancel the expired swap
		assert_ok!(Nfts::create_swap(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_1,
			collection_id,
			Some(item_2),
			Some(price_with_direction.clone()),
			duration,
		));
		assert_noop!(
			Nfts::cancel_swap(RuntimeOrigin::signed(account(2)), collection_id, item_1),
			Error::<Test>::NoPermission
		);
		System::set_block_number(expect_deadline + 1);
		assert_ok!(Nfts::cancel_swap(RuntimeOrigin::signed(account(2)), collection_id, item_1));

		// validate optional desired_item param
		assert_ok!(Nfts::create_swap(
			RuntimeOrigin::signed(user_id),
			collection_id,
			item_1,
			collection_id,
			None,
			Some(price_with_direction),
			duration,
		));

		let swap = PendingSwapOf::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(swap.desired_item, None);
	});
}

#[test]
fn claim_swap_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let user_1 = account(1);
		let user_2 = account(2);
		let collection_id = 0;
		let item_1 = 1;
		let item_2 = 2;
		let item_3 = 3;
		let item_4 = 4;
		let item_5 = 5;
		let price = 100;
		let price_direction = PriceDirection::Receive;
		let price_with_direction =
			PriceWithDirection { amount: price, direction: price_direction.clone() };
		let duration = 2;
		let initial_balance = 1000;
		let deadline = 1 + duration;

		Balances::make_free_balance_be(&user_1, initial_balance);
		Balances::make_free_balance_be(&user_2, initial_balance);

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_1.clone(),
			default_collection_config()
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_1,
			user_1.clone(),
			None,
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_2,
			user_2.clone(),
			default_item_config(),
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_3,
			user_2.clone(),
			default_item_config(),
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_4,
			user_1.clone(),
			None,
		));
		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_5,
			user_2.clone(),
			default_item_config(),
		));

		assert_ok!(Nfts::create_swap(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_1,
			collection_id,
			Some(item_2),
			Some(price_with_direction.clone()),
			duration,
		));

		// validate the deadline
		System::set_block_number(5);
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_2,
				collection_id,
				item_1,
				Some(price_with_direction.clone()),
			),
			Error::<Test>::DeadlineExpired
		);
		System::set_block_number(1);

		// validate edge cases
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_2,
				collection_id,
				item_4, // no swap was created for that asset
				Some(price_with_direction.clone()),
			),
			Error::<Test>::UnknownSwap
		);
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_4, // not my item
				collection_id,
				item_1,
				Some(price_with_direction.clone()),
			),
			Error::<Test>::NoPermission
		);
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_5, // my item, but not the one another part wants
				collection_id,
				item_1,
				Some(price_with_direction.clone()),
			),
			Error::<Test>::UnknownSwap
		);
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_2,
				collection_id,
				item_1,
				Some(PriceWithDirection { amount: price + 1, direction: price_direction.clone() }), // wrong price
			),
			Error::<Test>::UnknownSwap
		);
		assert_noop!(
			Nfts::claim_swap(
				RuntimeOrigin::signed(user_2.clone()),
				collection_id,
				item_2,
				collection_id,
				item_1,
				Some(PriceWithDirection { amount: price, direction: PriceDirection::Send }), // wrong direction
			),
			Error::<Test>::UnknownSwap
		);

		assert_ok!(Nfts::claim_swap(
			RuntimeOrigin::signed(user_2.clone()),
			collection_id,
			item_2,
			collection_id,
			item_1,
			Some(price_with_direction.clone()),
		));

		// validate the new owner
		let item = Item::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(item.owner, user_2.clone());
		let item = Item::<Test>::get(collection_id, item_2).unwrap();
		assert_eq!(item.owner, user_1.clone());

		// validate the balances
		assert_eq!(Balances::total_balance(&user_1), initial_balance + price);
		assert_eq!(Balances::total_balance(&user_2), initial_balance - price);

		// ensure we reset the swap
		assert!(!PendingSwapOf::<Test>::contains_key(collection_id, item_1));

		// validate the event
		assert!(events().contains(&Event::<Test>::SwapClaimed {
			sent_collection: collection_id,
			sent_item: item_2,
			sent_item_owner: user_2.clone(),
			received_collection: collection_id,
			received_item: item_1,
			received_item_owner: user_1.clone(),
			price: Some(price_with_direction.clone()),
			deadline,
		}));

		// validate the optional desired_item param and another price direction
		let price_direction = PriceDirection::Send;
		let price_with_direction = PriceWithDirection { amount: price, direction: price_direction };
		Balances::make_free_balance_be(&user_1, initial_balance);
		Balances::make_free_balance_be(&user_2, initial_balance);

		assert_ok!(Nfts::create_swap(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_4,
			collection_id,
			None,
			Some(price_with_direction.clone()),
			duration,
		));
		assert_ok!(Nfts::claim_swap(
			RuntimeOrigin::signed(user_2.clone()),
			collection_id,
			item_1,
			collection_id,
			item_4,
			Some(price_with_direction),
		));
		let item = Item::<Test>::get(collection_id, item_1).unwrap();
		assert_eq!(item.owner, user_1);
		let item = Item::<Test>::get(collection_id, item_4).unwrap();
		assert_eq!(item.owner, user_2);

		assert_eq!(Balances::total_balance(&user_1), initial_balance - price);
		assert_eq!(Balances::total_balance(&user_2), initial_balance + price);
	});
}

#[test]
fn various_collection_settings() {
	new_test_ext().execute_with(|| {
		// when we set only one value it's required to call .into() on it
		let config =
			collection_config_from_disabled_settings(CollectionSetting::TransferableItems.into());
		assert_ok!(Nfts::force_create(RuntimeOrigin::root(), account(1), config));

		let config = CollectionConfigOf::<Test>::get(0).unwrap();
		assert!(!config.is_setting_enabled(CollectionSetting::TransferableItems));
		assert!(config.is_setting_enabled(CollectionSetting::UnlockedMetadata));

		// no need to call .into() for multiple values
		let config = collection_config_from_disabled_settings(
			CollectionSetting::UnlockedMetadata | CollectionSetting::TransferableItems,
		);
		assert_ok!(Nfts::force_create(RuntimeOrigin::root(), account(1), config));

		let config = CollectionConfigOf::<Test>::get(1).unwrap();
		assert!(!config.is_setting_enabled(CollectionSetting::TransferableItems));
		assert!(!config.is_setting_enabled(CollectionSetting::UnlockedMetadata));

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			account(1),
			default_collection_config()
		));
	});
}

#[test]
fn collection_locking_should_work() {
	new_test_ext().execute_with(|| {
		let user_id = account(1);
		let collection_id = 0;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			collection_config_with_all_settings_enabled()
		));

		let lock_config =
			collection_config_from_disabled_settings(CollectionSetting::DepositRequired.into());
		assert_noop!(
			Nfts::lock_collection(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				lock_config.settings,
			),
			Error::<Test>::WrongSetting
		);

		// validate partial lock
		let lock_config = collection_config_from_disabled_settings(
			CollectionSetting::TransferableItems | CollectionSetting::UnlockedAttributes,
		);
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			lock_config.settings,
		));

		let stored_config = CollectionConfigOf::<Test>::get(collection_id).unwrap();
		assert_eq!(stored_config, lock_config);

		// validate full lock
		assert_ok!(Nfts::lock_collection(
			RuntimeOrigin::signed(user_id),
			collection_id,
			CollectionSettings::from_disabled(CollectionSetting::UnlockedMetadata.into()),
		));

		let stored_config = CollectionConfigOf::<Test>::get(collection_id).unwrap();
		let full_lock_config = collection_config_from_disabled_settings(
			CollectionSetting::TransferableItems |
				CollectionSetting::UnlockedMetadata |
				CollectionSetting::UnlockedAttributes,
		);
		assert_eq!(stored_config, full_lock_config);
	});
}

#[test]
fn pallet_level_feature_flags_should_work() {
	new_test_ext().execute_with(|| {
		Features::set(&PalletFeatures::from_disabled(
			PalletFeature::Trading | PalletFeature::Approvals | PalletFeature::Attributes,
		));

		let user_id = account(1);
		let collection_id = 0;
		let item_id = 1;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_id.clone(),
			default_collection_config()
		));

		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_id.clone()),
			collection_id,
			item_id,
			user_id.clone(),
			None,
		));

		// PalletFeature::Trading
		assert_noop!(
			Nfts::set_price(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_id,
				Some(1),
				None
			),
			Error::<Test>::MethodDisabled
		);
		assert_noop!(
			Nfts::buy_item(RuntimeOrigin::signed(user_id.clone()), collection_id, item_id, 1),
			Error::<Test>::MethodDisabled
		);

		// PalletFeature::Approvals
		assert_noop!(
			Nfts::approve_transfer(
				RuntimeOrigin::signed(user_id.clone()),
				collection_id,
				item_id,
				account(2),
				None
			),
			Error::<Test>::MethodDisabled
		);

		// PalletFeature::Attributes
		assert_noop!(
			Nfts::set_attribute(
				RuntimeOrigin::signed(user_id),
				collection_id,
				None,
				AttributeNamespace::CollectionOwner,
				bvec![0],
				bvec![0],
			),
			Error::<Test>::MethodDisabled
		);
	})
}

#[test]
fn group_roles_by_account_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Nfts::group_roles_by_account(vec![]), vec![]);

		let account_to_role = Nfts::group_roles_by_account(vec![
			(account(3), CollectionRole::Freezer),
			(account(1), CollectionRole::Issuer),
			(account(2), CollectionRole::Admin),
		]);
		let expect = vec![
			(account(1), CollectionRoles(CollectionRole::Issuer.into())),
			(account(2), CollectionRoles(CollectionRole::Admin.into())),
			(account(3), CollectionRoles(CollectionRole::Freezer.into())),
		];
		assert_eq!(account_to_role, expect);

		let account_to_role = Nfts::group_roles_by_account(vec![
			(account(3), CollectionRole::Freezer),
			(account(2), CollectionRole::Issuer),
			(account(2), CollectionRole::Admin),
		]);
		let expect = vec![
			(account(2), CollectionRoles(CollectionRole::Issuer | CollectionRole::Admin)),
			(account(3), CollectionRoles(CollectionRole::Freezer.into())),
		];
		assert_eq!(account_to_role, expect);
	})
}

#[test]
fn add_remove_item_attributes_approval_should_work() {
	new_test_ext().execute_with(|| {
		let user_1 = account(1);
		let user_2 = account(2);
		let user_3 = account(3);
		let user_4 = account(4);
		let collection_id = 0;
		let item_id = 0;

		assert_ok!(Nfts::force_create(
			RuntimeOrigin::root(),
			user_1.clone(),
			default_collection_config()
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_id,
			user_1.clone(),
			None
		));
		assert_ok!(Nfts::approve_item_attributes(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_id,
			user_2.clone(),
		));
		assert_eq!(item_attributes_approvals(collection_id, item_id), vec![user_2.clone()]);

		assert_ok!(Nfts::approve_item_attributes(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_id,
			user_3.clone(),
		));
		assert_ok!(Nfts::approve_item_attributes(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_id,
			user_2.clone(),
		));
		assert_eq!(
			item_attributes_approvals(collection_id, item_id),
			vec![user_2.clone(), user_3.clone()]
		);

		assert_noop!(
			Nfts::approve_item_attributes(
				RuntimeOrigin::signed(user_1.clone()),
				collection_id,
				item_id,
				user_4,
			),
			Error::<Test>::ReachedApprovalLimit
		);

		assert_ok!(Nfts::cancel_item_attributes_approval(
			RuntimeOrigin::signed(user_1),
			collection_id,
			item_id,
			user_2,
			CancelAttributesApprovalWitness { account_attributes: 1 },
		));
		assert_eq!(item_attributes_approvals(collection_id, item_id), vec![user_3]);
	})
}

#[test]
fn validate_signature() {
	new_test_ext().execute_with(|| {
		let user_1_pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let user_1_signer = MultiSigner::Sr25519(user_1_pair.public());
		let user_1 = user_1_signer.clone().into_account();
		let mint_data: PreSignedMint<u32, u32, AccountId, u32> = PreSignedMint {
			collection: 0,
			item: 0,
			attributes: vec![],
			metadata: vec![],
			only_account: None,
			deadline: 100000,
		};
		let encoded_data = Encode::encode(&mint_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&encoded_data));
		assert_ok!(Nfts::validate_signature(&encoded_data, &signature, &user_1));

		let mut wrapped_data: Vec<u8> = Vec::new();
		wrapped_data.extend(b"<Bytes>");
		wrapped_data.extend(&encoded_data);
		wrapped_data.extend(b"</Bytes>");

		let signature = MultiSignature::Sr25519(user_1_pair.sign(&wrapped_data));
		assert_ok!(Nfts::validate_signature(&encoded_data, &signature, &user_1));
	})
}

#[test]
fn pre_signed_mints_should_work() {
	new_test_ext().execute_with(|| {
		let user_0 = account(0);
		let user_1_pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let user_1_signer = MultiSigner::Sr25519(user_1_pair.public());
		let user_1 = user_1_signer.clone().into_account();
		let mint_data = PreSignedMint {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3])],
			metadata: vec![0, 1],
			only_account: None,
			deadline: 10000000,
		};
		let message = Encode::encode(&mint_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));
		let user_2 = account(2);
		let user_3 = account(3);

		Balances::make_free_balance_be(&user_0, 100);
		Balances::make_free_balance_be(&user_2, 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(user_0.clone()),
			user_1.clone(),
			collection_config_with_all_settings_enabled(),
		));

		assert_ok!(Nfts::mint_pre_signed(
			RuntimeOrigin::signed(user_2.clone()),
			mint_data.clone(),
			signature.clone(),
			user_1.clone(),
		));
		assert_eq!(items(), vec![(user_2.clone(), 0, 0)]);
		let metadata = ItemMetadataOf::<Test>::get(0, 0).unwrap();
		assert_eq!(
			metadata.deposit,
			ItemMetadataDeposit { account: Some(user_2.clone()), amount: 3 }
		);
		assert_eq!(metadata.data, vec![0, 1]);

		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![1]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![2], bvec![3]),
			]
		);
		let attribute_key: BoundedVec<_, _> = bvec![0];
		let (_, deposit) = Attribute::<Test>::get((
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			&attribute_key,
		))
		.unwrap();
		assert_eq!(deposit.account, Some(user_2.clone()));
		assert_eq!(deposit.amount, 3);

		assert_eq!(Balances::free_balance(&user_0), 100 - 2); // 2 - collection deposit
		assert_eq!(Balances::free_balance(&user_2), 100 - 1 - 3 - 6); // 1 - item deposit, 3 - metadata, 6 - attributes

		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				mint_data,
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::AlreadyExists
		);

		assert_ok!(Nfts::burn(RuntimeOrigin::signed(user_2.clone()), 0, 0));
		assert_eq!(Balances::free_balance(&user_2), 100 - 6);

		// validate the `only_account` field
		let mint_data = PreSignedMint {
			collection: 0,
			item: 0,
			attributes: vec![],
			metadata: vec![],
			only_account: Some(account(2)),
			deadline: 10000000,
		};

		// can't mint with the wrong signature
		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				mint_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::WrongSignature
		);

		let message = Encode::encode(&mint_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_3),
				mint_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::WrongOrigin
		);

		// validate signature's expiration
		System::set_block_number(10000001);
		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				mint_data,
				signature,
				user_1.clone(),
			),
			Error::<Test>::DeadlineExpired
		);
		System::set_block_number(1);

		// validate the collection
		let mint_data = PreSignedMint {
			collection: 1,
			item: 0,
			attributes: vec![],
			metadata: vec![],
			only_account: Some(account(2)),
			deadline: 10000000,
		};
		let message = Encode::encode(&mint_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				mint_data,
				signature,
				user_1.clone(),
			),
			Error::<Test>::NoPermission
		);

		// validate max attributes limit
		let mint_data = PreSignedMint {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3]), (vec![2], vec![3])],
			metadata: vec![0, 1],
			only_account: None,
			deadline: 10000000,
		};
		let message = Encode::encode(&mint_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));
		assert_noop!(
			Nfts::mint_pre_signed(
				RuntimeOrigin::signed(user_2),
				mint_data,
				signature,
				user_1.clone(),
			),
			Error::<Test>::MaxAttributesLimitReached
		);
	})
}

#[test]
fn pre_signed_attributes_should_work() {
	new_test_ext().execute_with(|| {
		let user_1_pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let user_1_signer = MultiSigner::Sr25519(user_1_pair.public());
		let user_1 = user_1_signer.clone().into_account();
		let user_2 = account(2);
		let user_3_pair = sp_core::sr25519::Pair::from_string("//Bob", None).unwrap();
		let user_3_signer = MultiSigner::Sr25519(user_3_pair.public());
		let user_3 = user_3_signer.clone().into_account();
		let collection_id = 0;
		let item_id = 0;

		Balances::make_free_balance_be(&user_1, 100);
		Balances::make_free_balance_be(&user_2, 100);
		Balances::make_free_balance_be(&user_3, 100);
		assert_ok!(Nfts::create(
			RuntimeOrigin::signed(user_1.clone()),
			user_1.clone(),
			collection_config_with_all_settings_enabled(),
		));
		assert_ok!(Nfts::mint(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			item_id,
			user_2.clone(),
			None,
		));

		// validate the CollectionOwner namespace
		let pre_signed_data = PreSignedAttributes {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3])],
			namespace: AttributeNamespace::CollectionOwner,
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_ok!(Nfts::set_attributes_pre_signed(
			RuntimeOrigin::signed(user_2.clone()),
			pre_signed_data.clone(),
			signature.clone(),
			user_1.clone(),
		));

		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![1]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![2], bvec![3]),
			]
		);
		let attribute_key: BoundedVec<_, _> = bvec![0];
		let (_, deposit) = Attribute::<Test>::get((
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			&attribute_key,
		))
		.unwrap();
		assert_eq!(deposit.account, Some(user_2.clone()));
		assert_eq!(deposit.amount, 3);

		assert_eq!(Balances::free_balance(&user_1), 100 - 2 - 1); // 2 - collection deposit, 1 - item deposit
		assert_eq!(Balances::free_balance(&user_2), 100 - 6); // 6 - attributes

		// validate the deposit gets returned on attribute update from collection's owner
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(user_1.clone()),
			collection_id,
			Some(item_id),
			AttributeNamespace::CollectionOwner,
			bvec![0],
			bvec![1],
		));
		let (_, deposit) = Attribute::<Test>::get((
			0,
			Some(0),
			AttributeNamespace::CollectionOwner,
			&attribute_key,
		))
		.unwrap();
		assert_eq!(deposit.account, None);
		assert_eq!(deposit.amount, 3);

		// validate we don't partially modify the state
		assert_eq!(item_attributes_approvals(collection_id, item_id), vec![]);
		let pre_signed_data = PreSignedAttributes {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2; 51], vec![3])],
			namespace: AttributeNamespace::Account(user_3.clone()),
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_3_pair.sign(&message));

		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_3.clone(),
			),
			Error::<Test>::IncorrectData
		);

		// no new approval was set
		assert_eq!(item_attributes_approvals(collection_id, item_id), vec![]);

		// no new attributes were added
		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![1]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![2], bvec![3]),
			]
		);

		// validate the Account namespace
		let pre_signed_data = PreSignedAttributes {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3])],
			namespace: AttributeNamespace::Account(user_3.clone()),
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_3_pair.sign(&message));

		assert_ok!(Nfts::set_attributes_pre_signed(
			RuntimeOrigin::signed(user_2.clone()),
			pre_signed_data.clone(),
			signature.clone(),
			user_3.clone(),
		));

		assert_eq!(
			attributes(0),
			vec![
				(Some(0), AttributeNamespace::CollectionOwner, bvec![0], bvec![1]),
				(Some(0), AttributeNamespace::Account(user_3.clone()), bvec![0], bvec![1]),
				(Some(0), AttributeNamespace::CollectionOwner, bvec![2], bvec![3]),
				(Some(0), AttributeNamespace::Account(user_3.clone()), bvec![2], bvec![3]),
			]
		);
		assert_eq!(item_attributes_approvals(collection_id, item_id), vec![user_3.clone()]);

		let attribute_key: BoundedVec<_, _> = bvec![0];
		let (_, deposit) = Attribute::<Test>::get((
			0,
			Some(0),
			AttributeNamespace::Account(user_3.clone()),
			&attribute_key,
		))
		.unwrap();
		assert_eq!(deposit.account, Some(user_2.clone()));
		assert_eq!(deposit.amount, 3);

		assert_eq!(Balances::free_balance(&user_2), 100 - 9);
		assert_eq!(Balances::free_balance(&user_3), 100);

		// validate the deposit gets returned on attribute update from user_3
		assert_ok!(Nfts::set_attribute(
			RuntimeOrigin::signed(user_3.clone()),
			collection_id,
			Some(item_id),
			AttributeNamespace::Account(user_3.clone()),
			bvec![0],
			bvec![1],
		));
		let (_, deposit) = Attribute::<Test>::get((
			0,
			Some(0),
			AttributeNamespace::Account(user_3.clone()),
			&attribute_key,
		))
		.unwrap();
		assert_eq!(deposit.account, Some(user_3.clone()));
		assert_eq!(deposit.amount, 3);

		assert_eq!(Balances::free_balance(&user_2), 100 - 6);
		assert_eq!(Balances::free_balance(&user_3), 100 - 3);

		// can't update with the wrong signature
		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::WrongSignature
		);

		// can't update if I don't own that item
		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_3.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_3.clone(),
			),
			Error::<Test>::NoPermission
		);

		// can't update the CollectionOwner namespace if the signer is not an owner of that
		// collection
		let pre_signed_data = PreSignedAttributes {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3])],
			namespace: AttributeNamespace::CollectionOwner,
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_3_pair.sign(&message));

		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_3.clone(),
			),
			Error::<Test>::NoPermission
		);

		// validate signature's expiration
		System::set_block_number(10000001);
		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_3.clone(),
			),
			Error::<Test>::DeadlineExpired
		);
		System::set_block_number(1);

		// validate item & collection
		let pre_signed_data = PreSignedAttributes {
			collection: 1,
			item: 1,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3])],
			namespace: AttributeNamespace::CollectionOwner,
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::UnknownItem
		);

		// validate max attributes limit
		let pre_signed_data = PreSignedAttributes {
			collection: 1,
			item: 1,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3]), (vec![2], vec![3])],
			namespace: AttributeNamespace::CollectionOwner,
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::MaxAttributesLimitReached
		);

		// validate the attribute's value length
		let pre_signed_data = PreSignedAttributes {
			collection: 0,
			item: 0,
			attributes: vec![(vec![0], vec![1]), (vec![2], vec![3; 51])],
			namespace: AttributeNamespace::CollectionOwner,
			deadline: 10000000,
		};
		let message = Encode::encode(&pre_signed_data);
		let signature = MultiSignature::Sr25519(user_1_pair.sign(&message));

		assert_noop!(
			Nfts::set_attributes_pre_signed(
				RuntimeOrigin::signed(user_2.clone()),
				pre_signed_data.clone(),
				signature.clone(),
				user_1.clone(),
			),
			Error::<Test>::IncorrectData
		);
	})
}
