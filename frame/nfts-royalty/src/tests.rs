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

//! Tests for the NFT Royalties pallet.

use crate::{mock::*, Error, NftWithRoyalty};
use frame_support::{assert_noop, assert_ok};
use pallet_nfts::{
	Account, CollectionAccount, CollectionConfig, CollectionSetting, CollectionSettings,
	Error as NftErrors, ItemSettings, MintSettings, ItemConfig
};
pub use sp_runtime::{DispatchError, ModuleError, Permill};

type AccountIdOf<Test> = <Test as frame_system::Config>::AccountId;
fn account(id: u8) -> AccountIdOf<Test> {
	[id; 32].into()
}
// Create a collection calling directly the NFT pallet
fn create_collection() {
	assert_ok!(Nfts::force_create(
		RuntimeOrigin::root(),
		account(1),
		CollectionConfig {
			settings: CollectionSettings::from_disabled(CollectionSetting::DepositRequired.into()),
			max_supply: None,
			mint_settings: MintSettings::default(),
		}
	));
	let mut collections: Vec<_> = CollectionAccount::<Test>::iter().map(|x| (x.0, x.1)).collect();
	collections.sort();
	assert_eq!(collections, vec![(account(1), 0)]);
}

#[test]
fn nft_minting_with_royalties_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		assert_ok!(NftsRoyalty::mint_item_with_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(1),
			ItemSettings::all_enabled(),
			Permill::from_percent(5),
			account(1)
		));
		// Get the items directly from the NFT pallet, to see if has been created there
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(1), 0, 42)]);
		// Read royalties pallet storage.
		let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_recipient, account(1));
	});
}

#[test]
fn nft_minting_with_royalties_fail_collection_not_exist() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NftsRoyalty::mint_item_with_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				42,
				account(1),
				ItemSettings::all_enabled(),
				Permill::from_percent(5),
				account(1)
			),
			NftErrors::<Test>::UnknownCollection
		);
	});
}
#[test]
fn nft_burn_with_royalties_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		// Mint the item we are going to burn
		assert_ok!(NftsRoyalty::mint_item_with_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(1),
			ItemSettings::all_enabled(),
			Permill::from_percent(5),
			account(1)
		));
		// Burn the item
		assert_ok!(NftsRoyalty::burn_item_with_royalty(RuntimeOrigin::signed(account(1)), 0, 42));
		// Get the items directly from the NFT pallet, to see if has been burned there
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![]);
		// Read royalties pallet storage to see if the royalties has been deleted.
		assert_eq!(NftWithRoyalty::<Test>::get((0, 42)), None);
	});
}
#[test]
fn nft_burn_error_nft_has_no_royalties() {
	new_test_ext().execute_with(|| {
		// Try to burn the item doesn't have royalties
		assert_noop!(
			NftsRoyalty::burn_item_with_royalty(RuntimeOrigin::signed(account(1)), 0, 42),
			Error::<Test>::NoRoyaltyExists
		);
	});
}

#[test]
fn transfer_royalties_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		assert_ok!(NftsRoyalty::mint_item_with_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(1),
			ItemSettings::all_enabled(),
			Permill::from_percent(5),
			account(1)
		));
		// Read royalties pallet storage.
		let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_recipient, account(1));

		assert_ok!(NftsRoyalty::transfer_royalty_recipient(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2)
		));
		// Read royalties pallet storage.
		let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_recipient, account(2));
	});
}

#[test]
fn transfer_royalties_should_fail_if_not_royalties_recipient() {
	new_test_ext().execute_with(|| {
		create_collection();
		assert_ok!(NftsRoyalty::mint_item_with_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(1),
			ItemSettings::all_enabled(),
			Permill::from_percent(5),
			account(1)
		));
		// Read royalties pallet storage.
		let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_recipient, account(1));

		assert_noop!(
			NftsRoyalty::transfer_royalty_recipient(
				RuntimeOrigin::signed(account(2)),
				0,
				42,
				account(2)
			),
			Error::<Test>::NoPermission
		);
		// Read royalties pallet storage to check the royalties haven't changed.
		let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_recipient, account(1));
	});
}

#[test]
fn set_item_with_royalty_should_work() {
    new_test_ext().execute_with(|| {
        create_collection();
        assert_ok!(Nfts::force_mint(
            RuntimeOrigin::signed(account(1)),
            0,
            43,
            account(1),
            ItemConfig { settings: ItemSettings::all_enabled() }
        ));
        // Make sure the item does not already exist in royalties pallet storage.
        assert_eq!(NftWithRoyalty::<Test>::get((0, 43)), None);
        assert_ok!(NftsRoyalty::set_item_with_royalty(
            RuntimeOrigin::signed(account(1)),
            0,
            43,
            ItemSettings::all_enabled(),
            Permill::from_percent(5),
            account(1)
        ));
        // Read royalties pallet storage.
        let nft_with_royalty = NftWithRoyalty::<Test>::get((0, 43)).unwrap();
        assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
        assert_eq!(nft_with_royalty.royalty_recipient, account(1));
    });
}
