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

//! Tests for the NFTs Royalty pallet.

use super::Event as NftsRoyaltyEvent;
use crate::{
	mock::*, CollectionRoyalty, Error, ItemRoyalty, RoyaltyDetails,
};
use frame_support::{assert_noop, assert_ok, traits::Currency};

use pallet_nfts::{
	Account, CollectionAccount, CollectionConfig, CollectionSetting, CollectionSettings,
	ItemConfig, ItemSettings, MintSettings,
};

pub use sp_runtime::{DispatchError, ModuleError, Permill};

type AccountIdOf<Test> = <Test as frame_system::Config>::AccountId;
fn account(id: u8) -> AccountIdOf<Test> {
	[id; 32].into()
}

fn last_event() -> NftsRoyaltyEvent<Test> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::NftsRoyalty(inner) = e { Some(inner) } else { None })
		.last()
		.unwrap()
}

// Create a collection calling directly the NFTs pallet
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

fn mint_item() -> u32 {
	let item_id = 42;
	assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, item_id, account(1), None,));
	item_id
}

// Set up balances for testing
fn set_up_balances(initial_balance: u64) {
	Balances::make_free_balance_be(&account(1), initial_balance);
	Balances::make_free_balance_be(&account(2), initial_balance);
	Balances::make_free_balance_be(&account(3), initial_balance);
	Balances::make_free_balance_be(&account(4), initial_balance);
}

#[test]
fn set_collection_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		set_up_balances(100);
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = CollectionRoyalty::<Test>::get(0).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		// Check that the deposit was taken
		assert_eq!(Balances::free_balance(&account(1)), 99);

		// Check the event was emitted
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyForCollectionSet {
				nft_collection: 0,
				royalty_percentage: Permill::from_percent(5),
				royalty_admin: account(1),
				royalty_recipients: nft_with_royalty.recipients
			}
		);
	});
}

#[test]
fn set_collection_royalty_fail_item_not_exist() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NftsRoyalty::set_collection_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				Permill::from_percent(5),
				account(1),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::CollectionDoesNotExist
		);
	});
}

#[test]
fn set_collection_royalty_fail_no_permission() {
	new_test_ext().execute_with(|| {
		create_collection();
		assert_noop!(
			NftsRoyalty::set_collection_royalty(
				RuntimeOrigin::signed(account(2)),
				0,
				Permill::from_percent(5),
				account(2),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn set_collection_royalty_fail_ovewrite() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		assert_noop!(
			NftsRoyalty::set_collection_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				Permill::from_percent(15),
				account(1),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::RoyaltyAlreadyExists
		);
	});
}
#[test]
fn set_collection_royalty_fail_limit_recipients() {
	new_test_ext().execute_with(|| {
		create_collection();
		set_up_balances(100);
		assert_noop!(
			NftsRoyalty::set_collection_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				Permill::from_percent(5),
				account(1),
				vec![
					RoyaltyDetails {
						royalty_recipient: account(1),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(2),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(3),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(4),
						royalty_recipient_percentage: Permill::from_percent(25),
					}
				]
			),
			Error::<Test>::MaxRecipientsLimit
		);
	});
}

#[test]
fn set_collection_royalty_fail_invalid_percentages() {
	new_test_ext().execute_with(|| {
		create_collection();
		set_up_balances(100);
		assert_noop!(
			NftsRoyalty::set_collection_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				Permill::from_percent(5),
				account(1),
				vec![
					RoyaltyDetails {
						royalty_recipient: account(1),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(2),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(3),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
				]
			),
			Error::<Test>::InvalidRoyaltyPercentage
		);
	});
}

#[test]
fn set_item_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Get the items directly from the NFTs pallet, to see if has been created there
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(1), 0, mint_id)]);

		// Read royalty pallet's storage.
		let nft_with_royalty = ItemRoyalty::<Test>::get((0, mint_id)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		// Check that the deposit was taken
		assert_eq!(Balances::free_balance(&account(1)), 99);

		// Check the event was emitted
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyForItemSet {
				nft_collection: 0,
				nft: mint_id,
				royalty_percentage: Permill::from_percent(5),
				royalty_admin: account(1),
				royalty_recipients: nft_with_royalty.recipients
			}
		);
	});
}

#[test]
fn set_item_royalty_fail_item_not_exist() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NftsRoyalty::set_item_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				42,
				Permill::from_percent(5),
				account(1),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::NftDoesNotExist
		);
	});
}

#[test]
fn set_item_royalty_fail_no_permission() {
	new_test_ext().execute_with(|| {
		create_collection();
		let mint_id = mint_item();
		assert_noop!(
			NftsRoyalty::set_item_royalty(
				RuntimeOrigin::signed(account(2)),
				0,
				mint_id,
				Permill::from_percent(5),
				account(2),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn set_item_royalty_fail_ovewrite() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		assert_noop!(
			NftsRoyalty::set_item_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				mint_id,
				Permill::from_percent(15),
				account(1),
				vec![RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				}]
			),
			Error::<Test>::RoyaltyAlreadyExists
		);
	});
}

#[test]
fn set_item_royalty_fail_limit_recipients() {
	new_test_ext().execute_with(|| {
		create_collection();
		set_up_balances(100);
		let mint_id = mint_item();
		assert_noop!(
			NftsRoyalty::set_item_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				mint_id,
				Permill::from_percent(5),
				account(1),
				vec![
					RoyaltyDetails {
						royalty_recipient: account(1),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(2),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(3),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(4),
						royalty_recipient_percentage: Permill::from_percent(25),
					}
				]
			),
			Error::<Test>::MaxRecipientsLimit
		);
	});
}

#[test]
fn set_item_royalty_fail_invalid_percentages() {
	new_test_ext().execute_with(|| {
		create_collection();
		set_up_balances(100);
		let mint_id = mint_item();
		assert_noop!(
			NftsRoyalty::set_item_royalty(
				RuntimeOrigin::signed(account(1)),
				0,
				mint_id,
				Permill::from_percent(5),
				account(1),
				vec![
					RoyaltyDetails {
						royalty_recipient: account(1),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(2),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
					RoyaltyDetails {
						royalty_recipient: account(3),
						royalty_recipient_percentage: Permill::from_percent(25),
					},
				]
			),
			Error::<Test>::InvalidRoyaltyPercentage
		);
	});
}

#[test]
fn transfer_collection_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = CollectionRoyalty::<Test>::get(0).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		assert_ok!(NftsRoyalty::transfer_collection_royalty_recipient(
			RuntimeOrigin::signed(account(1)),
			0,
			account(2)
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = CollectionRoyalty::<Test>::get(0).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(2));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));
		// Check if the event has been emitted.
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RecipientCollectionRoyaltyChanged {
				nft_collection: 0,
				new_royalty_recipient: account(2),
			}
		);
	});
}

#[test]
fn transfer_collection_royalty_should_fail_if_no_royalty_recipient() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = CollectionRoyalty::<Test>::get(0).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		assert_noop!(
			NftsRoyalty::transfer_collection_royalty_recipient(
				RuntimeOrigin::signed(account(2)),
				0,
				account(2)
			),
			Error::<Test>::NoPermission
		);
		// Read royalty pallet's storage to check that the royalty has not changed.
		let nft_with_royalty = CollectionRoyalty::<Test>::get(0).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));
	});
}

#[test]
fn transfer_item_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = ItemRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		assert_ok!(NftsRoyalty::transfer_item_royalty_recipient(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(2)
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = ItemRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(2));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));
		// Check if the event has been emitted.
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RecipientItemRoyaltyChanged {
				nft_collection: 0,
				nft: 42,
				new_royalty_recipient: account(2),
			}
		);
	});
}

#[test]
fn transfer_item_royalty_should_fail_if_no_royalty_recipient() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		// Read royalty pallet's storage.
		let nft_with_royalty = ItemRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));

		assert_noop!(
			NftsRoyalty::transfer_item_royalty_recipient(
				RuntimeOrigin::signed(account(2)),
				0,
				42,
				account(2)
			),
			Error::<Test>::NoPermission
		);
		// Read royalty pallet's storage to check that the royalty has not changed.
		let nft_with_royalty = ItemRoyalty::<Test>::get((0, 42)).unwrap();
		assert_eq!(nft_with_royalty.royalty_percentage, Permill::from_percent(5));
		assert_eq!(nft_with_royalty.royalty_admin, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient, account(1));
		assert_eq!(nft_with_royalty.recipients[0].royalty_recipient_percentage, Permill::from_percent(100));
	});
}

#[test]
fn buy_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(10),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_ok!(NftsRoyalty::buy(RuntimeOrigin::signed(account(2)), 0, 42, 60));
		// Get the items directly from the NFTs pallet, to see if the owner has changed
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(2), 0, 42)]);
		// Check the balance of royalty owner -> initial balance + price item + royalty.
		assert_eq!(Balances::total_balance(&account(1)), initial_balance + 50 + 5);
		// Check the balance of buyer -> initial balance - price item - royalty.
		assert_eq!(Balances::total_balance(&account(2)), initial_balance - 50 - 5);
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyPaid {
				nft_collection: 0,
				nft: 42,
				royalty_amount_paid: 5,
				royalty_recipient: account(1)
			}
		);
	});
}

#[test]
fn buy_should_work_on_item_royalty_with_collection_royalty() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(20),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));

		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(10),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_ok!(NftsRoyalty::buy(RuntimeOrigin::signed(account(2)), 0, 42, 60));
		// Get the items directly from the NFTs pallet, to see if the owner has changed
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(2), 0, 42)]);
		// Check the balance of royalty owner -> initial balance + price item + royalty.
		assert_eq!(Balances::total_balance(&account(1)), initial_balance + 50 + 5);
		// Check the balance of buyer -> initial balance - price item - royalty.
		assert_eq!(Balances::total_balance(&account(2)), initial_balance - 50 - 5);
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyPaid {
				nft_collection: 0,
				nft: 42,
				royalty_amount_paid: 5,
				royalty_recipient: account(1)
			}
		);
	});
}

#[test]
fn buy_should_work_on_collection_royalty_without_item() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		mint_item();
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(10),
			account(1),
			vec![RoyaltyDetails {
				royalty_recipient: account(1),
				royalty_recipient_percentage: Permill::from_percent(100),
			}]
		));
		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_ok!(NftsRoyalty::buy(RuntimeOrigin::signed(account(2)), 0, 42, 60));
		// Get the items directly from the NFTs pallet, to see if the owner has changed
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(2), 0, 42)]);
		// Check the balance of royalty owner -> initial balance + price item + royalty.
		assert_eq!(Balances::total_balance(&account(1)), initial_balance + 50 + 5);
		// Check the balance of buyer -> initial balance - price item - royalty.
		assert_eq!(Balances::total_balance(&account(2)), initial_balance - 50 - 5);
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyPaid {
				nft_collection: 0,
				nft: 42,
				royalty_amount_paid: 5,
				royalty_recipient: account(1)
			}
		);
	});
}

#[test]
fn buy_should_work_with_multiple_recipients_at_collection_level() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(10),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(20),
				},
				RoyaltyDetails {
					royalty_recipient: account(2),
					royalty_recipient_percentage: Permill::from_percent(60),
				},
				RoyaltyDetails {
					royalty_recipient: account(3),
					royalty_recipient_percentage: Permill::from_percent(20),
				}
			],
		));
		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_ok!(NftsRoyalty::buy(RuntimeOrigin::signed(account(4)), 0, 42, 60));
		// Get the items directly from the NFTs pallet, to see if the owner has changed
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(4), 0, 42)]);
		// Check the balance of royalties recipients -> initial balance + price item + royalty.
		assert_eq!(Balances::total_balance(&account(1)), initial_balance + 50 + 1);
		assert_eq!(Balances::total_balance(&account(2)), initial_balance + 3);
		assert_eq!(Balances::total_balance(&account(3)), initial_balance + 1);
		// Check the balance of buyer -> initial balance - price item - royalty.
		assert_eq!(Balances::total_balance(&account(4)), initial_balance - 50 - 5);
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyPaid {
				nft_collection: 0,
				nft: 42,
				royalty_amount_paid: 1,
				royalty_recipient: account(3)
			}
		);
	});
}

#[test]
fn buy_should_work_with_multiple_recipients_at_item_level() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(10),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(20),
				},
				RoyaltyDetails {
					royalty_recipient: account(2),
					royalty_recipient_percentage: Permill::from_percent(60),
				},
				RoyaltyDetails {
					royalty_recipient: account(3),
					royalty_recipient_percentage: Permill::from_percent(20),
				}
			],
		));
		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(10),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(20),
				},
				RoyaltyDetails {
					royalty_recipient: account(2),
					royalty_recipient_percentage: Permill::from_percent(60),
				},
				RoyaltyDetails {
					royalty_recipient: account(3),
					royalty_recipient_percentage: Permill::from_percent(20),
				}
			],
		));
		
		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_ok!(NftsRoyalty::buy(RuntimeOrigin::signed(account(4)), 0, 42, 60));
		// Get the items directly from the NFTs pallet, to see if the owner has changed
		let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
		items.sort();
		assert_eq!(items, vec![(account(4), 0, 42)]);
		// Check the balance of royalties recipients -> initial balance + price item + royalty.
		assert_eq!(Balances::total_balance(&account(1)), initial_balance + 50 + 1);
		assert_eq!(Balances::total_balance(&account(2)), initial_balance + 3);
		assert_eq!(Balances::total_balance(&account(3)), initial_balance + 1);
		// Check the balance of buyer -> initial balance - price item - royalty.
		assert_eq!(Balances::total_balance(&account(4)), initial_balance - 50 - 5);
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::RoyaltyPaid {
				nft_collection: 0,
				nft: 42,
				royalty_amount_paid: 1,
				royalty_recipient: account(3)
			}
		);
	});
}

#[test]
fn error_if_no_royalty_on_item_to_buy() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		assert_ok!(Nfts::force_mint(
			RuntimeOrigin::signed(account(1)),
			0,
			42,
			account(1),
			ItemConfig { settings: ItemSettings::all_enabled() }
		));

		assert_ok!(Nfts::set_price(RuntimeOrigin::signed(account(1)), 0, 42, Some(50), None,));

		assert_noop!(
			NftsRoyalty::buy(RuntimeOrigin::signed(account(2)), 0, 42, 50),
			Error::<Test>::NoRoyaltyExists
		);
	});
}

#[test]
fn error_if_buy_item_not_on_sale() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		let mint_id = mint_item();
		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				},
			],
		));

		assert_noop!(
			NftsRoyalty::buy(RuntimeOrigin::signed(account(2)), 0, 42, 50),
			Error::<Test>::NotForSale
		);
	});
}

#[test]
fn remove_collection_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		assert_ok!(NftsRoyalty::set_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			Permill::from_percent(5),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				},
			],
		));

		// Check that the deposit was taken
		assert_eq!(Balances::free_balance(&account(1)), initial_balance - 1);

		assert_ok!(NftsRoyalty::remove_collection_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
		));

		// Check the balance of royalty owner -> initial balance + deposit.
		assert_eq!(Balances::free_balance(&account(1)), initial_balance);
		
		// Check the event was emitted
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::CollectionRoyaltyRemoved {
				nft_collection: 0,
			}
		);
	});
}

#[test]
fn remove_item_royalty_should_work() {
	new_test_ext().execute_with(|| {
		create_collection();
		let initial_balance = 100;
		set_up_balances(initial_balance);

		// Create an item
		let mint_id = mint_item();

		assert_ok!(NftsRoyalty::set_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
			Permill::from_percent(5),
			account(1),
			vec![
				RoyaltyDetails {
					royalty_recipient: account(1),
					royalty_recipient_percentage: Permill::from_percent(100),
				},
			],
		));

		// Check that the deposit was taken
		assert_eq!(Balances::free_balance(&account(1)), initial_balance - 1);

		assert_ok!(NftsRoyalty::remove_item_royalty(
			RuntimeOrigin::signed(account(1)),
			0,
			mint_id,
		));

		// Check the balance of royalty owner -> initial balance + deposit.
		assert_eq!(Balances::free_balance(&account(1)), initial_balance);
		
		// Check the event was emitted
		assert_eq!(
			last_event(),
			NftsRoyaltyEvent::ItemRoyaltyRemoved {
				nft_collection: 0,
				nft: 42,
			}
		);
	});
}