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

//! Tests for Nft fractionalization pallet.

use crate::{mock::*, *};
use frame_support::{
	assert_noop, assert_ok,
	traits::{fungibles::InspectEnumerable, Currency},
};
use pallet_nfts::CollectionConfig;
use sp_runtime::{DispatchError, ModuleError};

fn assets() -> Vec<u32> {
	let mut s: Vec<_> = <<Test as Config>::Assets>::asset_ids().collect();
	s.sort();
	s
}

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let mock::RuntimeEvent::NftFractions(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect();

	System::reset_events();

	result
}

#[test]
fn fractionalize_should_work() {
	new_test_ext().execute_with(|| {
		let nft_collection_id = 0;
		let nft_id = 0;
		let asset_id = 0;
		let fractions = 1000;

		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);

		assert_ok!(Nfts::force_create(RuntimeOrigin::root(), 1, CollectionConfig::default()));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(1), nft_collection_id, nft_id, 1, None));

		assert_ok!(NftFractions::fractionalize(
			RuntimeOrigin::signed(1),
			nft_collection_id,
			nft_id,
			asset_id,
			2,
			fractions,
		));
		assert_eq!(assets(), vec![asset_id]);
		assert_eq!(Assets::balance(asset_id, 2), fractions);
		assert_eq!(Nfts::owner(nft_collection_id, nft_id), Some(1));
		assert_noop!(
			Nfts::transfer(RuntimeOrigin::signed(1), nft_collection_id, nft_id, 2),
			DispatchError::Module(ModuleError {
				index: 4,
				error: [12, 0, 0, 0],
				message: Some("ItemLocked")
			})
		);

		let details = NftToAsset::<Test>::get((&nft_collection_id, &nft_id)).unwrap();
		assert_eq!(details.asset, asset_id);
		assert_eq!(details.fractions, fractions);

		assert!(events().contains(&Event::<Test>::NftFractionalized {
			nft_collection: nft_collection_id,
			nft: nft_id,
			fractions,
			asset: asset_id,
			beneficiary: 2,
		}));

		let nft_id = nft_id + 1;
		assert_noop!(
			NftFractions::fractionalize(
				RuntimeOrigin::signed(1),
				nft_collection_id,
				nft_id,
				asset_id,
				2,
				fractions,
			),
			Error::<Test>::NftNotFound
		);

		assert_ok!(Nfts::mint(RuntimeOrigin::signed(1), nft_collection_id, nft_id, 2, None));
		assert_noop!(
			NftFractions::fractionalize(
				RuntimeOrigin::signed(1),
				nft_collection_id,
				nft_id,
				asset_id,
				2,
				fractions,
			),
			Error::<Test>::NoPermission
		);
	});
}

#[test]
fn unify_should_work() {
	new_test_ext().execute_with(|| {
		let nft_collection_id = 0;
		let nft_id = 0;
		let asset_id = 0;
		let fractions = 1000;

		Balances::make_free_balance_be(&1, 100);
		Balances::make_free_balance_be(&2, 100);

		assert_ok!(Nfts::force_create(RuntimeOrigin::root(), 1, CollectionConfig::default()));
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(1), nft_collection_id, nft_id, 1, None));
		assert_ok!(NftFractions::fractionalize(
			RuntimeOrigin::signed(1),
			nft_collection_id,
			nft_id,
			asset_id,
			2,
			fractions,
		));

		assert_noop!(
			NftFractions::unify(
				RuntimeOrigin::signed(2),
				nft_collection_id + 1,
				nft_id,
				asset_id,
				1,
			),
			Error::<Test>::DataNotFound
		);
		assert_noop!(
			NftFractions::unify(
				RuntimeOrigin::signed(2),
				nft_collection_id,
				nft_id,
				asset_id + 1,
				1,
			),
			Error::<Test>::DataNotFound
		);

		// can't unify the asset a user doesn't hold
		assert_noop!(
			NftFractions::unify(RuntimeOrigin::signed(1), nft_collection_id, nft_id, asset_id, 1),
			DispatchError::Module(ModuleError {
				index: 2,
				error: [1, 0, 0, 0],
				message: Some("NoAccount")
			})
		);

		assert_ok!(NftFractions::unify(
			RuntimeOrigin::signed(2),
			nft_collection_id,
			nft_id,
			asset_id,
			1,
		));

		assert_eq!(Assets::balance(asset_id, 2), 0);
		assert_eq!(Nfts::owner(nft_collection_id, nft_id), Some(1));
		assert!(!NftToAsset::<Test>::contains_key((&nft_collection_id, &nft_id)));

		assert!(events().contains(&Event::<Test>::NftUnified {
			nft_collection: nft_collection_id,
			nft: nft_id,
			asset: asset_id,
			beneficiary: 1,
		}));

		// validate we need to hold the full balance to un-fractionalize the NFT
		let asset_id = asset_id + 1;
		assert_ok!(NftFractions::fractionalize(
			RuntimeOrigin::signed(1),
			nft_collection_id,
			nft_id,
			asset_id,
			1,
			fractions,
		));
		assert_ok!(Assets::transfer(RuntimeOrigin::signed(1), asset_id, 2, 1));
		assert_eq!(Assets::balance(asset_id, 1), fractions - 1);
		assert_eq!(Assets::balance(asset_id, 2), 1);
		assert_noop!(
			NftFractions::unify(RuntimeOrigin::signed(1), nft_collection_id, nft_id, asset_id, 1),
			DispatchError::Module(ModuleError {
				index: 2,
				error: [0, 0, 0, 0],
				message: Some("BalanceLow")
			})
		);

		assert_ok!(Assets::transfer(RuntimeOrigin::signed(2), asset_id, 1, 1));
		assert_ok!(NftFractions::unify(
			RuntimeOrigin::signed(1),
			nft_collection_id,
			nft_id,
			asset_id,
			2,
		));
		assert_eq!(Nfts::owner(nft_collection_id, nft_id), Some(2));
	});
}
