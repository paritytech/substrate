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

use crate::{mock::*};
use frame_support::{assert_ok};
use pallet_nfts::{CollectionConfig, CollectionSetting, MintSettings, CollectionSettings, CollectionAccount, Account};

type AccountIdOf<Test> = <Test as frame_system::Config>::AccountId;
fn account(id: u8) -> AccountIdOf<Test> {
	[id; 32].into()
}

/// Basic test to check that the extrinsics of the NFT pallet can be executed
#[test]
fn basic_nft_minting_should_work() {
	new_test_ext().execute_with(|| {
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
		assert_ok!(Nfts::mint(RuntimeOrigin::signed(account(1)), 0, 42, account(1), None));
        let mut items: Vec<_> = Account::<Test>::iter().map(|x| x.0).collect();
	    items.sort();
		assert_eq!(items, vec![(account(1), 0, 42)]);
	});
}
