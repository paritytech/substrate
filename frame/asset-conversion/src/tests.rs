// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{mock::*, *};
use frame_support::{
	assert_noop, assert_ok,
	instances::Instance1,
	traits::{fungible::Inspect, fungibles::InspectEnumerable, Get},
};
use sp_arithmetic::Permill;
use sp_runtime::{DispatchError, TokenError};

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let mock::RuntimeEvent::AssetConversion(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect();

	System::reset_events();

	result
}

fn pools() -> Vec<PoolIdOf<Test>> {
	let mut s: Vec<_> = Pools::<Test>::iter().map(|x| x.0).collect();
	s.sort();
	s
}

fn assets() -> Vec<NativeOrAssetId<u32>> {
	// if the storage would be public:
	// let mut s: Vec<_> = pallet_assets::pallet::Asset::<Test>::iter().map(|x| x.0).collect();
	let mut s: Vec<_> = <<Test as Config>::Assets>::asset_ids()
		.map(|id| NativeOrAssetId::Asset(id))
		.collect();
	s.sort();
	s
}

fn pool_assets() -> Vec<u32> {
	let mut s: Vec<_> = <<Test as Config>::PoolAssets>::asset_ids().collect();
	s.sort();
	s
}

fn create_tokens(owner: u128, tokens: Vec<NativeOrAssetId<u32>>) {
	for token_id in tokens {
		let MultiAssetIdConversionResult::Converted(asset_id) =
			NativeOrAssetIdConverter::try_convert(&token_id)
		else {
			unreachable!("invalid token")
		};
		assert_ok!(Assets::force_create(RuntimeOrigin::root(), asset_id, owner, false, 1));
	}
}

fn balance(owner: u128, token_id: NativeOrAssetId<u32>) -> u128 {
	match token_id {
		NativeOrAssetId::Native => <<Test as Config>::Currency>::free_balance(owner),
		NativeOrAssetId::Asset(token_id) => <<Test as Config>::Assets>::balance(token_id, owner),
	}
}

fn pool_balance(owner: u128, token_id: u32) -> u128 {
	<<Test as Config>::PoolAssets>::balance(token_id, owner)
}

fn get_ed() -> u128 {
	<<Test as Config>::Currency>::minimum_balance()
}

macro_rules! bvec {
	($( $x:tt )*) => {
		vec![$( $x )*].try_into().unwrap()
	}
}

#[test]
fn check_pool_accounts_dont_collide() {
	use std::collections::HashSet;
	let mut map = HashSet::new();

	for i in 0..1_000_000u32 {
		let account = AssetConversion::get_pool_account(&(
			NativeOrAssetId::Native,
			NativeOrAssetId::Asset(i),
		));
		if map.contains(&account) {
			panic!("Collision at {}", i);
		}
		map.insert(account);
	}
}

#[test]
fn check_max_numbers() {
	new_test_ext().execute_with(|| {
		assert_eq!(AssetConversion::quote(&3u128, &u128::MAX, &u128::MAX).ok().unwrap(), 3);
		assert!(AssetConversion::quote(&u128::MAX, &3u128, &u128::MAX).is_err());
		assert_eq!(AssetConversion::quote(&u128::MAX, &u128::MAX, &1u128).ok().unwrap(), 1);

		assert_eq!(
			AssetConversion::get_amount_out(&100u128, &u128::MAX, &u128::MAX).ok().unwrap(),
			99
		);
		assert_eq!(
			AssetConversion::get_amount_in(&100u128, &u128::MAX, &u128::MAX).ok().unwrap(),
			101
		);
	});
}

#[test]
fn can_create_pool() {
	new_test_ext().execute_with(|| {
		let asset_account_deposit: u128 =
			<mock::Test as pallet_assets::Config<Instance1>>::AssetAccountDeposit::get();
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);

		let lp_token = AssetConversion::get_next_pool_asset_id();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 1000));
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_1));

		let setup_fee = <<Test as Config>::PoolSetupFee as Get<<Test as Config>::Balance>>::get();
		let pool_account = <<Test as Config>::PoolSetupFeeReceiver as Get<u128>>::get();
		assert_eq!(
			balance(user, NativeOrAssetId::Native),
			1000 - (setup_fee + asset_account_deposit)
		);
		assert_eq!(balance(pool_account, NativeOrAssetId::Native), setup_fee);
		assert_eq!(lp_token + 1, AssetConversion::get_next_pool_asset_id());

		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id,
				pool_account: AssetConversion::get_pool_account(&pool_id),
				lp_token
			}]
		);
		assert_eq!(pools(), vec![pool_id]);
		assert_eq!(assets(), vec![token_2]);
		assert_eq!(pool_assets(), vec![lp_token]);

		assert_noop!(
			AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_1),
			Error::<Test>::EqualAssets
		);
		assert_noop!(
			AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_2),
			Error::<Test>::EqualAssets
		);

		// validate we can create Asset(1)/Asset(2) pool
		let token_1 = NativeOrAssetId::Asset(1);
		create_tokens(user, vec![token_1]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		// validate we can force the first asset to be the Native currency only
		AllowMultiAssetPools::set(&false);
		let token_1 = NativeOrAssetId::Asset(3);
		assert_noop!(
			AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2),
			Error::<Test>::PoolMustContainNativeCurrency
		);
	});
}

#[test]
fn create_same_pool_twice_should_fail() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);

		let lp_token = AssetConversion::get_next_pool_asset_id();
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_1));
		let expected_free = lp_token + 1;
		assert_eq!(expected_free, AssetConversion::get_next_pool_asset_id());

		assert_noop!(
			AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_1),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, AssetConversion::get_next_pool_asset_id());

		// Try switching the same tokens around:
		assert_noop!(
			AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, AssetConversion::get_next_pool_asset_id());
	});
}

#[test]
fn different_pools_should_have_different_lp_tokens() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let token_3 = NativeOrAssetId::Asset(3);
		let pool_id_1_2 = (token_1, token_2);
		let pool_id_1_3 = (token_1, token_3);

		create_tokens(user, vec![token_2, token_3]);

		let lp_token2_1 = AssetConversion::get_next_pool_asset_id();
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_1));
		let lp_token3_1 = AssetConversion::get_next_pool_asset_id();

		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_2,
				pool_account: AssetConversion::get_pool_account(&pool_id_1_2),
				lp_token: lp_token2_1
			}]
		);

		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_3, token_1));
		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_3,
				pool_account: AssetConversion::get_pool_account(&pool_id_1_3),
				lp_token: lp_token3_1,
			}]
		);

		assert_ne!(lp_token2_1, lp_token3_1);
	});
}

#[test]
fn can_add_liquidity() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let token_3 = NativeOrAssetId::Asset(3);

		create_tokens(user, vec![token_2, token_3]);
		let lp_token1 = AssetConversion::get_next_pool_asset_id();
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		let lp_token2 = AssetConversion::get_next_pool_asset_id();
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_3));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 * 2 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, 1000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10000,
			10,
			10000,
			10,
			user,
		));

		let pool_id = (token_1, token_2);
		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: 10000,
			amount2_provided: 10,
			lp_token: lp_token1,
			lp_token_minted: 216,
		}));
		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		assert_eq!(balance(pallet_account, token_1), 10000);
		assert_eq!(balance(pallet_account, token_2), 10);
		assert_eq!(balance(user, token_1), 10000 + ed);
		assert_eq!(balance(user, token_2), 1000 - 10);
		assert_eq!(pool_balance(user, lp_token1), 216);

		// try to pass the non-native - native assets, the result should be the same
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_3,
			token_1,
			10,
			10000,
			10,
			10000,
			user,
		));

		let pool_id = (token_1, token_3);
		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: 10000,
			amount2_provided: 10,
			lp_token: lp_token2,
			lp_token_minted: 216,
		}));
		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		assert_eq!(balance(pallet_account, token_1), 10000);
		assert_eq!(balance(pallet_account, token_3), 10);
		assert_eq!(balance(user, token_1), ed);
		assert_eq!(balance(user, token_3), 1000 - 10);
		assert_eq!(pool_balance(user, lp_token2), 216);
	});
}

#[test]
fn add_tiny_liquidity_leads_to_insufficient_liquidity_minted_error() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 1000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_noop!(
			AssetConversion::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				1,
				1,
				1,
				1,
				user
			),
			Error::<Test>::AmountOneLessThanMinimal
		);

		assert_noop!(
			AssetConversion::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				get_ed(),
				1,
				1,
				1,
				user
			),
			Error::<Test>::InsufficientLiquidityMinted
		);
	});
}

#[test]
fn add_tiny_liquidity_directly_to_pool_address() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let token_3 = NativeOrAssetId::Asset(3);

		create_tokens(user, vec![token_2, token_3]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_3));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 * 2 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, 1000));

		// check we're still able to add the liquidity even when the pool already has some token_1
		let pallet_account = AssetConversion::get_pool_account(&(token_1, token_2));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), pallet_account, 1000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10000,
			10,
			10000,
			10,
			user,
		));

		// check the same but for token_3 (non-native token)
		let pallet_account = AssetConversion::get_pool_account(&(token_1, token_3));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, pallet_account, 1));
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_3,
			10000,
			10,
			10000,
			10,
			user,
		));
	});
}

#[test]
fn can_remove_liquidity() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		let lp_token = AssetConversion::get_next_pool_asset_id();
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000000000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 100000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			1000000000,
			100000,
			1000000000,
			100000,
			user,
		));

		let total_lp_received = pool_balance(user, lp_token);
		LiquidityWithdrawalFee::set(&Permill::from_percent(10));

		assert_ok!(AssetConversion::remove_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			total_lp_received,
			0,
			0,
			user,
		));

		assert!(events().contains(&Event::<Test>::LiquidityRemoved {
			who: user,
			withdraw_to: user,
			pool_id,
			amount1: 899991000,
			amount2: 89999,
			lp_token,
			lp_token_burned: total_lp_received,
			withdrawal_fee: <Test as Config>::LiquidityWithdrawalFee::get()
		}));

		let pool_account = AssetConversion::get_pool_account(&pool_id);
		assert_eq!(balance(pool_account, token_1), 100009000);
		assert_eq!(balance(pool_account, token_2), 10001);
		assert_eq!(pool_balance(pool_account, lp_token), 100);

		assert_eq!(balance(user, token_1), 10000000000 - 1000000000 + 899991000);
		assert_eq!(balance(user, token_2), 89999);
		assert_eq!(pool_balance(user, lp_token), 0);
	});
}

#[test]
fn can_not_redeem_more_lp_tokens_than_were_minted() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let lp_token = AssetConversion::get_next_pool_asset_id();

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 + get_ed()));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10000,
			10,
			10000,
			10,
			user,
		));

		// Only 216 lp_tokens_minted
		assert_eq!(pool_balance(user, lp_token), 216);

		assert_noop!(
			AssetConversion::remove_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				216 + 1, // Try and redeem 10 lp tokens while only 9 minted.
				0,
				0,
				user,
			),
			DispatchError::Token(TokenError::FundsUnavailable)
		);
	});
}

#[test]
fn can_quote_price() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 100000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10000,
			200,
			1,
			1,
			user,
		));

		assert_eq!(
			AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Native,
				NativeOrAssetId::Asset(2),
				3000,
				false,
			),
			Some(60)
		);
		// Check it still gives same price:
		// (if the above accidentally exchanged then it would not give same quote as before)
		assert_eq!(
			AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Native,
				NativeOrAssetId::Asset(2),
				3000,
				false,
			),
			Some(60)
		);

		// Check inverse:
		assert_eq!(
			AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Asset(2),
				NativeOrAssetId::Native,
				60,
				false,
			),
			Some(3000)
		);
	});
}

#[test]
fn can_swap_with_native() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));

		let input_amount = 100;
		let expect_receive =
			AssetConversion::get_amount_out(&input_amount, &liquidity2, &liquidity1)
				.ok()
				.unwrap();

		assert_ok!(AssetConversion::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_2, token_1],
			input_amount,
			1,
			user,
			false,
		));

		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		assert_eq!(balance(user, token_1), expect_receive + ed);
		assert_eq!(balance(user, token_2), 1000 - liquidity2 - input_amount);
		assert_eq!(balance(pallet_account, token_1), liquidity1 - expect_receive);
		assert_eq!(balance(pallet_account, token_2), liquidity2 + input_amount);
	});
}

#[test]
fn can_swap_with_realistic_values() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let dot = NativeOrAssetId::Native;
		let usd = NativeOrAssetId::Asset(2);
		create_tokens(user, vec![usd]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), dot, usd));

		const UNIT: u128 = 1_000_000_000;

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 300_000 * UNIT));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1_100_000 * UNIT));

		let liquidity_dot = 200_000 * UNIT; // ratio for a 5$ price
		let liquidity_usd = 1_000_000 * UNIT;
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			dot,
			usd,
			liquidity_dot,
			liquidity_usd,
			1,
			1,
			user,
		));

		let input_amount = 10 * UNIT; // usd

		assert_ok!(AssetConversion::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![usd, dot],
			input_amount,
			1,
			user,
			false,
		));

		assert!(events().contains(&Event::<Test>::SwapExecuted {
			who: user,
			send_to: user,
			path: bvec![usd, dot],
			amount_in: 10 * UNIT,      // usd
			amount_out: 1_993_980_120, // About 2 dot after div by UNIT.
		}));
	});
}

#[test]
fn can_not_swap_in_pool_with_no_liquidity_added_yet() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		// Check can't swap an empty pool
		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				10,
				1,
				user,
				false,
			),
			Error::<Test>::PoolNotFound
		);
	});
}

#[test]
fn check_no_panic_when_try_swap_close_to_empty_pool() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);
		let lp_token = AssetConversion::get_next_pool_asset_id();

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));

		let lp_token_minted = pool_balance(user, lp_token);
		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: liquidity1,
			amount2_provided: liquidity2,
			lp_token,
			lp_token_minted,
		}));

		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		assert_eq!(balance(pallet_account, token_1), liquidity1);
		assert_eq!(balance(pallet_account, token_2), liquidity2);

		assert_ok!(AssetConversion::remove_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			lp_token_minted,
			1,
			1,
			user,
		));

		// Now, the pool should exist but be almost empty.
		// Let's try and drain it.
		assert_eq!(balance(pallet_account, token_1), 708);
		assert_eq!(balance(pallet_account, token_2), 15);

		// validate the reserve should always stay above the ED
		assert_noop!(
			AssetConversion::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				708 - ed + 1, // amount_out
				500,          // amount_in_max
				user,
				false,
			),
			Error::<Test>::ReserveLeftLessThanMinimal
		);

		assert_ok!(AssetConversion::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_2, token_1],
			608, // amount_out
			500, // amount_in_max
			user,
			false,
		));

		let token_1_left = balance(pallet_account, token_1);
		let token_2_left = balance(pallet_account, token_2);
		assert_eq!(token_1_left, 708 - 608);

		// The price for the last tokens should be very high
		assert_eq!(
			AssetConversion::get_amount_in(&(token_1_left - 1), &token_2_left, &token_1_left)
				.ok()
				.unwrap(),
			10625
		);

		assert_noop!(
			AssetConversion::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				token_1_left - 1, // amount_out
				1000,             // amount_in_max
				user,
				false,
			),
			Error::<Test>::ProvidedMaximumNotSufficientForSwap
		);

		// Try to swap what's left in the pool
		assert_noop!(
			AssetConversion::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				token_1_left, // amount_out
				1000,         // amount_in_max
				user,
				false,
			),
			Error::<Test>::AmountOutTooHigh
		);
	});
}

#[test]
fn swap_should_not_work_if_too_much_slippage() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 + get_ed()));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));

		let exchange_amount = 100;

		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				exchange_amount, // amount_in
				4000,            // amount_out_min
				user,
				false,
			),
			Error::<Test>::ProvidedMinimumNotSufficientForSwap
		);
	});
}

#[test]
fn can_swap_tokens_for_exact_tokens() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 20000 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		let before1 = balance(pallet_account, token_1) + balance(user, token_1);
		let before2 = balance(pallet_account, token_2) + balance(user, token_2);

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));

		let exchange_out = 50;
		let expect_in = AssetConversion::get_amount_in(&exchange_out, &liquidity1, &liquidity2)
			.ok()
			.unwrap();

		assert_ok!(AssetConversion::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2],
			exchange_out, // amount_out
			3500,         // amount_in_max
			user,
			true,
		));

		assert_eq!(balance(user, token_1), 10000 + ed - expect_in);
		assert_eq!(balance(user, token_2), 1000 - liquidity2 + exchange_out);
		assert_eq!(balance(pallet_account, token_1), liquidity1 + expect_in);
		assert_eq!(balance(pallet_account, token_2), liquidity2 - exchange_out);

		// check invariants:

		// native and asset totals should be preserved.
		assert_eq!(before1, balance(pallet_account, token_1) + balance(user, token_1));
		assert_eq!(before2, balance(pallet_account, token_2) + balance(user, token_2));
	});
}

#[test]
fn can_swap_tokens_for_exact_tokens_when_not_liquidity_provider() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let user2 = 2;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let pool_id = (token_1, token_2);
		let lp_token = AssetConversion::get_next_pool_asset_id();

		create_tokens(user2, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user2), token_1, token_2));

		let ed = get_ed();
		let base1 = 10000;
		let base2 = 1000;
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, base1 + ed));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user2, base1 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user2), 2, user2, base2));

		let pallet_account = AssetConversion::get_pool_account(&pool_id);
		let before1 =
			balance(pallet_account, token_1) + balance(user, token_1) + balance(user2, token_1);
		let before2 =
			balance(pallet_account, token_2) + balance(user, token_2) + balance(user2, token_2);

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user2,
		));

		assert_eq!(balance(user, token_1), base1 + ed);
		assert_eq!(balance(user, token_2), 0);

		let exchange_out = 50;
		let expect_in = AssetConversion::get_amount_in(&exchange_out, &liquidity1, &liquidity2)
			.ok()
			.unwrap();

		assert_ok!(AssetConversion::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2],
			exchange_out, // amount_out
			3500,         // amount_in_max
			user,
			true,
		));

		assert_eq!(balance(user, token_1), base1 + ed - expect_in);
		assert_eq!(balance(pallet_account, token_1), liquidity1 + expect_in);
		assert_eq!(balance(user, token_2), exchange_out);
		assert_eq!(balance(pallet_account, token_2), liquidity2 - exchange_out);

		// check invariants:

		// native and asset totals should be preserved.
		assert_eq!(
			before1,
			balance(pallet_account, token_1) + balance(user, token_1) + balance(user2, token_1)
		);
		assert_eq!(
			before2,
			balance(pallet_account, token_2) + balance(user, token_2) + balance(user2, token_2)
		);

		let lp_token_minted = pool_balance(user2, lp_token);
		assert_eq!(lp_token_minted, 1314);

		assert_ok!(AssetConversion::remove_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			lp_token_minted,
			0,
			0,
			user2,
		));
	});
}

#[test]
fn swap_when_existential_deposit_would_cause_reaping_but_keep_alive_set() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let user2 = 2;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user2, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user2), token_1, token_2));

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 101));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user2, 10000 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user2), 2, user2, 1000));

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			10000,
			200,
			1,
			1,
			user2,
		));

		assert_noop!(
			AssetConversion::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				1,   // amount_out
				101, // amount_in_max
				user,
				true,
			),
			DispatchError::Token(TokenError::NotExpendable)
		);

		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				51, // amount_in
				1,  // amount_out_min
				user,
				true,
			),
			DispatchError::Token(TokenError::NotExpendable)
		);
	});
}

#[test]
fn swap_tokens_for_exact_tokens_should_not_work_if_too_much_slippage() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 20000 + get_ed()));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 10000;
		let liquidity2 = 200;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));

		let exchange_out = 1;

		assert_noop!(
			AssetConversion::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				exchange_out, // amount_out
				50,           // amount_in_max just greater than slippage.
				user,
				true
			),
			Error::<Test>::ProvidedMaximumNotSufficientForSwap
		);
	});
}

#[test]
fn swap_exact_tokens_for_tokens_in_multi_hops() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let token_3 = NativeOrAssetId::Asset(3);

		create_tokens(user, vec![token_2, token_3]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_3));

		let ed = get_ed();
		let base1 = 10000;
		let base2 = 10000;
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, base1 * 2 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, base2));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, base2));

		let liquidity1 = 10000;
		let liquidity2 = 200;
		let liquidity3 = 2000;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			token_3,
			liquidity2,
			liquidity3,
			1,
			1,
			user,
		));

		let input_amount = 500;
		let expect_out2 = AssetConversion::get_amount_out(&input_amount, &liquidity1, &liquidity2)
			.ok()
			.unwrap();
		let expect_out3 = AssetConversion::get_amount_out(&expect_out2, &liquidity2, &liquidity3)
			.ok()
			.unwrap();

		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1],
				input_amount,
				80,
				user,
				true,
			),
			Error::<Test>::InvalidPath
		);

		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2, token_3, token_2],
				input_amount,
				80,
				user,
				true,
			),
			Error::<Test>::NonUniquePath
		);

		assert_ok!(AssetConversion::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2, token_3],
			input_amount, // amount_in
			80,           // amount_out_min
			user,
			true,
		));

		let pool_id1 = (token_1, token_2);
		let pool_id2 = (token_2, token_3);
		let pallet_account1 = AssetConversion::get_pool_account(&pool_id1);
		let pallet_account2 = AssetConversion::get_pool_account(&pool_id2);

		assert_eq!(balance(user, token_1), base1 + ed - input_amount);
		assert_eq!(balance(pallet_account1, token_1), liquidity1 + input_amount);
		assert_eq!(balance(pallet_account1, token_2), liquidity2 - expect_out2);
		assert_eq!(balance(pallet_account2, token_2), liquidity2 + expect_out2);
		assert_eq!(balance(pallet_account2, token_3), liquidity3 - expect_out3);
		assert_eq!(balance(user, token_3), 10000 - liquidity3 + expect_out3);
	});
}

#[test]
fn swap_tokens_for_exact_tokens_in_multi_hops() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);
		let token_3 = NativeOrAssetId::Asset(3);

		create_tokens(user, vec![token_2, token_3]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_2, token_3));

		let ed = get_ed();
		let base1 = 10000;
		let base2 = 10000;
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, base1 * 2 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, base2));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, base2));

		let liquidity1 = 10000;
		let liquidity2 = 200;
		let liquidity3 = 2000;

		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
		));
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			token_3,
			liquidity2,
			liquidity3,
			1,
			1,
			user,
		));

		let exchange_out3 = 100;
		let expect_in2 = AssetConversion::get_amount_in(&exchange_out3, &liquidity2, &liquidity3)
			.ok()
			.unwrap();
		let expect_in1 = AssetConversion::get_amount_in(&expect_in2, &liquidity1, &liquidity2)
			.ok()
			.unwrap();

		assert_ok!(AssetConversion::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2, token_3],
			exchange_out3, // amount_out
			1000,          // amount_in_max
			user,
			true,
		));

		let pool_id1 = (token_1, token_2);
		let pool_id2 = (token_2, token_3);
		let pallet_account1 = AssetConversion::get_pool_account(&pool_id1);
		let pallet_account2 = AssetConversion::get_pool_account(&pool_id2);

		assert_eq!(balance(user, token_1), base1 + ed - expect_in1);
		assert_eq!(balance(pallet_account1, token_1), liquidity1 + expect_in1);
		assert_eq!(balance(pallet_account1, token_2), liquidity2 - expect_in2);
		assert_eq!(balance(pallet_account2, token_2), liquidity2 + expect_in2);
		assert_eq!(balance(pallet_account2, token_3), liquidity3 - exchange_out3);
		assert_eq!(balance(user, token_3), 10000 - liquidity3 + exchange_out3);
	});
}

#[test]
fn can_not_swap_same_asset() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = NativeOrAssetId::Asset(1);

		create_tokens(user, vec![token_1]);
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 1, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_noop!(
			AssetConversion::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_1,
				liquidity1,
				liquidity2,
				1,
				1,
				user,
			),
			Error::<Test>::PoolNotFound
		);

		let exchange_amount = 10;
		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_1],
				exchange_amount,
				1,
				user,
				true,
			),
			Error::<Test>::PoolNotFound
		);

		assert_noop!(
			AssetConversion::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![NativeOrAssetId::Native, NativeOrAssetId::Native],
				exchange_amount,
				1,
				user,
				true,
			),
			Error::<Test>::PoolNotFound
		);
	});
}

#[test]
fn validate_pool_id_sorting() {
	new_test_ext().execute_with(|| {
		use crate::NativeOrAssetId::{Asset, Native};
		assert_eq!(AssetConversion::get_pool_id(Native, Asset(2)), (Native, Asset(2)));
		assert_eq!(AssetConversion::get_pool_id(Asset(2), Native), (Native, Asset(2)));
		assert_eq!(AssetConversion::get_pool_id(Native, Native), (Native, Native));
		assert_eq!(AssetConversion::get_pool_id(Asset(2), Asset(1)), (Asset(1), Asset(2)));
		assert!(Asset(2) > Asset(1));
		assert!(Asset(1) <= Asset(1));
		assert_eq!(Asset(1), Asset(1));
		assert_eq!(Native::<u32>, Native::<u32>);
		assert!(Native < Asset(1));
	});
}

#[test]
fn cannot_block_pool_creation() {
	new_test_ext().execute_with(|| {
		// User 1 is the pool creator
		let user = 1;
		// User 2 is the attacker
		let attacker = 2;

		let ed = get_ed();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), attacker, 10000 + ed));

		// The target pool the user wants to create is Native <=> Asset(2)
		let token_1 = NativeOrAssetId::Native;
		let token_2 = NativeOrAssetId::Asset(2);

		// Attacker computes the still non-existing pool account for the target pair
		let pool_account =
			AssetConversion::get_pool_account(&AssetConversion::get_pool_id(token_2, token_1));
		// And transfers the ED to that pool account
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(attacker), pool_account, ed));
		// Then, the attacker creates 14 tokens and sends one of each to the pool account
		for i in 10..25 {
			create_tokens(attacker, vec![NativeOrAssetId::Asset(i)]);
			assert_ok!(Assets::mint(RuntimeOrigin::signed(attacker), i, attacker, 1000));
			assert_ok!(Assets::transfer(RuntimeOrigin::signed(attacker), i, pool_account, 1));
		}

		// User can still create the pool
		create_tokens(user, vec![token_2]);
		assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		// User has to transfer one Asset(2) token to the pool account (otherwise add_liquidity will
		// fail with `AssetTwoDepositDidNotMeetMinimum`)
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), user, 10000 + ed));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 10000));
		assert_ok!(Assets::transfer(RuntimeOrigin::signed(user), 2, pool_account, 1));

		// add_liquidity shouldn't fail because of the number of consumers
		assert_ok!(AssetConversion::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10000,
			100,
			10000,
			10,
			user,
		));
	});
}
