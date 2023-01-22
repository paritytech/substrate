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
use sp_runtime::{DispatchError, ModuleError};

use frame_support::{assert_noop, assert_ok, traits::fungibles::InspectEnumerable};

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let mock::RuntimeEvent::Dex(inner) = e { Some(inner) } else { None })
		.collect();

	System::reset_events();

	result
}

fn pools() -> Vec<PoolIdOf<Test>> {
	let mut s: Vec<_> = Pools::<Test>::iter().map(|x| x.0).collect();
	s.sort();
	s
}

fn assets() -> Vec<MultiAssetId<u32>> {
	// if the storage would be public:
	// let mut s: Vec<_> = pallet_assets::pallet::Asset::<Test>::iter().map(|x| x.0).collect();
	let mut s: Vec<_> = <<Test as Config>::Assets>::asset_ids()
		.map(|id| MultiAssetId::Asset(id))
		.collect();
	s.sort();
	s
}

fn pool_assets() -> Vec<u32> {
	// if the storage would be public:
	// let mut s: Vec<_> = pallet_assets::pallet::PoolAsset::<Test>::iter().map(|x| x.0).collect();
	let mut s: Vec<_> = <<Test as Config>::PoolAssets>::asset_ids().collect();
	s.sort();
	s
}

fn create_tokens(owner: u64, tokens: Vec<MultiAssetId<u32>>) {
	for token_id in tokens {
		if let MultiAssetId::Asset(token_id) = token_id {
			assert_ok!(Assets::force_create(RuntimeOrigin::root(), token_id, owner, true, 1));
		}
	}
}

fn balance(owner: u64, token_id: MultiAssetId<u32>) -> u64 {
	match token_id {
		MultiAssetId::Native => <<Test as Config>::Currency>::free_balance(owner),
		MultiAssetId::Asset(token_id) => <<Test as Config>::Assets>::balance(token_id, owner),
	}
}

fn pool_balance(owner: u64, token_id: u32) -> u64 {
	<<Test as Config>::PoolAssets>::balance(token_id, owner)
}

macro_rules! bvec {
	($( $x:tt )*) => {
		vec![$( $x )*].try_into().unwrap()
	}
}

#[test]
fn check_u64() {
	new_test_ext().execute_with(|| {
		assert_eq!(Dex::quote(&3u64, &u64::MAX, &u64::MAX).ok().unwrap(), 3);
		assert!(Dex::quote(&u64::MAX, &3u64, &u64::MAX).is_err());
		assert_eq!(Dex::quote(&u64::MAX, &u64::MAX, &1u64).ok().unwrap(), 1);

		assert_eq!(Dex::get_amount_out(&100u64, &u64::MAX, &u64::MAX).ok().unwrap(), 99);
		assert_eq!(Dex::get_amount_in(&100u64, &u64::MAX, &u64::MAX).ok().unwrap(), 101);
	});
}

#[test]
fn can_create_pool() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);

		let lp_token: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_1));
		assert_eq!(lp_token + 1, Dex::get_next_pool_asset_id());

		assert_eq!(events(), [Event::<Test>::PoolCreated { creator: user, pool_id, lp_token }]);
		assert_eq!(pools(), vec![pool_id]);
		assert_eq!(assets(), vec![token_2]);
		assert_eq!(pool_assets(), vec![lp_token]);

		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_1),
			Error::<Test>::EqualAssets
		);
		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_2),
			Error::<Test>::EqualAssets
		);
		let token_1 = MultiAssetId::Asset(1);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		AllowMultiAssetPools::set(&false);
		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2),
			Error::<Test>::PoolMustContainNativeCurrency
		);
	});
}

#[test]
fn create_same_pool_twice_should_fail() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);

		let lp_token: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_1));
		let expected_free = lp_token + 1;
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());

		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_1),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());

		// Try switching the same tokens around:
		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());
	});
}

#[test]
fn different_pools_should_have_different_lp_tokens() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let token_3 = MultiAssetId::Asset(3);
		let pool_id_1_2 = (token_1, token_2);
		let pool_id_1_3 = (token_1, token_3);

		create_tokens(user, vec![token_2]);

		let lp_token2_1: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_1));
		let lp_token3_1: u32 = Dex::get_next_pool_asset_id();

		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_2,
				lp_token: lp_token2_1
			}]
		);

		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_3, token_1));
		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_3,
				lp_token: lp_token3_1
			}]
		);

		assert_ne!(lp_token2_1, lp_token3_1);
	});
}

#[test]
fn can_add_liquidity() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		let lp_token = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10,
			10,
			10,
			10,
			user,
			false
		));

		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: 10,
			amount2_provided: 10,
			lp_token,
			lp_token_minted: 9,
		}));

		let pallet_account = Dex::get_pool_account(pool_id);
		assert_eq!(balance(pallet_account, token_1), 10);
		assert_eq!(balance(pallet_account, token_2), 10);
		assert_eq!(pool_balance(user, lp_token), 9);
	});
}

#[test]
fn add_tiny_liquidity_leads_to_insufficient_liquidity_minted_error() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_noop!(
			Dex::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				1,
				1,
				1,
				1,
				user,
				false
			),
			Error::<Test>::InsufficientLiquidityMinted
		);
	});
}

#[test]
fn can_remove_liquidity() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		let lp_token = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10,
			10,
			10,
			10,
			user,
			false
		));

		assert_ok!(Dex::remove_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			9,
			0,
			0,
			user,
		));

		assert!(events().contains(&Event::<Test>::LiquidityRemoved {
			who: user,
			withdraw_to: user,
			pool_id,
			amount1: 9,
			amount2: 9,
			lp_token,
			lp_token_burned: 9,
		}));

		let pallet_account = Dex::get_pool_account(pool_id);
		assert_eq!(balance(pallet_account, token_1), 1);
		assert_eq!(balance(pallet_account, token_2), 1);
		assert_eq!(pool_balance(pallet_account, lp_token), 1);

		assert_eq!(balance(user, token_1), 999);
		assert_eq!(balance(user, token_2), 999);
		assert_eq!(pool_balance(user, lp_token), 0);
	});
}

#[test]
fn can_not_redeem_more_lp_tokens_than_were_minted() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			10,
			10,
			10,
			10,
			user,
			false
		));

		// Only 9 lp_tokens_minted

		assert_noop!(
			Dex::remove_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				9 + 1, // Try and redeem 10 lp tokens while only 9 minted.
				0,
				0,
				user,
			),
			DispatchError::Module(ModuleError {
				index: 3,
				error: [0; 4],
				message: Some("BalanceLow")
			})
		);
	});
}

#[test]
fn can_quote_price() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			1000,
			20,
			1,
			1,
			user,
			false
		));

		assert_eq!(Dex::quote_price_exact_tokens_for_tokens(None, Some(2), 3000, false), Some(60));
		// Check it still gives same price:
		// (if the above accidentally exchanged then it would not give same quote as before) 
		assert_eq!(Dex::quote_price_exact_tokens_for_tokens(None, Some(2), 3000, false), Some(60));

		// Check inverse:
		assert_eq!(Dex::quote_price_exact_tokens_for_tokens(Some(2), None, 60, false), Some(3000));
	});
}

#[test]
fn can_swap_with_native() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			false
		));

		let input_amount = 10;
		let expect_receive =
			Dex::get_amount_out(&input_amount, &liquidity2, &liquidity1).ok().unwrap();

		assert_ok!(Dex::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_2, token_1],
			input_amount,
			1,
			user,
			false
		));

		let pallet_account = Dex::get_pool_account(pool_id);
		assert_eq!(balance(user, token_1), expect_receive);
		assert_eq!(balance(pallet_account, token_1), liquidity1 - expect_receive);
		assert_eq!(balance(pallet_account, token_2), liquidity2 + input_amount);
	});
}

#[test]
fn can_swap_with_realistic_values() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let dot = MultiAssetId::Native;
		let usd = MultiAssetId::Asset(2);

		create_tokens(user, vec![usd]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), dot, usd));

		const UNIT: u64 = 1_000_000_000;

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 300_000 * UNIT, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1_100_000 * UNIT));

		let liquidity_dot = 200_000 * UNIT; // ratio for a 5$ price
		let liquidity_usd = 1_000_000 * UNIT;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			dot,
			usd,
			liquidity_dot,
			liquidity_usd,
			1,
			1,
			user,
			false
		));

		let input_amount = 10 * UNIT; // usd

		assert_ok!(Dex::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![usd, dot],
			input_amount,
			1,
			user,
			false
		));

		assert!(events().contains(&Event::<Test>::SwapExecuted {
			who: user,
			send_to: user,
			path: bvec![usd, dot],
			amount_in: 10 * UNIT,      // usd
			amount_out: 1_993_980_120  // About 2 dot after div by UNIT.
		}));
	});
}

#[test]
fn add_liquidity_causes_below_existential_deposit_but_keep_alive_set() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_noop!(
			Dex::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_2,
				liquidity1,
				liquidity2,
				1,
				1,
				user,
				true // keep_alive set so user account doesn't get reaped.
			),
			DispatchError::Module(ModuleError {
				index: 1,
				error: [4, 0, 0, 0],
				message: Some("KeepAlive")
			})
		);
	});
}

#[test]
fn can_not_swap_in_pool_with_no_liquidity_added_yet() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		// Check can't swap an empty pool
		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				10,
				1,
				user,
				false
			),
			Error::<Test>::PoolNotFound
		);
	});
}

#[test]
fn check_no_panic_when_try_swap_close_to_empty_pool() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);
		let lp_token = Dex::get_next_pool_asset_id();
		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			false
		));

		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: liquidity1,
			amount2_provided: liquidity2,
			lp_token,
			lp_token_minted: 140,
		}));

		let pallet_account = Dex::get_pool_account(pool_id);

		assert_eq!(balance(pallet_account, token_1), 1000);

		assert_ok!(Dex::remove_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			140,
			992, // min1
			19,  // min2
			user
		));

		// Now pool should exist but be almost empty.
		// Let's try and drain it.
		assert_eq!(balance(pallet_account, token_1), 8);

		assert_ok!(Dex::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_2, token_1],
			20,
			7,
			user,
			false
		));

		assert_eq!(balance(pallet_account, token_1), 1);

		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				20,
				1,
				user,
				false
			),
			Error::<Test>::InsufficientOutputAmount
		); // The price for the last one is very high.
	});
}

#[test]
fn swap_should_not_work_with_if_too_much_slippage() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			false
		));

		let exchange_amount = 10;

		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_2, token_1],
				exchange_amount,
				333, // amount out min
				user,
				false
			),
			Error::<Test>::InsufficientOutputAmount
		);
	});
}

#[test]
fn can_swap_tokens_for_exact_tokens() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);
		let pallet_account = Dex::get_pool_account(pool_id);
		let base1 = 1000;

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, base1 + 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let before1 = balance(pallet_account, token_1) + balance(user, token_1);
		let before2 = balance(pallet_account, token_2) + balance(user, token_2);

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			true
		));

		assert_eq!(balance(user, token_1), 1000);
		assert_eq!(balance(user, token_2), 980);

		let exchange_out2 = 1;

		let expect_in1 = Dex::get_amount_in(&exchange_out2, &liquidity1, &liquidity2).ok().unwrap();

		assert_ok!(Dex::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2],
			exchange_out2, // amount_out
			100,           // amount_in_max
			user,
			true
		));

		assert_eq!(balance(user, token_1), 1000 - expect_in1);
		assert_eq!(balance(pallet_account, token_1), liquidity1 + expect_in1);
		assert_eq!(balance(user, token_2), 1000 - 20 + exchange_out2);
		assert_eq!(balance(pallet_account, token_2), liquidity2 - exchange_out2);

		// check invariants:

		// dot and asset totals should be preserved.
		assert_eq!(before1, balance(pallet_account, token_1) + balance(user, token_1));
		assert_eq!(before2, balance(pallet_account, token_2) + balance(user, token_2));
	});
}

#[test]
fn can_swap_tokens_for_exact_tokens_when_not_liquidity_provider() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let user2 = 2;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let pool_id = (token_1, token_2);
		let pallet_account = Dex::get_pool_account(pool_id);
		let base1 = 1000;

		create_tokens(user2, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user2), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, base1, 0));
		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user2, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user2), 2, user2, 1000));

		let before1 =
			balance(pallet_account, token_1) + balance(user, token_1) + balance(user2, token_1);
		let before2 =
			balance(pallet_account, token_2) + balance(user, token_2) + balance(user2, token_2);

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user2,
			false
		));

		assert_eq!(balance(user, token_1), 1000);
		assert_eq!(balance(user, token_2), 0);

		let exchange_out2 = 1;

		let expect_in1 = Dex::get_amount_in(&exchange_out2, &liquidity1, &liquidity2).ok().unwrap();

		assert_ok!(Dex::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2],
			exchange_out2,
			100, // amount_in_max
			user,
			true
		));

		assert_eq!(balance(user, token_1), 1000 - expect_in1);
		assert_eq!(balance(pallet_account, token_1), liquidity1 + expect_in1);
		assert_eq!(balance(user, token_2), exchange_out2);
		assert_eq!(balance(pallet_account, token_2), liquidity2 - exchange_out2);

		// check invariants:

		// dot and asset totals should be preserved.
		assert_eq!(
			before1,
			balance(pallet_account, token_1) + balance(user, token_1) + balance(user2, token_1)
		);
		assert_eq!(
			before2,
			balance(pallet_account, token_2) + balance(user, token_2) + balance(user2, token_2)
		);

		assert_ok!(Dex::remove_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			9,
			0,
			0,
			user2,
		));

		// assert_eq!(balance(user2, token_1), 67);
		// assert_eq!(balance(user2, token_2), 981);
	});
}

#[test]
fn swap_when_existential_deposit_would_cause_reaping_but_keep_alive_set() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let user2 = 2;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);

		create_tokens(user2, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user2), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1, 0));
		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user2, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user2), 2, user2, 2000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user2),
			token_1,
			token_2,
			1000,
			2000,
			1,
			1,
			user2,
			false
		));

		assert_noop!(
			Dex::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				1,
				1, // amount_in_min
				user,
				true
			),
			DispatchError::Module(ModuleError {
				index: 1,
				error: [4, 0, 0, 0],
				message: Some("KeepAlive")
			})
		);

		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				1,
				1, // amount_in_min
				user,
				true
			),
			DispatchError::Module(ModuleError {
				index: 1,
				error: [4, 0, 0, 0],
				message: Some("KeepAlive")
			})
		);
	});
}

#[test]
fn swap_tokens_for_exact_tokens_should_not_work_if_too_much_slippage() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let base1 = 1000;

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, base1 + 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			true
		));
		let exchange_out2 = 1;

		assert_noop!(
			Dex::swap_tokens_for_exact_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_2],
				exchange_out2,
				52, // amount_in_max just greater than slippage.
				user,
				true
			),
			Error::<Test>::ExcessiveInputAmount
		);
	});
}

#[test]
fn swap_exact_tokens_for_tokens_in_multi_hops() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let token_3 = MultiAssetId::Asset(3);
		let base1 = 10000;

		create_tokens(user, vec![token_2, token_3]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_3));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, base1 + 10000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 10000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, 10000));

		let liquidity1 = 10000;
		let liquidity2 = 200;
		let liquidity3 = 2000;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			true
		));
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			token_3,
			liquidity2,
			liquidity3,
			1,
			1,
			user,
			true
		));

		let input_amount = 500;
		let expect_out2 =
			Dex::get_amount_out(&input_amount, &liquidity1, &liquidity2).ok().unwrap();
		let expect_out3 = Dex::get_amount_out(&expect_out2, &liquidity2, &liquidity3).ok().unwrap();

		assert_ok!(Dex::swap_exact_tokens_for_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2, token_3],
			input_amount, // amount_in
			80,           // amount_out_min
			user,
			true
		));

		let pool_id1 = (token_1, token_2);
		let pool_id2 = (token_2, token_3);
		let pallet_account1 = Dex::get_pool_account(pool_id1);
		let pallet_account2 = Dex::get_pool_account(pool_id2);

		assert_eq!(balance(user, token_1), base1 - input_amount);
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
		let token_1 = MultiAssetId::Native;
		let token_2 = MultiAssetId::Asset(2);
		let token_3 = MultiAssetId::Asset(3);
		let base1 = 10000;

		create_tokens(user, vec![token_2, token_3]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_1, token_2));
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2, token_3));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, base1 + 10000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 2, user, 10000));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 3, user, 10000));

		let liquidity1 = 10000;
		let liquidity2 = 200;
		let liquidity3 = 2000;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_1,
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			true
		));
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			token_3,
			liquidity2,
			liquidity3,
			1,
			1,
			user,
			true
		));

		let exchange_out3 = 100;
		let expect_in2 = Dex::get_amount_in(&exchange_out3, &liquidity2, &liquidity3).ok().unwrap();
		let expect_in1 = Dex::get_amount_in(&expect_in2, &liquidity1, &liquidity2).ok().unwrap();

		assert_ok!(Dex::swap_tokens_for_exact_tokens(
			RuntimeOrigin::signed(user),
			bvec![token_1, token_2, token_3],
			exchange_out3,
			1000, // amount_in_max
			user,
			true
		));

		let pool_id1 = (token_1, token_2);
		let pool_id2 = (token_2, token_3);
		let pallet_account1 = Dex::get_pool_account(pool_id1);
		let pallet_account2 = Dex::get_pool_account(pool_id2);

		assert_eq!(balance(user, token_1), base1 - expect_in1);
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
		let token_1 = MultiAssetId::Asset(1);

		create_tokens(user, vec![token_1]);
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), 1, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_noop!(
			Dex::add_liquidity(
				RuntimeOrigin::signed(user),
				token_1,
				token_1,
				liquidity1,
				liquidity2,
				1,
				1,
				user,
				true
			),
			Error::<Test>::PoolNotFound
		);

		let exchange_amount = 10;
		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![token_1, token_1],
				exchange_amount,
				1,
				user,
				true
			),
			Error::<Test>::PoolNotFound
		);

		assert_noop!(
			Dex::swap_exact_tokens_for_tokens(
				RuntimeOrigin::signed(user),
				bvec![MultiAssetId::Native, MultiAssetId::Native],
				exchange_amount,
				1,
				user,
				true
			),
			Error::<Test>::PoolNotFound
		);
	});
}
