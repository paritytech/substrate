// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Extended System Tests for Balances and Assets interactions

#![cfg(test)]

use super::mock::*;

use frame_support::{
	assert_ok, assert_noop,
	traits::{Currency, ExistenceRequirement::AllowDeath},
	dispatch::Dispatchable,
};
use sp_runtime::traits::Zero;

use pallet_assets::Call as AssetsCall;
use pallet_balances::Error as BalancesError;

const ASSET_OWNER: u64 = 1337;

fn setup_asset(id: u32, zombies: u32, min_balance: u64) {
	let force_create_call = Call::Assets(
		AssetsCall::<Test>::force_create(id, ASSET_OWNER, zombies, min_balance)
	);
	assert_ok!(force_create_call.dispatch(Origin::root()));
}

fn mint_asset(id: u32, who: u64, amount: u64) {
	let mint_call = Call::Assets(
		AssetsCall::<Test>::mint(id, who, amount)
	);
	assert_ok!(mint_call.dispatch(Origin::signed(ASSET_OWNER)));
}

fn transfer_asset(id: u32, from: u64, to: u64, amount: u64) {
	let mint_call = Call::Assets(
		AssetsCall::<Test>::transfer(id, to, amount)
	);
	assert_ok!(mint_call.dispatch(Origin::signed(from)));
}

fn account_is_dead(who: u64) -> bool {
	!System::account_exists(&who) &&
	System::providers(&who).is_zero() &&
	System::consumers(&who).is_zero() &&
	Balances::total_balance(&who).is_zero()
}

#[test]
fn lifecycle_scenarios_work() {
	new_test_ext().execute_with(|| {
		let who = 1;
		setup_asset(1, 2, 10);
		assert_eq!(Assets::zombie_allowance(1), 2);

		// Account starts totally dead
		assert!(account_is_dead(who));

		// Mint Asset to user, they have no balance
		mint_asset(1, who, 100);

		// Account has no native balance, so does not exist.
		assert!(account_is_dead(who));
		// But as a zombie they have tracked asset balance.
		assert_eq!(Assets::balance(1, who), 100);
		assert_eq!(Assets::zombie_allowance(1), 1);

		// Account later gets a balance
		Balances::make_free_balance_be(&1, 1_000);

		// Account now exists in the system, but is still a zombie.
		assert!(System::account_exists(&who));
		assert_eq!(System::providers(&who), 1);

		// No consumer yet
		assert_eq!(System::consumers(&who), 0);

		// Account needs to transfer to dezombify
		transfer_asset(1, who, 2, 10);

		// Now has consumer counter
		assert_eq!(System::consumers(&who), 1);

		// Zombie allowance should stay at 1 since new zombie is added
		// but account is also dezombified.
		assert_eq!(Assets::zombie_allowance(1), 1);

		// One more transfer to fill up zombie slots.
		transfer_asset(1, who, 3, 10);
		assert_eq!(Assets::zombie_allowance(1), 0);

		// Account cannot be killed because of active consumers. It even ignores `AllowDeath`.
		assert_noop!(
			<Balances as Currency<_>>::transfer(&who, &2, 1_000, AllowDeath),
			BalancesError::<Test, _>::KeepAlive,
		);

		// User transfers all their tokens away, removing their reference
		transfer_asset(1, who, 2, 80);
		assert_eq!(System::consumers(&who), 0);

		// Now killing transfer works
		assert_ok!(<Balances as Currency<_>>::transfer(&who, &2, 1_000, AllowDeath));
		// Account is totally dead
		assert!(account_is_dead(who));

		// Give life to account 3
		Balances::make_free_balance_be(&3, 1_000);

		// Two zombies still in the system. One simple transfer should fix that.
		assert_eq!(Assets::zombie_allowance(1), 0);
		transfer_asset(1, 2, 3, 10);
		assert_eq!(Assets::zombie_allowance(1), 1);
		// TODO: dezombify only happens in one direction... Should happen in both directions I think.
		transfer_asset(1, 3, 2, 10);
		assert_eq!(Assets::zombie_allowance(1), 2);
	});
}
