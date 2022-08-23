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

//! Tests for pallet-example-basic.

use super::*;
use crate::{mock::*, Event};
use frame_election_provider_support::{ElectionProvider, SortedListProvider, Support};
use frame_support::{
	assert_noop, assert_ok, assert_storage_noop, bounded_vec,
	dispatch::WithPostDispatchInfo,
	pallet_prelude::*,
	traits::{Currency, Get, ReservableCurrency},
	weights::{extract_actual_weight, GetDispatchInfo},
};
use pallet_balances::Error as BalancesError;
use pallet_nomination_pools::{
	BondedPool, BondedPools, LastPoolId, PoolId, PoolRoles, RewardPools,
};
use pallet_staking::RewardDestination;

use sp_runtime::{
	assert_eq_error_rate,
	traits::{BadOrigin, Dispatchable, Zero},
	Perbill, Percent,
};
use sp_staking::{
	offence::{DisableStrategy, OffenceDetails, OnOffenceHandler},
	SessionIndex, StakingInterface,
};
use sp_std::prelude::*;
use substrate_test_utils::assert_eq_uvec;

pub const DEFAULT_ROLES: PoolRoles<AccountId> =
	PoolRoles { depositor: 10, root: Some(900), nominator: Some(901), state_toggler: Some(902) };

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(BondedPools::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(Staking::bonding_duration(), 3);
		let last_pool = LastPoolId::<Runtime>::get();
		assert_eq!(last_pool, 1);
	})
}

#[test]
fn cannot_register_if_not_bonded() {
	new_test_ext().execute_with(|| {
		let stash = 1;
		let ctrl = 2;
		// Mint accounts 1 and 2 with 200 tokens.
		for i in [stash, ctrl] {
			let _ = Balances::make_free_balance_be(&1, 200);
		}
		// Attempt to fast unstake.
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(1), Some(1_u32)),
			Error::<Runtime>::NotController
		);
	});
}

#[test]
fn register_works() {
	new_test_ext().execute_with(|| {
		let stash = 1;
		let ctrl = 2;
		// Mint accounts 1 and 2 with 200 tokens.
		for i in [stash, ctrl] {
			let _ = Balances::make_free_balance_be(&1, 200);
		}
		// Account 1 bonds 200 tokens (stash) with account 2 as the controller.
		assert_ok!(Staking::bond(Origin::signed(1), 2, 100, RewardDestination::Controller));

		// Stash nominates a validator
		assert_ok!(Staking::nominate(Origin::signed(ctrl), vec![3_u128]));

		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32)));
	});
}

#[test]
fn cannot_register_if_in_queue() {
	new_test_ext().execute_with(|| {});
}

#[test]
fn cannot_register_if_head() {
	new_test_ext().execute_with(|| {});
}

#[test]
fn cannot_register_if_has_unlocking_chunks() {
	new_test_ext().execute_with(|| {});
}

#[test]
fn deregister_works() {
	new_test_ext().execute_with(|| {});
}

#[test]
fn control_works() {
	new_test_ext().execute_with(|| {});
}

#[test]
fn unstake_paused_mid_election() {
	new_test_ext().execute_with(|| {
		todo!(
			"a dude is being unstaked, midway being checked, election happens, they are still not
	exposed, but a new era needs to be checked, therefore this unstake takes longer than
	expected."
		)
	});
}
