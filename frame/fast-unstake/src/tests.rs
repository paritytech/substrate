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

/// Utility function to mint a stash and controller account with 200 tokens
/// and start staking: stash bonds 100 tokens and nominates account 3.
/// returns the accounts [stash, ctrl]
fn mint_and_initiate_staking() -> (AccountId, AccountId) {
	let stash = 1;
	let ctrl = 2;
	// Mint accounts 1 and 2 with 200 tokens.
	for i in [stash, ctrl] {
		let _ = Balances::make_free_balance_be(&1, 200);
	}
	// Account 1 bonds 200 tokens (stash) with account 2 as the controller.
	assert_ok!(Staking::bond(Origin::signed(1), 2, 100, RewardDestination::Controller));

	// Stash nominates a validator
	// NOTE: not sure where this validator is coming from (not an actual validator).
	assert_ok!(Staking::nominate(Origin::signed(ctrl), vec![3_u128]));

	return (stash, ctrl)
}

#[test]
fn register_works() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32)));
		// Ensure stash is in the queue.
		assert_ne!(Queue::<Runtime>::get(stash), None);
	});
}

#[test]
fn cannot_register_if_not_bonded() {
	new_test_ext().execute_with(|| {
		// Mint accounts 1 and 2 with 200 tokens.
		for i in 1..2 {
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
fn cannot_register_if_in_queue() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Insert some Queue item
		Queue::<Runtime>::insert(stash, Some(1_u32));
		// Cannot re-register, already in queue
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32)),
			Error::<Runtime>::AlreadyQueued
		);
	});
}

#[test]
fn cannot_register_if_head() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Insert some Head item for stash
		Head::<Runtime>::put(UnstakeRequest {
			stash: stash.clone(),
			checked: vec![],
			maybe_pool_id: None,
		});
		// Controller attempts to regsiter
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32)),
			Error::<Runtime>::AlreadyHead
		);
	});
}

#[test]
fn cannot_register_if_has_unlocking_chunks() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Start unbonding half of staked tokens
		assert_ok!(Staking::unbond(Origin::signed(ctrl), 50_u128));
		// Cannot regsiter for fast unstake with unlock chunks active
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32)),
			Error::<Runtime>::NotFullyBonded
		);
	});
}

#[test]
fn deregister_works() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32));
		// Controller then changes mind and deregisters.
		assert_ok!(FastUnstake::deregister(Origin::signed(ctrl)));
		// Ensure stash no longer exists in the queue.
		assert_eq!(Queue::<Runtime>::get(stash), None);
	});
}

#[test]
fn cannot_deregister_if_not_controller() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32));
		// Stash tries to deregister.
		assert_noop!(FastUnstake::deregister(Origin::signed(stash)), Error::<Runtime>::NotController);
	});
}

#[test]
fn cannot_deregister_if_not_queued() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller tries to deregister without first registering
		assert_noop!(FastUnstake::deregister(Origin::signed(ctrl)), Error::<Runtime>::NotQueued);
	});
}

#[test]
fn cannot_deregister_already_head() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller attempts to regsiter, should fail
		FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32));
		// Insert some Head item for stash.
		Head::<Runtime>::put(UnstakeRequest {
			stash: stash.clone(),
			checked: vec![],
			maybe_pool_id: None,
		});
		// Controller attempts to deregister
		assert_noop!(FastUnstake::deregister(Origin::signed(ctrl)), Error::<Runtime>::AlreadyHead);
	});
}

#[test]
fn control_works() {
	new_test_ext().execute_with(|| {
		// account with control (root) origin wants to only check 1 era per block.
		assert_ok!(FastUnstake::control(Origin::root(), 1_u32));
	});
}

#[test]
fn control_must_be_control_origin() {
	new_test_ext().execute_with(|| {
		// account without control (root) origin wants to only check 1 era per block.
		assert_noop!(FastUnstake::control(Origin::signed(1), 1_u32), BadOrigin);
	});
}

#[test]
fn unstake_paused_mid_election() {
	new_test_ext().execute_with(|| {
		// Initiate staking position
		let (stash, ctrl) = mint_and_initiate_staking();
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(ctrl), Some(1_u32));
		todo!(
			"a dude is being unstaked, midway being checked, election happens, they are still not
	exposed, but a new era needs to be checked, therefore this unstake takes longer than
	expected."
		)
	});
}
