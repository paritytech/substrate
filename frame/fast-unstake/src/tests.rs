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

//! Tests for pallet-fast-unstake.

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
	});
}

#[test]
fn register_works() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32)));
		// Ensure stash is in the queue.
		assert_ne!(Queue::<Runtime>::get(STASH), None);
	});
}

#[test]
fn cannot_register_if_not_bonded() {
	ExtBuilder::default().build_and_execute(|| {
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
	ExtBuilder::default().build_and_execute(|| {
		// Insert some Queue item
		Queue::<Runtime>::insert(STASH, Some(1_u32));
		// Cannot re-register, already in queue
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32)),
			Error::<Runtime>::AlreadyQueued
		);
	});
}

#[test]
fn cannot_register_if_head() {
	ExtBuilder::default().build_and_execute(|| {
		// Insert some Head item for stash
		Head::<Runtime>::put(UnstakeRequest {
			stash: STASH.clone(),
			checked: vec![],
			maybe_pool_id: None,
		});
		// Controller attempts to regsiter
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32)),
			Error::<Runtime>::AlreadyHead
		);
	});
}

#[test]
fn cannot_register_if_has_unlocking_chunks() {
	ExtBuilder::default().build_and_execute(|| {
		// Start unbonding half of staked tokens
		assert_ok!(Staking::unbond(Origin::signed(CONTROLLER), 50_u128));
		// Cannot regsiter for fast unstake with unlock chunks active
		assert_noop!(
			FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32)),
			Error::<Runtime>::NotFullyBonded
		);
	});
}

#[test]
fn deregister_works() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32));
		// Controller then changes mind and deregisters.
		assert_ok!(FastUnstake::deregister(Origin::signed(CONTROLLER)));
		// Ensure stash no longer exists in the queue.
		assert_eq!(Queue::<Runtime>::get(STASH), None);
	});
}

#[test]
fn cannot_deregister_if_not_controller() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32));
		// Stash tries to deregister.
		assert_noop!(
			FastUnstake::deregister(Origin::signed(STASH)),
			Error::<Runtime>::NotController
		);
	});
}

#[test]
fn cannot_deregister_if_not_queued() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller tries to deregister without first registering
		assert_noop!(
			FastUnstake::deregister(Origin::signed(CONTROLLER)),
			Error::<Runtime>::NotQueued
		);
	});
}

#[test]
fn cannot_deregister_already_head() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller attempts to regsiter, should fail
		FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32));
		// Insert some Head item for stash.
		Head::<Runtime>::put(UnstakeRequest {
			stash: STASH.clone(),
			checked: vec![],
			maybe_pool_id: None,
		});
		// Controller attempts to deregister
		assert_noop!(
			FastUnstake::deregister(Origin::signed(CONTROLLER)),
			Error::<Runtime>::AlreadyHead
		);
	});
}

#[test]
fn control_works() {
	ExtBuilder::default().build_and_execute(|| {
		// account with control (root) origin wants to only check 1 era per block.
		assert_ok!(FastUnstake::control(Origin::root(), 1_u32));
	});
}

#[test]
fn control_must_be_control_origin() {
	ExtBuilder::default().build_and_execute(|| {
		// account without control (root) origin wants to only check 1 era per block.
		assert_noop!(FastUnstake::control(Origin::signed(1), 1_u32), BadOrigin);
	});
}

#[test]
fn process_head_tests() {
	ExtBuilder::default().build_and_execute(|| {
		// put 1 era per block
		ErasToCheckPerBlock::<Runtime>::put(1);

		// TODO: go to block number after BondingDuration eras have passed.
		// is there an accurate calculation for this?
		run_to_block(50_000);

		// register for fast unstake
		FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32));
		assert_eq!(Queue::<Runtime>::get(STASH), Some(Some(1)));

		// process on idle
		let remaining_weight = BlockWeights::get().max_block;
		FastUnstake::on_idle(Zero::zero(), remaining_weight);

		// assert queue item has been moved to head
		assert_eq!(Queue::<Runtime>::get(STASH), None);

		// assert head item present
		assert_eq!(
			Head::<Runtime>::get(),
			Some(UnstakeRequest { stash: 1, checked: vec![0], maybe_pool_id: Some(1) })
		);

		// run on_idle until BondingDuration - 1
		let bond_duration: u64 = BondingDuration::get().into();
		let next_block: u64 = System::block_number() + 1;
		let last_block: u64 = next_block + bond_duration - 2;

		// checking blocks to loop...
		assert_eq!(next_block, 50001);
		assert_eq!(last_block, 50002);

		for i in next_block..last_block {
			run_to_block(i);
			FastUnstake::on_idle(i.into(), remaining_weight);
		}

		// check head item still exists on last era, all eras checked - last
		assert_eq!(
			Head::<Runtime>::get(),
			Some(UnstakeRequest { stash: 1, checked: vec![0], maybe_pool_id: Some(1) })
		);

		// run on_idle again to process last era for head item, should be fully processed
		run_to_block(System::block_number() + 1);
		assert_eq!(Head::<Runtime>::get(), None);
	});
}

#[test]
fn unstake_paused_mid_election() {
	ExtBuilder::default().build_and_execute(|| {
		// Initiate staking position
		// Controller account registers for fast unstake.
		FastUnstake::register_fast_unstake(Origin::signed(CONTROLLER), Some(1_u32));
		todo!(
			"a dude is being unstaked, midway being checked, election happens, they are still not
	exposed, but a new era needs to be checked, therefore this unstake takes longer than
	expected."
		)
	});
}
