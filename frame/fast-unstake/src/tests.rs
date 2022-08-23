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
use pallet_nomination_pools::{BondedPool, PoolId, *};

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
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(PoolMembers::<Runtime>::count(), 1);
		assert_eq!(Staking::bonding_duration(), 3);

		let last_pool = LastPoolId::<Runtime>::get();
		assert_eq!(
			BondedPool::<Runtime>::get(last_pool).unwrap(),
			BondedPool::<Runtime> {
				id: last_pool,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 10,
					member_counter: 1,
					roles: DEFAULT_ROLES
				},
			}
		);
		assert_eq!(
			RewardPools::<Runtime>::get(last_pool).unwrap(),
			RewardPool::<Runtime> {
				last_recorded_reward_counter: Zero::zero(),
				last_recorded_total_payouts: 0,
				total_rewards_claimed: 0
			}
		);
		assert_eq!(
			PoolMembers::<Runtime>::get(10).unwrap(),
			PoolMember::<Runtime> { pool_id: last_pool, points: 10, ..Default::default() }
		);

		let bonded_account = Pools::create_bonded_account(last_pool);
		let reward_account = Pools::create_reward_account(last_pool);

		// the bonded_account should be bonded by the depositor's funds.
		assert_eq!(Staking::active_stake(&bonded_account).unwrap(), 10);
		assert_eq!(Staking::total_stake(&bonded_account).unwrap(), 10);

		// but not nominating yet.
		assert!(Nominations::get().is_none());

		// reward account should have an initial ED in it.
		assert_eq!(Balances::free_balance(&reward_account), Balances::minimum_balance());
	})
}

#[test]
fn cannot_register_if_in_queue() {}

#[test]
fn cannot_register_if_head() {}

#[test]
fn cannot_register_if_has_unlocking_chunks() {}

#[test]
fn cannot_register_if_not_bonded() {}

#[test]
fn unstake_paused_mid_election() {
	todo!("a dude is being unstaked, midway being checked, election happens, they are still not exposed, but a new era needs to be checked, therefore this unstake takes longer than expected.")
}
