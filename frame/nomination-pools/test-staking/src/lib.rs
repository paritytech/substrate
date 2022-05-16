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

#![cfg(test)]

mod mock;

use frame_support::{assert_noop, assert_ok, traits::Currency};
use mock::*;
use pallet_nomination_pools::{
	Error as PoolsError, Event as PoolsEvent, LastPoolId, PoolMembers, PoolState,
};
use pallet_staking::{CurrentEra, Event as StakingEvent};

#[test]
fn pool_lifecycle_e2e() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::minimum_balance(), 5);
		assert_eq!(Staking::current_era(), None);

		// create the pool, we know this has id 1.
		assert_ok!(Pools::create(Origin::signed(10), 50, 10, 10, 10));
		assert_eq!(LastPoolId::<Runtime>::get(), 1);

		// have the pool nominate.
		assert_ok!(Pools::nominate(Origin::signed(10), 1, vec![1, 2, 3]));

		assert_eq!(staking_events_since_last_call(), vec![StakingEvent::Bonded(POOL1_BONDED, 50),]);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Created { depositor: 10, pool_id: 1 },
				PoolsEvent::Bonded { member: 10, pool_id: 1, bonded: 50, joined: true },
			]
		);

		// have two members join
		assert_ok!(Pools::join(Origin::signed(20), 10, 1));
		assert_ok!(Pools::join(Origin::signed(21), 10, 1));

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Bonded(POOL1_BONDED, 10), StakingEvent::Bonded(POOL1_BONDED, 10),]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Bonded { member: 20, pool_id: 1, bonded: 10, joined: true },
				PoolsEvent::Bonded { member: 21, pool_id: 1, bonded: 10, joined: true },
			]
		);

		// pool goes into destroying
		assert_ok!(Pools::set_state(Origin::signed(10), 1, PoolState::Destroying));

		// depositor cannot unbond yet.
		assert_noop!(
			Pools::unbond(Origin::signed(10), 10, 50),
			PoolsError::<Runtime>::NotOnlyPoolMember,
		);

		// now the members want to unbond.
		assert_ok!(Pools::unbond(Origin::signed(20), 20, 10));
		assert_ok!(Pools::unbond(Origin::signed(21), 21, 10));

		assert_eq!(PoolMembers::<Runtime>::get(20).unwrap().unbonding_eras.len(), 1);
		assert_eq!(PoolMembers::<Runtime>::get(20).unwrap().points, 0);
		assert_eq!(PoolMembers::<Runtime>::get(21).unwrap().unbonding_eras.len(), 1);
		assert_eq!(PoolMembers::<Runtime>::get(21).unwrap().points, 0);

		assert_eq!(
			staking_events_since_last_call(),
			vec![
				StakingEvent::Unbonded(POOL1_BONDED, 10),
				StakingEvent::Unbonded(POOL1_BONDED, 10),
			]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::StateChanged { pool_id: 1, new_state: PoolState::Destroying },
				PoolsEvent::Unbonded { member: 20, pool_id: 1, points: 10, balance: 10 },
				PoolsEvent::Unbonded { member: 21, pool_id: 1, points: 10, balance: 10 },
			]
		);

		// depositor cannot still unbond
		assert_noop!(
			Pools::unbond(Origin::signed(10), 10, 50),
			PoolsError::<Runtime>::NotOnlyPoolMember,
		);

		for e in 1..BondingDuration::get() {
			CurrentEra::<Runtime>::set(Some(e));
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(20), 20, 0),
				PoolsError::<Runtime>::CannotWithdrawAny
			);
		}

		// members are now unlocked.
		CurrentEra::<Runtime>::set(Some(BondingDuration::get()));

		// depositor cannot still unbond
		assert_noop!(
			Pools::unbond(Origin::signed(10), 10, 50),
			PoolsError::<Runtime>::NotOnlyPoolMember,
		);

		// but members can now withdraw.
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(20), 20, 0));
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(21), 21, 0));
		assert!(PoolMembers::<Runtime>::get(20).is_none());
		assert!(PoolMembers::<Runtime>::get(21).is_none());

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Withdrawn(POOL1_BONDED, 20),]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Withdrawn { member: 20, pool_id: 1, points: 10, balance: 10 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 20 },
				PoolsEvent::Withdrawn { member: 21, pool_id: 1, points: 10, balance: 10 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 21 },
			]
		);

		// as soon as all members have left, the depositor can try to unbond, but since the
		// min-nominator intention is set, they must chill first.
		assert_noop!(
			Pools::unbond(Origin::signed(10), 10, 50),
			pallet_staking::Error::<Runtime>::InsufficientBond
		);

		assert_ok!(Pools::chill(Origin::signed(10), 1));
		assert_ok!(Pools::unbond(Origin::signed(10), 10, 50));

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Chilled(POOL1_BONDED), StakingEvent::Unbonded(POOL1_BONDED, 50),]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![PoolsEvent::Unbonded { member: 10, pool_id: 1, points: 50, balance: 50 }]
		);

		// waiting another bonding duration:
		CurrentEra::<Runtime>::set(Some(BondingDuration::get() * 2));
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 1));

		// pools is fully destroyed now.
		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Withdrawn(POOL1_BONDED, 50),]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Withdrawn { member: 10, pool_id: 1, points: 50, balance: 50 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 10 },
				PoolsEvent::Destroyed { pool_id: 1 }
			]
		);
	})
}
