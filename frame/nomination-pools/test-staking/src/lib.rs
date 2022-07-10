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

use frame_support::{assert_noop, assert_ok, bounded_btree_map, traits::Currency};
use mock::*;
use pallet_nomination_pools::{
	Error as PoolsError, Event as PoolsEvent, LastPoolId, PoolMember, PoolMembers, PoolState,
};
use pallet_staking::{CurrentEra, Event as StakingEvent, Payee, RewardDestination};

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

#[test]
fn pool_slash_e2e() {
	new_test_ext().execute_with(|| {
		ExistentialDeposit::set(1);
		assert_eq!(Balances::minimum_balance(), 1);
		assert_eq!(Staking::current_era(), None);

		// create the pool, we know this has id 1.
		assert_ok!(Pools::create(Origin::signed(10), 40, 10, 10, 10));
		assert_eq!(LastPoolId::<Runtime>::get(), 1);

		assert_eq!(staking_events_since_last_call(), vec![StakingEvent::Bonded(POOL1_BONDED, 40)]);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Created { depositor: 10, pool_id: 1 },
				PoolsEvent::Bonded { member: 10, pool_id: 1, bonded: 40, joined: true },
			]
		);

		assert_eq!(Payee::<Runtime>::get(POOL1_BONDED), RewardDestination::Account(POOL1_REWARD));

		// have two members join
		assert_ok!(Pools::join(Origin::signed(20), 20, 1));
		assert_ok!(Pools::join(Origin::signed(21), 20, 1));

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Bonded(POOL1_BONDED, 20), StakingEvent::Bonded(POOL1_BONDED, 20)]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Bonded { member: 20, pool_id: 1, bonded: 20, joined: true },
				PoolsEvent::Bonded { member: 21, pool_id: 1, bonded: 20, joined: true },
			]
		);

		// now let's progress a bit.
		CurrentEra::<Runtime>::set(Some(1));

		// 20 / 80 of the total funds are unlocked, and safe from any further slash.
		assert_ok!(Pools::unbond(Origin::signed(10), 10, 10));
		assert_ok!(Pools::unbond(Origin::signed(20), 20, 10));

		assert_eq!(
			staking_events_since_last_call(),
			vec![
				StakingEvent::Unbonded(POOL1_BONDED, 10),
				StakingEvent::Unbonded(POOL1_BONDED, 10)
			]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Unbonded { member: 10, pool_id: 1, balance: 10, points: 10 },
				PoolsEvent::Unbonded { member: 20, pool_id: 1, balance: 10, points: 10 }
			]
		);

		CurrentEra::<Runtime>::set(Some(2));

		// note: depositor cannot fully unbond at this point.
		// these funds will still get slashed.
		assert_ok!(Pools::unbond(Origin::signed(10), 10, 10));
		assert_ok!(Pools::unbond(Origin::signed(20), 20, 10));
		assert_ok!(Pools::unbond(Origin::signed(21), 21, 10));

		assert_eq!(
			staking_events_since_last_call(),
			vec![
				StakingEvent::Unbonded(POOL1_BONDED, 10),
				StakingEvent::Unbonded(POOL1_BONDED, 10),
				StakingEvent::Unbonded(POOL1_BONDED, 10),
			]
		);

		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Unbonded { member: 10, pool_id: 1, balance: 10, points: 10 },
				PoolsEvent::Unbonded { member: 20, pool_id: 1, balance: 10, points: 10 },
				PoolsEvent::Unbonded { member: 21, pool_id: 1, balance: 10, points: 10 },
			]
		);

		// At this point, 20 are safe from slash, 30 are unlocking but vulnerable to slash, and and
		// another 30 are active and vulnerable to slash. Let's slash half of them.
		pallet_staking::slashing::do_slash::<Runtime>(
			&POOL1_BONDED,
			30,
			&mut Default::default(),
			&mut Default::default(),
			1, // slash era 1, affects chunks at era 5 onwards.
		);

		assert_eq!(staking_events_since_last_call(), vec![StakingEvent::Slashed(POOL1_BONDED, 30)]);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				// 30 has been slashed to 15 (15 slash)
				PoolsEvent::UnbondingPoolSlashed { pool_id: 1, era: 5, balance: 15 },
				// 30 has been slashed to 15 (15 slash)
				PoolsEvent::PoolSlashed { pool_id: 1, balance: 15 }
			]
		);

		CurrentEra::<Runtime>::set(Some(3));
		assert_ok!(Pools::unbond(Origin::signed(21), 21, 10));

		assert_eq!(
			PoolMembers::<Runtime>::get(21).unwrap(),
			PoolMember {
				pool_id: 1,
				points: 0,
				reward_pool_total_earnings: 0,
				// the 10 points unlocked just now correspond to 5 points in the unbond pool.
				unbonding_eras: bounded_btree_map!(5 => 10, 6 => 5)
			}
		);
		assert_eq!(staking_events_since_last_call(), vec![StakingEvent::Unbonded(POOL1_BONDED, 5)]);
		assert_eq!(
			pool_events_since_last_call(),
			vec![PoolsEvent::Unbonded { member: 21, pool_id: 1, balance: 5, points: 5 }]
		);

		// now we start withdrawing. we do it all at once, at era 6 where 20 and 21 are fully free.
		CurrentEra::<Runtime>::set(Some(6));
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(20), 20, 0));
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(21), 21, 0));

		assert_eq!(
			pool_events_since_last_call(),
			vec![
				// 20 had unbonded 10 safely, and 10 got slashed by half.
				PoolsEvent::Withdrawn { member: 20, pool_id: 1, balance: 10 + 5, points: 20 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 20 },
				// 21 unbonded all of it after the slash
				PoolsEvent::Withdrawn { member: 21, pool_id: 1, balance: 5 + 5, points: 15 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 21 }
			]
		);
		assert_eq!(
			staking_events_since_last_call(),
			// a 10 (un-slashed) + 10/2 (slashed) balance from 10 has also been unlocked
			vec![StakingEvent::Withdrawn(POOL1_BONDED, 15 + 10 + 15)]
		);

		// now, finally, we can unbond the depositor further than their current limit.
		assert_ok!(Pools::set_state(Origin::signed(10), 1, PoolState::Destroying));
		assert_ok!(Pools::unbond(Origin::signed(10), 10, 20));

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Unbonded(POOL1_BONDED, 10)]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::StateChanged { pool_id: 1, new_state: PoolState::Destroying },
				PoolsEvent::Unbonded { member: 10, pool_id: 1, points: 10, balance: 10 }
			]
		);

		CurrentEra::<Runtime>::set(Some(9));
		assert_eq!(
			PoolMembers::<Runtime>::get(10).unwrap(),
			PoolMember {
				pool_id: 1,
				points: 0,
				reward_pool_total_earnings: 0,
				unbonding_eras: bounded_btree_map!(4 => 10, 5 => 10, 9 => 10)
			}
		);
		// withdraw the depositor, they should lose 12 balance in total due to slash.
		assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));

		assert_eq!(
			staking_events_since_last_call(),
			vec![StakingEvent::Withdrawn(POOL1_BONDED, 10)]
		);
		assert_eq!(
			pool_events_since_last_call(),
			vec![
				PoolsEvent::Withdrawn { member: 10, pool_id: 1, balance: 10 + 15, points: 30 },
				PoolsEvent::MemberRemoved { pool_id: 1, member: 10 },
				PoolsEvent::Destroyed { pool_id: 1 }
			]
		);
	});
}
