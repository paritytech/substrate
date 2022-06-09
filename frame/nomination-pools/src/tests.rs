// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use super::*;
use crate::{mock::*, Event};
use frame_support::{
	assert_err, assert_noop, assert_ok, assert_storage_noop, bounded_btree_map,
	storage::{with_transaction, TransactionOutcome},
};
use pallet_balances::Event as BEvent;
use sp_runtime::traits::Dispatchable;

macro_rules! unbonding_pools_with_era {
	($($k:expr => $v:expr),* $(,)?) => {{
		use sp_std::iter::{Iterator, IntoIterator};
		let not_bounded: BTreeMap<_, _> = Iterator::collect(IntoIterator::into_iter([$(($k, $v),)*]));
		UnbondingPoolsWithEra::try_from(not_bounded).unwrap()
	}};
}

macro_rules! member_unbonding_eras {
	($( $any:tt )*) => {{
		let x: BoundedBTreeMap<EraIndex, Balance, MaxUnbonding> = bounded_btree_map!($( $any )*);
		x
	}};
}

pub const DEFAULT_ROLES: PoolRoles<AccountId> =
	PoolRoles { depositor: 10, root: Some(900), nominator: Some(901), state_toggler: Some(902) };

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(BondedPools::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(PoolMembers::<Runtime>::count(), 1);
		assert_eq!(StakingMock::bonding_duration(), 3);

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
			RewardPool::<Runtime> { balance: 0, points: 0u32.into(), total_earnings: 0 }
		);
		assert_eq!(
			PoolMembers::<Runtime>::get(10).unwrap(),
			PoolMember::<Runtime> { pool_id: last_pool, points: 10, ..Default::default() }
		);

		let bonded_account = Pools::create_bonded_account(last_pool);
		let reward_account = Pools::create_reward_account(last_pool);

		// the bonded_account should be bonded by the depositor's funds.
		assert_eq!(StakingMock::active_stake(&bonded_account).unwrap(), 10);
		assert_eq!(StakingMock::total_stake(&bonded_account).unwrap(), 10);

		// but not nominating yet.
		assert!(Nominations::get().is_none());

		// reward account should have an initial ED in it.
		assert_eq!(Balances::free_balance(&reward_account), Balances::minimum_balance());
	})
}

mod bonded_pool {
	use super::*;
	#[test]
	fn balance_to_point_works() {
		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime> {
				id: 123123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			};

			// 1 points : 1 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			assert_eq!(bonded_pool.balance_to_point(10), 10);
			assert_eq!(bonded_pool.balance_to_point(0), 0);

			// 2 points : 1 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 50);
			assert_eq!(bonded_pool.balance_to_point(10), 20);

			// 1 points : 2 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			bonded_pool.points = 50;
			assert_eq!(bonded_pool.balance_to_point(10), 5);

			// 100 points : 0 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 0);
			bonded_pool.points = 100;
			assert_eq!(bonded_pool.balance_to_point(10), 100 * 10);

			// 0 points : 100 balance
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			bonded_pool.points = 0;
			assert_eq!(bonded_pool.balance_to_point(10), 10);

			// 10 points : 3 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 30);
			bonded_pool.points = 100;
			assert_eq!(bonded_pool.balance_to_point(10), 33);

			// 2 points : 3 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 300);
			bonded_pool.points = 200;
			assert_eq!(bonded_pool.balance_to_point(10), 6);

			// 4 points : 9 balance ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 900);
			bonded_pool.points = 400;
			assert_eq!(bonded_pool.balance_to_point(90), 40);
		})
	}

	#[test]
	fn points_to_balance_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 1 balance : 1 points ratio
			let mut bonded_pool = BondedPool::<Runtime> {
				id: 123123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			};

			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			assert_eq!(bonded_pool.points_to_balance(10), 10);
			assert_eq!(bonded_pool.points_to_balance(0), 0);

			// 2 balance : 1 points ratio
			bonded_pool.points = 50;
			assert_eq!(bonded_pool.points_to_balance(10), 20);

			// 100 balance : 0 points ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			bonded_pool.points = 0;
			assert_eq!(bonded_pool.points_to_balance(10), 0);

			// 0 balance : 100 points ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 0);
			bonded_pool.points = 100;
			assert_eq!(bonded_pool.points_to_balance(10), 0);

			// 10 balance : 3 points ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
			bonded_pool.points = 30;
			assert_eq!(bonded_pool.points_to_balance(10), 33);

			// 2 balance : 3 points ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 200);
			bonded_pool.points = 300;
			assert_eq!(bonded_pool.points_to_balance(10), 6);

			// 4 balance : 9 points ratio
			StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 400);
			bonded_pool.points = 900;
			assert_eq!(bonded_pool.points_to_balance(90), 40);
		})
	}

	#[test]
	fn ok_to_join_with_works() {
		ExtBuilder::default().build_and_execute(|| {
			let pool = BondedPool::<Runtime> {
				id: 123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			};

			let min_points_to_balance: u128 =
				<<Runtime as Config>::MinPointsToBalance as Get<u32>>::get().into();

			// Simulate a 100% slashed pool
			StakingMock::set_bonded_balance(pool.bonded_account(), 0);
			assert_noop!(pool.ok_to_join(0), Error::<Runtime>::OverflowRisk);

			// Simulate a slashed pool at `MinPointsToBalance` + 1 slashed pool
			StakingMock::set_bonded_balance(
				pool.bonded_account(),
				min_points_to_balance.saturating_add(1).into(),
			);
			assert_ok!(pool.ok_to_join(0));

			// Simulate a slashed pool at `MinPointsToBalance`
			StakingMock::set_bonded_balance(pool.bonded_account(), min_points_to_balance);
			assert_noop!(pool.ok_to_join(0), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(
				pool.bonded_account(),
				Balance::MAX / min_points_to_balance,
			);
			// New bonded balance would be over threshold of Balance type
			assert_noop!(pool.ok_to_join(0), Error::<Runtime>::OverflowRisk);
			// and a sanity check
			StakingMock::set_bonded_balance(
				pool.bonded_account(),
				Balance::MAX / min_points_to_balance - 1,
			);
			assert_ok!(pool.ok_to_join(0));
		});
	}
}

mod reward_pool {
	#[test]
	fn current_balance_only_counts_balance_over_existential_deposit() {
		use super::*;

		ExtBuilder::default().build_and_execute(|| {
			let reward_account = Pools::create_reward_account(2);

			// Given
			assert_eq!(Balances::free_balance(&reward_account), 0);

			// Then
			assert_eq!(RewardPool::<Runtime>::current_balance(2), 0);

			// Given
			Balances::make_free_balance_be(&reward_account, Balances::minimum_balance());

			// Then
			assert_eq!(RewardPool::<Runtime>::current_balance(2), 0);

			// Given
			Balances::make_free_balance_be(&reward_account, Balances::minimum_balance() + 1);

			// Then
			assert_eq!(RewardPool::<Runtime>::current_balance(2), 1);
		});
	}
}

mod unbond_pool {
	use super::*;

	#[test]
	fn points_to_issue_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 1 points : 1 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 100 };
			assert_eq!(unbond_pool.balance_to_point(10), 10);
			assert_eq!(unbond_pool.balance_to_point(0), 0);

			// 2 points : 1 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 50 };
			assert_eq!(unbond_pool.balance_to_point(10), 20);

			// 1 points : 2 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 50, balance: 100 };
			assert_eq!(unbond_pool.balance_to_point(10), 5);

			// 100 points : 0 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 0 };
			assert_eq!(unbond_pool.balance_to_point(10), 100 * 10);

			// 0 points : 100 balance
			let unbond_pool = UnbondPool::<Runtime> { points: 0, balance: 100 };
			assert_eq!(unbond_pool.balance_to_point(10), 10);

			// 10 points : 3 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 30 };
			assert_eq!(unbond_pool.balance_to_point(10), 33);

			// 2 points : 3 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 200, balance: 300 };
			assert_eq!(unbond_pool.balance_to_point(10), 6);

			// 4 points : 9 balance ratio
			let unbond_pool = UnbondPool::<Runtime> { points: 400, balance: 900 };
			assert_eq!(unbond_pool.balance_to_point(90), 40);
		})
	}

	#[test]
	fn balance_to_unbond_works() {
		// 1 balance : 1 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 100 };
		assert_eq!(unbond_pool.point_to_balance(10), 10);
		assert_eq!(unbond_pool.point_to_balance(0), 0);

		// 1 balance : 2 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 50 };
		assert_eq!(unbond_pool.point_to_balance(10), 5);

		// 2 balance : 1 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 50, balance: 100 };
		assert_eq!(unbond_pool.point_to_balance(10), 20);

		// 100 balance : 0 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 0, balance: 100 };
		assert_eq!(unbond_pool.point_to_balance(10), 0);

		// 0 balance : 100 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 0 };
		assert_eq!(unbond_pool.point_to_balance(10), 0);

		// 10 balance : 3 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 30, balance: 100 };
		assert_eq!(unbond_pool.point_to_balance(10), 33);

		// 2 balance : 3 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 300, balance: 200 };
		assert_eq!(unbond_pool.point_to_balance(10), 6);

		// 4 balance : 9 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 900, balance: 400 };
		assert_eq!(unbond_pool.point_to_balance(90), 40);
	}
}

mod sub_pools {
	use super::*;

	#[test]
	fn maybe_merge_pools_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TotalUnbondingPools::<Runtime>::get(), 5);
			assert_eq!(BondingDuration::get(), 3);
			assert_eq!(PostUnbondingPoolsWindow::get(), 2);

			// Given
			let mut sub_pool_0 = SubPools::<Runtime> {
				no_era: UnbondPool::<Runtime>::default(),
				with_era: unbonding_pools_with_era! {
					0 => UnbondPool::<Runtime> { points: 10, balance: 10 },
					1 => UnbondPool::<Runtime> { points: 10, balance: 10 },
					2 => UnbondPool::<Runtime> { points: 20, balance: 20 },
					3 => UnbondPool::<Runtime> { points: 30, balance: 30 },
					4 => UnbondPool::<Runtime> { points: 40, balance: 40 },
				},
			};

			// When `current_era < TotalUnbondingPools`,
			let sub_pool_1 = sub_pool_0.clone().maybe_merge_pools(0);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When `current_era == TotalUnbondingPools`,
			let sub_pool_1 = sub_pool_1.maybe_merge_pools(1);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When  `current_era - TotalUnbondingPools == 0`,
			let mut sub_pool_1 = sub_pool_1.maybe_merge_pools(2);

			// Then era 0 is merged into the `no_era` pool
			sub_pool_0.no_era = sub_pool_0.with_era.remove(&0).unwrap();
			assert_eq!(sub_pool_1, sub_pool_0);

			// Given we have entries for era 1..=5
			sub_pool_1
				.with_era
				.try_insert(5, UnbondPool::<Runtime> { points: 50, balance: 50 })
				.unwrap();
			sub_pool_0
				.with_era
				.try_insert(5, UnbondPool::<Runtime> { points: 50, balance: 50 })
				.unwrap();

			// When `current_era - TotalUnbondingPools == 1`
			let sub_pool_2 = sub_pool_1.maybe_merge_pools(3);
			let era_1_pool = sub_pool_0.with_era.remove(&1).unwrap();

			// Then era 1 is merged into the `no_era` pool
			sub_pool_0.no_era.points += era_1_pool.points;
			sub_pool_0.no_era.balance += era_1_pool.balance;
			assert_eq!(sub_pool_2, sub_pool_0);

			// When `current_era - TotalUnbondingPools == 5`, so all pools with era <= 4 are removed
			let sub_pool_3 = sub_pool_2.maybe_merge_pools(7);

			// Then all eras <= 5 are merged into the `no_era` pool
			for era in 2..=5 {
				let to_merge = sub_pool_0.with_era.remove(&era).unwrap();
				sub_pool_0.no_era.points += to_merge.points;
				sub_pool_0.no_era.balance += to_merge.balance;
			}
			assert_eq!(sub_pool_3, sub_pool_0);
		});
	}
}

mod join {
	use super::*;

	#[test]
	fn join_works() {
		let bonded = |points, member_counter| BondedPool::<Runtime> {
			id: 1,
			inner: BondedPoolInner {
				state: PoolState::Open,
				points,
				member_counter,
				roles: DEFAULT_ROLES,
			},
		};
		ExtBuilder::default().build_and_execute(|| {
			// Given
			Balances::make_free_balance_be(&11, ExistentialDeposit::get() + 2);
			assert!(!PoolMembers::<Runtime>::contains_key(&11));

			// When
			assert_ok!(Pools::join(Origin::signed(11), 2, 1));

			// Then

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 11, pool_id: 1, bonded: 2, joined: true },
				]
			);

			assert_eq!(
				PoolMembers::<Runtime>::get(&11).unwrap(),
				PoolMember::<Runtime> { pool_id: 1, points: 2, ..Default::default() }
			);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap(), bonded(12, 2));

			// Given
			// The bonded balance is slashed in half
			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), 6);

			// And
			Balances::make_free_balance_be(&12, ExistentialDeposit::get() + 12);
			assert!(!PoolMembers::<Runtime>::contains_key(&12));

			// When
			assert_ok!(Pools::join(Origin::signed(12), 12, 1));

			// Then
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Bonded { member: 12, pool_id: 1, bonded: 12, joined: true }]
			);

			assert_eq!(
				PoolMembers::<Runtime>::get(&12).unwrap(),
				PoolMember::<Runtime> { pool_id: 1, points: 24, ..Default::default() }
			);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap(), bonded(12 + 24, 3));
		});
	}

	#[test]
	fn join_errors_correctly() {
		ExtBuilder::default().with_check(0).build_and_execute(|| {
			// 10 is already part of the default pool created.
			assert_eq!(PoolMembers::<Runtime>::get(&10).unwrap().pool_id, 1);

			assert_noop!(
				Pools::join(Origin::signed(10), 420, 123),
				Error::<Runtime>::AccountBelongsToOtherPool
			);

			assert_noop!(Pools::join(Origin::signed(11), 420, 123), Error::<Runtime>::PoolNotFound);

			// Force the pools bonded balance to 0, simulating a 100% slash
			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), 0);
			assert_noop!(Pools::join(Origin::signed(11), 420, 1), Error::<Runtime>::OverflowRisk);

			// Given a mocked bonded pool
			BondedPool::<Runtime> {
				id: 123,
				inner: BondedPoolInner {
					member_counter: 1,
					state: PoolState::Open,
					points: 100,
					roles: DEFAULT_ROLES,
				},
			}
			.put();

			// and reward pool
			RewardPools::<Runtime>::insert(
				123,
				RewardPool::<Runtime> {
					balance: Zero::zero(),
					total_earnings: Zero::zero(),
					points: U256::from(0u32),
				},
			);

			// Force the points:balance ratio to `MinPointsToBalance` (100/10)
			let min_points_to_balance: u128 =
				<<Runtime as Config>::MinPointsToBalance as Get<u32>>::get().into();

			StakingMock::set_bonded_balance(
				Pools::create_bonded_account(123),
				min_points_to_balance,
			);
			assert_noop!(Pools::join(Origin::signed(11), 420, 123), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(
				Pools::create_bonded_account(123),
				Balance::MAX / min_points_to_balance,
			);
			// Balance needs to be gt Balance::MAX / `MinPointsToBalance`
			assert_noop!(Pools::join(Origin::signed(11), 5, 123), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), min_points_to_balance);

			// Cannot join a pool that isn't open
			unsafe_set_state(123, PoolState::Blocked).unwrap();
			assert_noop!(
				Pools::join(Origin::signed(11), min_points_to_balance, 123),
				Error::<Runtime>::NotOpen
			);

			unsafe_set_state(123, PoolState::Destroying).unwrap();
			assert_noop!(
				Pools::join(Origin::signed(11), min_points_to_balance, 123),
				Error::<Runtime>::NotOpen
			);

			// Given
			MinJoinBond::<Runtime>::put(100);

			// Then
			assert_noop!(
				Pools::join(Origin::signed(11), 99, 123),
				Error::<Runtime>::MinimumBondNotMet
			);
		});
	}

	#[test]
	#[cfg_attr(debug_assertions, should_panic(expected = "Defensive failure has been triggered!"))]
	#[cfg_attr(not(debug_assertions), should_panic)]
	fn join_panics_when_reward_pool_not_found() {
		ExtBuilder::default().build_and_execute(|| {
			StakingMock::set_bonded_balance(Pools::create_bonded_account(123), 100);
			BondedPool::<Runtime> {
				id: 123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			}
			.put();
			let _ = Pools::join(Origin::signed(11), 420, 123);
		});
	}

	#[test]
	fn join_max_member_limits_are_respected() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(MaxPoolMembersPerPool::<Runtime>::get(), Some(3));
			for i in 1..3 {
				let account = i + 100;
				Balances::make_free_balance_be(&account, 100 + Balances::minimum_balance());

				assert_ok!(Pools::join(Origin::signed(account), 100, 1));
			}

			Balances::make_free_balance_be(&103, 100 + Balances::minimum_balance());

			// Then
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 101, pool_id: 1, bonded: 100, joined: true },
					Event::Bonded { member: 102, pool_id: 1, bonded: 100, joined: true }
				]
			);

			assert_noop!(
				Pools::join(Origin::signed(103), 100, 1),
				Error::<Runtime>::MaxPoolMembers
			);

			// Given
			assert_eq!(PoolMembers::<Runtime>::count(), 3);
			assert_eq!(MaxPoolMembers::<Runtime>::get(), Some(4));

			Balances::make_free_balance_be(&104, 100 + Balances::minimum_balance());
			assert_ok!(Pools::create(Origin::signed(104), 100, 104, 104, 104));

			let pool_account = BondedPools::<Runtime>::iter()
				.find(|(_, bonded_pool)| bonded_pool.roles.depositor == 104)
				.map(|(pool_account, _)| pool_account)
				.unwrap();

			// Then
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 104, pool_id: 2 },
					Event::Bonded { member: 104, pool_id: 2, bonded: 100, joined: true }
				]
			);

			assert_noop!(
				Pools::join(Origin::signed(103), 100, pool_account),
				Error::<Runtime>::MaxPoolMembers
			);
		});
	}
}

mod claim_payout {
	use super::*;

	fn del(points: Balance, reward_pool_total_earnings: Balance) -> PoolMember<Runtime> {
		PoolMember {
			pool_id: 1,
			points,
			reward_pool_total_earnings,
			unbonding_eras: Default::default(),
		}
	}

	fn rew(balance: Balance, points: u32, total_earnings: Balance) -> RewardPool<Runtime> {
		RewardPool { balance, points: points.into(), total_earnings }
	}

	#[test]
	fn claim_payout_works() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				// Given each member currently has a free balance of
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				let ed = Balances::minimum_balance();
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 100);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 50, pool_id: 1, bonded: 50, joined: true },
						Event::PaidOut { member: 10, pool_id: 1, payout: 10 },
					]
				);

				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(PoolMembers::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 90);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 40 }]
				);

				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(PoolMembers::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 50 }]
				);

				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(PoolMembers::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 5 }]
				);

				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(PoolMembers::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(45, 5_000 - 50 * 10, 150));
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 45);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 20 }]
				);

				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(PoolMembers::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(25, 4_500 - 50 * 40, 150));
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 50));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 75);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 50 }]
				);

				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(PoolMembers::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(
						25,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * bonded_pool.points(100)
						// del points = member.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				assert_eq!(Balances::free_balance(&50), 50 + 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 25);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 5 }]
				);

				// We expect a payout of 5
				assert_eq!(PoolMembers::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(20, 2_500 - 10 * 50, 200));
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 400));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 420);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 40 }]
				);

				// We expect a payout of 40
				assert_eq!(PoolMembers::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(
						380,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * bonded_pool.points(100)
						// del points = member.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				assert_eq!(Balances::free_balance(&10), 20 + 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 20));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 400);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 2 }]
				);

				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(PoolMembers::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 398);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 188 }]
				);

				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(PoolMembers::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 210);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 210 }]
				);

				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(PoolMembers::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 0);
			});
	}

	#[test]
	fn do_reward_payout_correctly_sets_pool_state_to_destroying() {
		ExtBuilder::default().build_and_execute(|| {
			let _ = with_transaction(|| -> TransactionOutcome<DispatchResult> {
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
				let mut member = PoolMembers::<Runtime>::get(10).unwrap();

				// -- reward_pool.total_earnings saturates

				// Given
				Balances::make_free_balance_be(&default_reward_account(), Balance::MAX);

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut member,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert!(bonded_pool.is_destroying());

				storage::TransactionOutcome::Rollback(Ok(()))
			});

			// -- current_points saturates (reward_pool.points + new_earnings * bonded_pool.points)
			let _ = with_transaction(|| -> TransactionOutcome<DispatchResult> {
				// Given
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
				let mut member = PoolMembers::<Runtime>::get(10).unwrap();
				// Force new_earnings * bonded_pool.points == 100
				Balances::make_free_balance_be(&default_reward_account(), 5 + 10);
				assert_eq!(bonded_pool.points, 10);
				// Force reward_pool.points == U256::MAX - new_earnings * bonded_pool.points
				reward_pool.points = U256::MAX - U256::from(100u32);
				RewardPools::<Runtime>::insert(1, reward_pool.clone());

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut member,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert!(bonded_pool.is_destroying());

				storage::TransactionOutcome::Rollback(Ok(()))
			});
		});
	}

	#[test]
	fn reward_payout_errors_if_a_member_is_fully_unbonding() {
		ExtBuilder::default().add_members(vec![(11, 11)]).build_and_execute(|| {
			// fully unbond the member.
			assert_ok!(Pools::fully_unbond(Origin::signed(11), 11));

			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
			let mut member = PoolMembers::<Runtime>::get(11).unwrap();

			assert_noop!(
				Pools::do_reward_payout(&11, &mut member, &mut bonded_pool, &mut reward_pool,),
				Error::<Runtime>::FullyUnbonding
			);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 11, pool_id: 1, bonded: 11, joined: true },
					Event::Unbonded { member: 11, pool_id: 1, points: 11, balance: 11 }
				]
			);
		});
	}

	#[test]
	fn calculate_member_payout_works_with_a_pool_of_1() {
		let del = |reward_pool_total_earnings| del(10, reward_pool_total_earnings);

		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
			let mut member = PoolMembers::<Runtime>::get(10).unwrap();
			let ed = Balances::minimum_balance();

			// Given no rewards have been earned
			// When
			let payout =
				Pools::calculate_member_payout(&mut member, &mut bonded_pool, &mut reward_pool)
					.unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(member, del(0));
			assert_eq!(reward_pool, rew(0, 0, 0));

			// Given the pool has earned some rewards for the first time
			Balances::make_free_balance_be(&default_reward_account(), ed + 5);

			// When
			let payout =
				Pools::calculate_member_payout(&mut member, &mut bonded_pool, &mut reward_pool)
					.unwrap();

			// Then
			assert_eq!(payout, 5); //  (10 * 5 del virtual points / 10 * 5 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 5));
			assert_eq!(member, del(5));

			// Given the pool has earned rewards again
			Balances::make_free_balance_be(&default_reward_account(), ed + 10);

			// When
			let payout =
				Pools::calculate_member_payout(&mut member, &mut bonded_pool, &mut reward_pool)
					.unwrap();

			// Then
			assert_eq!(payout, 10); // (10 * 10 del virtual points / 10 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 15));
			assert_eq!(member, del(15));

			// Given the pool has earned no new rewards
			Balances::make_free_balance_be(&default_reward_account(), ed + 0);

			// When
			let payout =
				Pools::calculate_member_payout(&mut member, &mut bonded_pool, &mut reward_pool)
					.unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(reward_pool, rew(0, 0, 15));
			assert_eq!(member, del(15));
		});
	}

	#[test]
	fn calculate_member_payout_works_with_a_pool_of_3() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
				let ed = Balances::minimum_balance();
				// PoolMember with 10 points
				let mut del_10 = PoolMembers::<Runtime>::get(10).unwrap();
				// PoolMember with 40 points
				let mut del_40 = PoolMembers::<Runtime>::get(40).unwrap();
				// PoolMember with 50 points
				let mut del_50 = PoolMembers::<Runtime>::get(50).unwrap();

				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 50, pool_id: 1, bonded: 50, joined: true }
					]
				);

				// Given we have a total of 100 points split among the members
				assert_eq!(del_50.points + del_40.points + del_10.points, 100);
				assert_eq!(bonded_pool.points, 100);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 100);

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_10, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 10); // (10 del virtual points / 100 pool points) * 100 pool balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(reward_pool, rew(90, 100 * 100 - 100 * 10, 100));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 10));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_40, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 40); // (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(del_40, del(40, 100));
				assert_eq!(
					reward_pool,
					rew(
						50,
						// old pool points - member virtual points
						9_000 - 100 * 40,
						100
					)
				);
				// Mock the reward pool transferring the payout to del_40
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 40));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_50, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 50); // (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(reward_pool, rew(0, 0, 100));
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 50));

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 50);

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_10, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 5); // (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(reward_pool, rew(45, 5_000 - 50 * 10, 150));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 5));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_40, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 20); // (2,000 del virtual points / 4,500 pool points) * 45 pool balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(reward_pool, rew(25, 4_500 - 50 * 40, 150));
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 20));

				// Given del_50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 50));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 75);

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_50, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 50); // (5,000 del virtual points / 7,5000 pool points) * 75 pool balance
				assert_eq!(del_50, del(50, 200));
				assert_eq!(
					reward_pool,
					rew(
						25,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * bonded_pool.points(100)
						// del points = member.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 50));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_10, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 5);
				assert_eq!(del_10, del(10, 200));
				assert_eq!(reward_pool, rew(20, 2_500 - 10 * 50, 200));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 5));

				// Given del_40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 400));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 420);

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_10, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 40);
				assert_eq!(del_10, del(10, 600));
				assert_eq!(
					reward_pool,
					rew(
						380,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * bonded_pool.points(100)
						// del points = member.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 40));

				// Given del_40 + del_50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 20));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 400);

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_10, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 2); // (200 del virtual points / 38,000 pool points) * 400 pool balance
				assert_eq!(del_10, del(10, 620));
				assert_eq!(reward_pool, rew(398, (38_000 + 20 * 100) - 10 * 20, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 2));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_40, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 188); // (18,800 del virtual points /  39,800 pool points) * 399 pool balance
				assert_eq!(del_40, del(40, 620));
				assert_eq!(reward_pool, rew(210, 39_800 - 40 * 470, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 188));

				// When
				let payout =
					Pools::calculate_member_payout(&mut del_50, &mut bonded_pool, &mut reward_pool)
						.unwrap();

				// Then
				assert_eq!(payout, 210); // (21,000 / 21,000) * 210
				assert_eq!(del_50, del(50, 620));
				assert_eq!(reward_pool, rew(0, 21_000 - 50 * 420, 620));
			});
	}

	#[test]
	fn do_reward_payout_works() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
				let ed = Balances::minimum_balance();

				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 50, pool_id: 1, bonded: 50, joined: true }
					]
				);

				// Given the bonded pool has 100 points
				assert_eq!(bonded_pool.points, 100);
				// Each member currently has a free balance of
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 100);

				let mut del_10 = PoolMembers::get(10).unwrap();
				let mut del_40 = PoolMembers::get(40).unwrap();
				let mut del_50 = PoolMembers::get(50).unwrap();

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut del_10,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 10 }]
				);

				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(reward_pool, rew(90, 100 * 100 - 100 * 10, 100));
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 90);

				// When
				assert_ok!(Pools::do_reward_payout(
					&40,
					&mut del_40,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 40 }]
				);

				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(del_40, del(40, 100));
				assert_eq!(reward_pool, rew(50, 9_000 - 100 * 40, 100));
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 50);

				// When
				assert_ok!(Pools::do_reward_payout(
					&50,
					&mut del_50,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 50 }]
				);

				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(reward_pool, rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&default_reward_account(), ed + 50);

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut del_10,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 5 }]
				);

				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(reward_pool, rew(45, 5_000 - 50 * 10, 150));
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 45);

				// When
				assert_ok!(Pools::do_reward_payout(
					&40,
					&mut del_40,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 20 }]
				);

				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(reward_pool, rew(25, 4_500 - 50 * 40, 150));
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 50));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 75);

				// When
				assert_ok!(Pools::do_reward_payout(
					&50,
					&mut del_50,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 50 }]
				);

				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(del_50, del(50, 200));
				assert_eq!(
					reward_pool,
					rew(
						25,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * bonded_pool.points(100)
						// del points = member.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				assert_eq!(Balances::free_balance(&50), 50 + 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 25);

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut del_10,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 5 }]
				);

				// We expect a payout of 5
				assert_eq!(del_10, del(10, 200));
				assert_eq!(reward_pool, rew(20, 2_500 - 10 * 50, 200));
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 400));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 420);

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut del_10,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 40 }]
				);

				// We expect a payout of 40
				assert_eq!(del_10, del(10, 600));
				assert_eq!(
					reward_pool,
					rew(
						380,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * bonded_pool.points(100)
						// del points = member.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				assert_eq!(Balances::free_balance(&10), 20 + 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 20));
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 400);

				// When
				assert_ok!(Pools::do_reward_payout(
					&10,
					&mut del_10,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 10, pool_id: 1, payout: 2 }]
				);

				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(del_10, del(10, 620));
				assert_eq!(reward_pool, rew(398, (38_000 + 20 * 100) - 10 * 20, 620));
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 398);

				// When
				assert_ok!(Pools::do_reward_payout(
					&40,
					&mut del_40,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 40, pool_id: 1, payout: 188 }]
				);

				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(del_40, del(40, 620));
				assert_eq!(reward_pool, rew(210, 39_800 - 40 * 470, 620));
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 210);

				// When
				assert_ok!(Pools::do_reward_payout(
					&50,
					&mut del_50,
					&mut bonded_pool,
					&mut reward_pool
				));

				// Then
				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::PaidOut { member: 50, pool_id: 1, payout: 210 }]
				);

				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(del_50, del(50, 620));
				assert_eq!(reward_pool, rew(0, 21_000 - 50 * 420, 620));
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&default_reward_account()), ed + 0);
			});
	}
}

mod unbond {
	use super::*;

	#[test]
	fn unbond_of_1_works() {
		ExtBuilder::default().build_and_execute(|| {
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(fully_unbond_permissioned(10));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
				unbonding_pools_with_era! { 0 + 3 => UnbondPool::<Runtime> { points: 10, balance: 10 }}
			);

			assert_eq!(
				BondedPool::<Runtime>::get(1).unwrap(),
				BondedPool {
					id: 1,
					inner: BondedPoolInner {
						state: PoolState::Destroying,
						points: 0,
						member_counter: 1,
						roles: DEFAULT_ROLES,
					}
				}
			);

			assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 0);
		});
	}

	#[test]
	fn unbond_of_3_works() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				let ed = Balances::minimum_balance();
				// Given a slash from 600 -> 100
				StakingMock::set_bonded_balance(default_bonded_account(), 100);
				// and unclaimed rewards of 600.
				Balances::make_free_balance_be(&default_reward_account(), ed + 600);

				// When
				assert_ok!(fully_unbond_permissioned(40));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
					unbonding_pools_with_era! { 0 + 3 => UnbondPool { points: 6, balance: 6 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Open,
							points: 560,
							member_counter: 3,
							roles: DEFAULT_ROLES,
						}
					}
				);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 550, pool_id: 1, bonded: 550, joined: true },
						Event::PaidOut { member: 40, pool_id: 1, payout: 40 },
						Event::Unbonded { member: 40, pool_id: 1, points: 6, balance: 6 }
					]
				);

				assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 94);
				assert_eq!(
					PoolMembers::<Runtime>::get(40).unwrap().unbonding_eras,
					member_unbonding_eras!(0 + 3 => 6)
				);
				assert_eq!(Balances::free_balance(&40), 40 + 40); // We claim rewards when unbonding

				// When
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(fully_unbond_permissioned(550));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					unbonding_pools_with_era! { 0 + 3 => UnbondPool { points: 98, balance: 98 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Destroying,
							points: 10,
							member_counter: 3,
							roles: DEFAULT_ROLES
						}
					}
				);
				assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 2);
				assert_eq!(
					PoolMembers::<Runtime>::get(550).unwrap().unbonding_eras,
					member_unbonding_eras!(0 + 3 => 92)
				);
				assert_eq!(Balances::free_balance(&550), 550 + 550);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::PaidOut { member: 550, pool_id: 1, payout: 550 },
						Event::Unbonded { member: 550, pool_id: 1, points: 92, balance: 92 }
					]
				);

				// When
				CurrentEra::set(3);
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 40, 0));
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 550, 0));
				assert_ok!(fully_unbond_permissioned(10));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
					unbonding_pools_with_era! { 6 => UnbondPool { points: 2, balance: 2 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Destroying,
							points: 0,
							member_counter: 1,
							roles: DEFAULT_ROLES
						}
					}
				);
				assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 0);

				assert_eq!(Balances::free_balance(&550), 550 + 550 + 92);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 40, pool_id: 1, points: 6, balance: 6 },
						Event::MemberRemoved { pool_id: 1, member: 40 },
						Event::Withdrawn { member: 550, pool_id: 1, points: 92, balance: 92 },
						Event::MemberRemoved { pool_id: 1, member: 550 },
						Event::PaidOut { member: 10, pool_id: 1, payout: 10 },
						Event::Unbonded { member: 10, pool_id: 1, points: 2, balance: 2 }
					]
				);
			});
	}

	#[test]
	fn unbond_merges_older_pools() {
		ExtBuilder::default().with_check(1).build_and_execute(|| {
			// Given
			assert_eq!(StakingMock::bonding_duration(), 3);
			SubPoolsStorage::<Runtime>::insert(
				1,
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						0 + 3 => UnbondPool { balance: 10, points: 100 },
						1 + 3 => UnbondPool { balance: 20, points: 20 },
						2 + 3 => UnbondPool { balance: 101, points: 101}
					},
				},
			);
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// When
			let current_era = 1 + TotalUnbondingPools::<Runtime>::get();
			CurrentEra::set(current_era);

			assert_ok!(fully_unbond_permissioned(10));

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: UnbondPool { balance: 10 + 20, points: 100 + 20 },
					with_era: unbonding_pools_with_era! {
						2 + 3 => UnbondPool { balance: 101, points: 101},
						current_era + 3 => UnbondPool { balance: 10, points: 10 },
					},
				},
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 10, balance: 10 }
				]
			);
		});
	}

	#[test]
	fn unbond_kick_works() {
		// Kick: the pool is blocked and the caller is either the root or state-toggler.
		ExtBuilder::default()
			.add_members(vec![(100, 100), (200, 200)])
			.build_and_execute(|| {
				// Given
				unsafe_set_state(1, PoolState::Blocked).unwrap();
				let bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				assert_eq!(bonded_pool.roles.root.unwrap(), 900);
				assert_eq!(bonded_pool.roles.nominator.unwrap(), 901);
				assert_eq!(bonded_pool.roles.state_toggler.unwrap(), 902);

				// When the nominator tries to kick, then its a noop
				assert_noop!(
					Pools::fully_unbond(Origin::signed(901), 100),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// When the root kicks then its ok
				assert_ok!(Pools::fully_unbond(Origin::signed(900), 100));

				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 100, pool_id: 1, bonded: 100, joined: true },
						Event::Bonded { member: 200, pool_id: 1, bonded: 200, joined: true },
						Event::Unbonded { member: 100, pool_id: 1, points: 100, balance: 100 },
					]
				);

				// When the state toggler kicks then its ok
				assert_ok!(Pools::fully_unbond(Origin::signed(902), 200));

				assert_eq!(
					pool_events_since_last_call(),
					vec![Event::Unbonded { member: 200, pool_id: 1, points: 200, balance: 200 }]
				);

				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							roles: DEFAULT_ROLES,
							state: PoolState::Blocked,
							points: 10, // Only 10 points because 200 + 100 was unbonded
							member_counter: 3,
						}
					}
				);
				assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 10);
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: unbonding_pools_with_era! {
							0 + 3 => UnbondPool { points: 100 + 200, balance: 100 + 200 }
						},
					}
				);
				assert_eq!(
					*UnbondingBalanceMap::get().get(&default_bonded_account()).unwrap(),
					100 + 200
				);
			});
	}

	#[test]
	fn unbond_permissionless_works() {
		// Scenarios where non-admin accounts can unbond others
		ExtBuilder::default().add_members(vec![(100, 100)]).build_and_execute(|| {
			// Given the pool is blocked
			unsafe_set_state(1, PoolState::Blocked).unwrap();

			// A permissionless unbond attempt errors
			assert_noop!(
				Pools::fully_unbond(Origin::signed(420), 100),
				Error::<Runtime>::NotKickerOrDestroying
			);

			// permissionless unbond must be full
			assert_noop!(
				Pools::unbond(Origin::signed(420), 100, 80),
				Error::<Runtime>::PartialUnbondNotAllowedPermissionlessly,
			);

			// Given the pool is destroying
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// The depositor cannot be fully unbonded until they are the last member
			assert_noop!(
				Pools::fully_unbond(Origin::signed(10), 10),
				Error::<Runtime>::NotOnlyPoolMember
			);

			// Any account can unbond a member that is not the depositor
			assert_ok!(Pools::fully_unbond(Origin::signed(420), 100));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 100, pool_id: 1, bonded: 100, joined: true },
					Event::Unbonded { member: 100, pool_id: 1, points: 100, balance: 100 }
				]
			);

			// still permissionless unbond must be full
			assert_noop!(
				Pools::unbond(Origin::signed(420), 100, 80),
				Error::<Runtime>::PartialUnbondNotAllowedPermissionlessly,
			);

			// Given the pool is blocked
			unsafe_set_state(1, PoolState::Blocked).unwrap();

			// The depositor cannot be unbonded
			assert_noop!(
				Pools::fully_unbond(Origin::signed(420), 10),
				Error::<Runtime>::DoesNotHavePermission
			);

			// Given the pools is destroying
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// The depositor cannot be unbonded yet.
			assert_noop!(
				Pools::fully_unbond(Origin::signed(420), 10),
				Error::<Runtime>::DoesNotHavePermission,
			);

			// but when everyone is unbonded it can..
			CurrentEra::set(3);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 100, 0));

			// still permissionless unbond must be full.
			assert_noop!(
				Pools::unbond(Origin::signed(420), 10, 5),
				Error::<Runtime>::PartialUnbondNotAllowedPermissionlessly,
			);

			// but full unbond works.
			assert_ok!(Pools::fully_unbond(Origin::signed(420), 10));

			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 0);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 + 3 => UnbondPool { points: 10, balance: 10 }
					}
				}
			);
			assert_eq!(StakingMock::active_stake(&default_bonded_account()).unwrap(), 0);
			assert_eq!(*UnbondingBalanceMap::get().get(&default_bonded_account()).unwrap(), 10);
		});
	}

	#[test]
	#[cfg_attr(debug_assertions, should_panic(expected = "Defensive failure has been triggered!"))]
	#[cfg_attr(not(debug_assertions), should_panic)]
	fn unbond_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::fully_unbond(Origin::signed(11), 11),
				Error::<Runtime>::PoolMemberNotFound
			);

			// Add the member
			let member = PoolMember { pool_id: 2, points: 10, ..Default::default() };
			PoolMembers::<Runtime>::insert(11, member);

			let _ = Pools::fully_unbond(Origin::signed(11), 11);
		});
	}

	#[test]
	#[cfg_attr(debug_assertions, should_panic(expected = "Defensive failure has been triggered!"))]
	#[cfg_attr(not(debug_assertions), should_panic)]
	fn unbond_panics_when_reward_pool_not_found() {
		ExtBuilder::default().build_and_execute(|| {
			let member = PoolMember { pool_id: 2, points: 10, ..Default::default() };
			PoolMembers::<Runtime>::insert(11, member);
			BondedPool::<Runtime> {
				id: 1,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 10,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			}
			.put();

			let _ = Pools::fully_unbond(Origin::signed(11), 11);
		});
	}

	#[test]
	fn partial_unbond_era_tracking() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 10);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 0);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().pool_id, 1);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!()
			);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 10);
			assert!(SubPoolsStorage::<Runtime>::get(1).is_none());
			assert_eq!(CurrentEra::get(), 0);
			assert_eq!(BondingDuration::get(), 3);

			// so the depositor can leave, just keeps the test simpler.
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// when: casual unbond
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 1));

			// then
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 9);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 1);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 9);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 1, balance: 1 }
				]
			);

			// when: casual further unbond, same era.
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 5));

			// then
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 4);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 6);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 4);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 6)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 6, balance: 6 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Unbonded { member: 10, pool_id: 1, points: 5, balance: 5 }]
			);

			// when: casual further unbond, next era.
			CurrentEra::set(1);
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 1));

			// then
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 3);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 7);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 3);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 6, 4 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 6, balance: 6 },
						4 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Unbonded { member: 10, pool_id: 1, points: 1, balance: 1 }]
			);

			// when: unbonding more than our active: error
			assert_err!(
				frame_support::storage::in_storage_layer(|| Pools::unbond(
					Origin::signed(10),
					10,
					5
				)),
				Error::<Runtime>::NotEnoughPointsToUnbond
			);
			// instead:
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 3));

			// then
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 0);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 10);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 0);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 6, 4 => 4)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 6, balance: 6 },
						4 => UnbondPool { points: 4, balance: 4 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Unbonded { member: 10, pool_id: 1, points: 3, balance: 3 }]
			);
		});
	}

	#[test]
	fn partial_unbond_max_chunks() {
		ExtBuilder::default().ed(1).build_and_execute(|| {
			// so the depositor can leave, just keeps the test simpler.
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			MaxUnbonding::set(2);

			// given
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 2));
			CurrentEra::set(1);
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 3));
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 2, 4 => 3)
			);

			// when
			CurrentEra::set(2);
			assert_err!(
				frame_support::storage::in_storage_layer(|| Pools::unbond(
					Origin::signed(10),
					10,
					4
				)),
				Error::<Runtime>::MaxUnbondingLimit
			);

			// when
			MaxUnbonding::set(3);
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 1));
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 2, 4 => 3, 5 => 1)
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 2, balance: 2 },
					Event::Unbonded { member: 10, pool_id: 1, points: 3, balance: 3 },
					Event::Unbonded { member: 10, pool_id: 1, points: 1, balance: 1 }
				]
			);
		})
	}

	// depositor can unbond inly up to `MinCreateBond`.
	#[test]
	fn depositor_permissioned_partial_unbond() {
		ExtBuilder::default().ed(1).build_and_execute(|| {
			// given
			assert_eq!(MinCreateBond::<Runtime>::get(), 2);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 10);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 0);

			// can unbond a bit..
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 3));
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 7);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 3);

			// but not less than 2
			assert_noop!(
				Pools::unbond(Origin::signed(10), 10, 6),
				Error::<Runtime>::NotOnlyPoolMember
			);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 3, balance: 3 }
				]
			);
		});
	}

	// same as above, but the pool is slashed and therefore the depositor cannot partially unbond.
	#[test]
	fn depositor_permissioned_partial_unbond_slashed() {
		ExtBuilder::default().ed(1).build_and_execute(|| {
			// given
			assert_eq!(MinCreateBond::<Runtime>::get(), 2);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 10);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 0);

			// slash the default pool
			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), 5);

			// cannot unbond even 7, because the value of shares is now less.
			assert_noop!(
				Pools::unbond(Origin::signed(10), 10, 7),
				Error::<Runtime>::NotOnlyPoolMember
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
				]
			);
		});
	}

	#[test]
	fn every_unbonding_triggers_payout() {
		ExtBuilder::default().build_and_execute(|| {
			let initial_reward_account = Balances::free_balance(Pools::create_reward_account(1));
			assert_eq!(initial_reward_account, Balances::minimum_balance());
			assert_eq!(initial_reward_account, 5);

			// set the pool to destroying so that depositor can leave.
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			Balances::make_free_balance_be(
				&Pools::create_reward_account(1),
				2 * Balances::minimum_balance(),
			);

			assert_ok!(Pools::unbond(Origin::signed(10), 10, 2));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					// exactly equal to ed, all that can be claimed.
					Event::PaidOut { member: 10, pool_id: 1, payout: 5 },
					Event::Unbonded { member: 10, pool_id: 1, points: 2, balance: 2 }
				]
			);

			CurrentEra::set(1);
			Balances::make_free_balance_be(
				&Pools::create_reward_account(1),
				2 * Balances::minimum_balance(),
			);

			assert_ok!(Pools::unbond(Origin::signed(10), 10, 3));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					// exactly equal to ed, all that can be claimed.
					Event::PaidOut { member: 10, pool_id: 1, payout: 5 },
					Event::Unbonded { member: 10, pool_id: 1, points: 3, balance: 3 }
				]
			);

			CurrentEra::set(2);
			Balances::make_free_balance_be(
				&Pools::create_reward_account(1),
				2 * Balances::minimum_balance(),
			);

			assert_ok!(Pools::unbond(Origin::signed(10), 10, 5));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::PaidOut { member: 10, pool_id: 1, payout: 5 },
					Event::Unbonded { member: 10, pool_id: 1, points: 5, balance: 5 }
				]
			);

			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 2, 4 => 3, 5 => 5)
			);
		});
	}
}

mod pool_withdraw_unbonded {
	use super::*;

	#[test]
	fn pool_withdraw_unbonded_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Given 10 unbond'ed directly against the pool account
			assert_ok!(StakingMock::unbond(default_bonded_account(), 5));
			// and the pool account only has 10 balance
			assert_eq!(StakingMock::active_stake(&default_bonded_account()), Some(5));
			assert_eq!(StakingMock::total_stake(&default_bonded_account()), Some(10));
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);

			// When
			assert_ok!(Pools::pool_withdraw_unbonded(Origin::signed(10), 1, 0));

			// Then there unbonding balance is no longer locked
			assert_eq!(StakingMock::active_stake(&default_bonded_account()), Some(5));
			assert_eq!(StakingMock::total_stake(&default_bonded_account()), Some(5));
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);
		});
	}
}

mod withdraw_unbonded {
	use super::*;
	use frame_support::bounded_btree_map;

	#[test]
	fn withdraw_unbonded_works_against_slashed_no_era_sub_pool() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// reduce the noise a bit.
				let _ = balances_events_since_last_call();

				// Given
				assert_eq!(StakingMock::bonding_duration(), 3);
				assert_ok!(Pools::fully_unbond(Origin::signed(550), 550));
				assert_ok!(Pools::fully_unbond(Origin::signed(40), 40));
				assert_eq!(Balances::free_balance(&default_bonded_account()), 600);

				let mut current_era = 1;
				CurrentEra::set(current_era);

				let mut sub_pools = SubPoolsStorage::<Runtime>::get(1).unwrap();
				let unbond_pool = sub_pools.with_era.get_mut(&3).unwrap();
				// Sanity check
				assert_eq!(*unbond_pool, UnbondPool { points: 550 + 40, balance: 550 + 40 });

				// Simulate a slash to the pool with_era(current_era), decreasing the balance by
				// half
				{
					unbond_pool.balance /= 2; // 295
					SubPoolsStorage::<Runtime>::insert(1, sub_pools);
					// Update the equivalent of the unbonding chunks for the `StakingMock`
					let mut x = UnbondingBalanceMap::get();
					*x.get_mut(&default_bonded_account()).unwrap() /= 5;
					UnbondingBalanceMap::set(&x);
					Balances::make_free_balance_be(
						&default_bonded_account(),
						Balances::free_balance(&default_bonded_account()) / 2, // 300
					);
					StakingMock::set_bonded_balance(
						default_bonded_account(),
						StakingMock::active_stake(&default_bonded_account()).unwrap() / 2,
					);
				};

				// Advance the current_era to ensure all `with_era` pools will be merged into
				// `no_era` pool
				current_era += TotalUnbondingPools::<Runtime>::get();
				CurrentEra::set(current_era);

				// Simulate some other call to unbond that would merge `with_era` pools into
				// `no_era`
				let sub_pools =
					SubPoolsStorage::<Runtime>::get(1).unwrap().maybe_merge_pools(current_era);
				SubPoolsStorage::<Runtime>::insert(1, sub_pools);

				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: UnbondPool { points: 550 + 40, balance: 275 + 20 },
						with_era: Default::default()
					}
				);

				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 550, pool_id: 1, bonded: 550, joined: true },
						Event::Unbonded { member: 550, pool_id: 1, points: 550, balance: 550 },
						Event::Unbonded { member: 40, pool_id: 1, points: 40, balance: 40 },
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::BalanceSet {
						who: default_bonded_account(),
						free: 300,
						reserved: 0
					}]
				);

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().no_era,
					UnbondPool { points: 40, balance: 20 }
				);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 550, pool_id: 1, balance: 275, points: 550 },
						Event::MemberRemoved { pool_id: 1, member: 550 }
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::Transfer { from: default_bonded_account(), to: 550, amount: 275 }]
				);

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(40), 40, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().no_era,
					UnbondPool { points: 0, balance: 0 }
				);
				assert!(!PoolMembers::<Runtime>::contains_key(40));
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 40, pool_id: 1, balance: 20, points: 40 },
						Event::MemberRemoved { pool_id: 1, member: 40 }
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::Transfer { from: default_bonded_account(), to: 40, amount: 20 }]
				);

				// now, finally, the depositor can take out its share.
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(fully_unbond_permissioned(10));

				current_era += 3;
				CurrentEra::set(current_era);

				// when
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Unbonded { member: 10, pool_id: 1, balance: 5, points: 5 },
						Event::Withdrawn { member: 10, pool_id: 1, balance: 5, points: 5 },
						Event::MemberRemoved { pool_id: 1, member: 10 },
						Event::Destroyed { pool_id: 1 }
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![
						BEvent::Transfer { from: default_bonded_account(), to: 10, amount: 5 },
						BEvent::Transfer { from: default_reward_account(), to: 10, amount: 5 }
					]
				);
			});
	}

	#[test]
	fn withdraw_unbonded_works_against_slashed_with_era_sub_pools() {
		ExtBuilder::default()
			.add_members(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				let _ = balances_events_since_last_call();

				// Given
				// current bond is 600, we slash it all to 300.
				StakingMock::set_bonded_balance(default_bonded_account(), 300);
				Balances::make_free_balance_be(&default_bonded_account(), 300);
				assert_eq!(StakingMock::total_stake(&default_bonded_account()), Some(300));

				assert_ok!(fully_unbond_permissioned(40));
				assert_ok!(fully_unbond_permissioned(550));

				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					unbonding_pools_with_era! { 3 => UnbondPool { points: 550 / 2 + 40 / 2, balance: 550 / 2 + 40 / 2 }}
				);

				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 40, pool_id: 1, bonded: 40, joined: true },
						Event::Bonded { member: 550, pool_id: 1, bonded: 550, joined: true },
						Event::Unbonded { member: 40, pool_id: 1, balance: 20, points: 20 },
						Event::Unbonded { member: 550, pool_id: 1, balance: 275, points: 275 },
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::BalanceSet {
						who: default_bonded_account(),
						free: 300,
						reserved: 0
					},]
				);

				CurrentEra::set(StakingMock::bonding_duration());

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(40), 40, 0));

				// Then
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::Transfer { from: default_bonded_account(), to: 40, amount: 20 },]
				);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 40, pool_id: 1, balance: 20, points: 20 },
						Event::MemberRemoved { pool_id: 1, member: 40 }
					]
				);

				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					unbonding_pools_with_era! { 3 => UnbondPool { points: 550 / 2, balance: 550 / 2 }}
				);

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					balances_events_since_last_call(),
					vec![BEvent::Transfer { from: default_bonded_account(), to: 550, amount: 275 },]
				);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 550, pool_id: 1, balance: 275, points: 275 },
						Event::MemberRemoved { pool_id: 1, member: 550 }
					]
				);
				assert!(SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era.is_empty());

				// now, finally, the depositor can take out its share.
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(fully_unbond_permissioned(10));

				// because everyone else has left, the points
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					unbonding_pools_with_era! { 6 => UnbondPool { points: 5, balance: 5 }}
				);

				CurrentEra::set(CurrentEra::get() + 3);

				// when
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));

				// then
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 0);

				// in this test 10 also gets a fair share of the slash, because the slash was
				// applied to the bonded account.
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Unbonded { member: 10, pool_id: 1, points: 5, balance: 5 },
						Event::Withdrawn { member: 10, pool_id: 1, points: 5, balance: 5 },
						Event::MemberRemoved { pool_id: 1, member: 10 },
						Event::Destroyed { pool_id: 1 }
					]
				);
				assert_eq!(
					balances_events_since_last_call(),
					vec![
						BEvent::Transfer { from: default_bonded_account(), to: 10, amount: 5 },
						BEvent::Transfer { from: default_reward_account(), to: 10, amount: 5 }
					]
				);
			});
	}

	#[test]
	fn withdraw_unbonded_handles_faulty_sub_pool_accounting() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(Balances::minimum_balance(), 5);
			assert_eq!(Balances::free_balance(&10), 5);
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(Pools::fully_unbond(Origin::signed(10), 10));

			// Simulate a slash that is not accounted for in the sub pools.
			Balances::make_free_balance_be(&default_bonded_account(), 5);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
				//------------------------------balance decrease is not account for
				unbonding_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 10 } }
			);

			CurrentEra::set(0 + 3);

			// When
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));

			// Then
			assert_eq!(Balances::free_balance(10), 10 + 5);
			assert_eq!(Balances::free_balance(&default_bonded_account()), 0);
		});
	}

	#[test]
	fn withdraw_unbonded_errors_correctly() {
		ExtBuilder::default().with_check(0).build_and_execute(|| {
			// Insert the sub-pool
			let sub_pools = SubPools {
				no_era: Default::default(),
				with_era: unbonding_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 10  }},
			};
			SubPoolsStorage::<Runtime>::insert(1, sub_pools.clone());

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 11, 0),
				Error::<Runtime>::PoolMemberNotFound
			);

			let mut member = PoolMember { pool_id: 1, points: 10, ..Default::default() };
			PoolMembers::<Runtime>::insert(11, member.clone());

			// Simulate calling `unbond`
			member.unbonding_eras = member_unbonding_eras!(3 + 0 => 10);
			PoolMembers::<Runtime>::insert(11, member.clone());

			// We are still in the bonding duration
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 11, 0),
				Error::<Runtime>::CannotWithdrawAny
			);

			// If we error the member does not get removed
			assert_eq!(PoolMembers::<Runtime>::get(&11), Some(member));
			// and the sub pools do not get updated.
			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), sub_pools)
		});
	}

	#[test]
	fn withdraw_unbonded_kick() {
		ExtBuilder::default()
			.add_members(vec![(100, 100), (200, 200)])
			.build_and_execute(|| {
				// Given
				assert_ok!(Pools::fully_unbond(Origin::signed(100), 100));
				assert_ok!(Pools::fully_unbond(Origin::signed(200), 200));
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							points: 10,
							state: PoolState::Open,
							member_counter: 3,
							roles: DEFAULT_ROLES
						}
					}
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// Cannot kick when pool is open
				assert_noop!(
					Pools::withdraw_unbonded(Origin::signed(902), 100, 0),
					Error::<Runtime>::NotKickerOrDestroying
				);
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Created { depositor: 10, pool_id: 1 },
						Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
						Event::Bonded { member: 100, pool_id: 1, bonded: 100, joined: true },
						Event::Bonded { member: 200, pool_id: 1, bonded: 200, joined: true },
						Event::Unbonded { member: 100, pool_id: 1, points: 100, balance: 100 },
						Event::Unbonded { member: 200, pool_id: 1, points: 200, balance: 200 }
					]
				);

				// Given
				unsafe_set_state(1, PoolState::Blocked).unwrap();

				// Cannot kick as a nominator
				assert_noop!(
					Pools::withdraw_unbonded(Origin::signed(901), 100, 0),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// Can kick as root
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(900), 100, 0));

				// Can kick as state toggler
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(900), 200, 0));

				assert_eq!(Balances::free_balance(100), 100 + 100);
				assert_eq!(Balances::free_balance(200), 200 + 200);
				assert!(!PoolMembers::<Runtime>::contains_key(100));
				assert!(!PoolMembers::<Runtime>::contains_key(200));
				assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default());
				assert_eq!(
					pool_events_since_last_call(),
					vec![
						Event::Withdrawn { member: 100, pool_id: 1, points: 100, balance: 100 },
						Event::MemberRemoved { pool_id: 1, member: 100 },
						Event::Withdrawn { member: 200, pool_id: 1, points: 200, balance: 200 },
						Event::MemberRemoved { pool_id: 1, member: 200 }
					]
				);
			});
	}

	#[test]
	fn withdraw_unbonded_destroying_permissionless() {
		ExtBuilder::default().add_members(vec![(100, 100)]).build_and_execute(|| {
			// Given
			assert_ok!(Pools::fully_unbond(Origin::signed(100), 100));
			assert_eq!(
				BondedPool::<Runtime>::get(1).unwrap(),
				BondedPool {
					id: 1,
					inner: BondedPoolInner {
						points: 10,
						state: PoolState::Open,
						member_counter: 2,
						roles: DEFAULT_ROLES,
					}
				}
			);
			CurrentEra::set(StakingMock::bonding_duration());
			assert_eq!(Balances::free_balance(100), 100);

			// Cannot permissionlessly withdraw
			assert_noop!(
				Pools::fully_unbond(Origin::signed(420), 100),
				Error::<Runtime>::NotKickerOrDestroying
			);

			// Given
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// Can permissionlesly withdraw a member that is not the depositor
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(420), 100, 0));

			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default(),);
			assert_eq!(Balances::free_balance(100), 100 + 100);
			assert!(!PoolMembers::<Runtime>::contains_key(100));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 100, pool_id: 1, bonded: 100, joined: true },
					Event::Unbonded { member: 100, pool_id: 1, points: 100, balance: 100 },
					Event::Withdrawn { member: 100, pool_id: 1, points: 100, balance: 100 },
					Event::MemberRemoved { pool_id: 1, member: 100 }
				]
			);
		});
	}

	#[test]
	fn partial_withdraw_unbonded_depositor() {
		ExtBuilder::default().ed(1).build_and_execute(|| {
			// so the depositor can leave, just keeps the test simpler.
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// given
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 6));
			CurrentEra::set(1);
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 1));
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 6, 4 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 6, balance: 6 },
						4 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().active_points(), 3);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().unbonding_points(), 7);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 6, balance: 6 },
					Event::Unbonded { member: 10, pool_id: 1, points: 1, balance: 1 }
				]
			);

			// when
			CurrentEra::set(2);
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(10), 10, 0),
				Error::<Runtime>::CannotWithdrawAny
			);

			// when
			CurrentEra::set(3);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));

			// then
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(4 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						4 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Withdrawn { member: 10, pool_id: 1, points: 6, balance: 6 }]
			);

			// when
			CurrentEra::set(4);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));

			// then
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!()
			);
			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default());
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Withdrawn { member: 10, pool_id: 1, points: 1, balance: 1 },]
			);

			// when repeating:
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(10), 10, 0),
				Error::<Runtime>::CannotWithdrawAny
			);
		});
	}

	#[test]
	fn partial_withdraw_unbonded_non_depositor() {
		ExtBuilder::default().add_members(vec![(11, 10)]).build_and_execute(|| {
			// given
			assert_ok!(Pools::unbond(Origin::signed(11), 11, 6));
			CurrentEra::set(1);
			assert_ok!(Pools::unbond(Origin::signed(11), 11, 1));
			assert_eq!(
				PoolMembers::<Runtime>::get(11).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 6, 4 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						3 => UnbondPool { points: 6, balance: 6 },
						4 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(PoolMembers::<Runtime>::get(11).unwrap().active_points(), 3);
			assert_eq!(PoolMembers::<Runtime>::get(11).unwrap().unbonding_points(), 7);
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 11, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 11, pool_id: 1, points: 6, balance: 6 },
					Event::Unbonded { member: 11, pool_id: 1, points: 1, balance: 1 }
				]
			);

			// when
			CurrentEra::set(2);
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 11, 0),
				Error::<Runtime>::CannotWithdrawAny
			);

			// when
			CurrentEra::set(3);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(11), 11, 0));

			// then
			assert_eq!(
				PoolMembers::<Runtime>::get(11).unwrap().unbonding_eras,
				member_unbonding_eras!(4 => 1)
			);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: unbonding_pools_with_era! {
						4 => UnbondPool { points: 1, balance: 1 }
					}
				}
			);
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Withdrawn { member: 11, pool_id: 1, points: 6, balance: 6 }]
			);

			// when
			CurrentEra::set(4);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(11), 11, 0));

			// then
			assert_eq!(
				PoolMembers::<Runtime>::get(11).unwrap().unbonding_eras,
				member_unbonding_eras!()
			);
			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default());
			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Withdrawn { member: 11, pool_id: 1, points: 1, balance: 1 }]
			);

			// when repeating:
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 11, 0),
				Error::<Runtime>::CannotWithdrawAny
			);
		});
	}

	#[test]
	fn full_multi_step_withdrawing_non_depositor() {
		ExtBuilder::default().add_members(vec![(100, 100)]).build_and_execute(|| {
			// given
			assert_ok!(Pools::unbond(Origin::signed(100), 100, 75));
			assert_eq!(
				PoolMembers::<Runtime>::get(100).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 75)
			);

			// progress one era and unbond the leftover.
			CurrentEra::set(1);
			assert_ok!(Pools::unbond(Origin::signed(100), 100, 25));
			assert_eq!(
				PoolMembers::<Runtime>::get(100).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 75, 4 => 25)
			);

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(100), 100, 0),
				Error::<Runtime>::CannotWithdrawAny
			);

			// now the 75 should be free.
			CurrentEra::set(3);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(100), 100, 0));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 100, pool_id: 1, bonded: 100, joined: true },
					Event::Unbonded { member: 100, pool_id: 1, points: 75, balance: 75 },
					Event::Unbonded { member: 100, pool_id: 1, points: 25, balance: 25 },
					Event::Withdrawn { member: 100, pool_id: 1, points: 75, balance: 75 },
				]
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(100).unwrap().unbonding_eras,
				member_unbonding_eras!(4 => 25)
			);

			// the 25 should be free now, and the member removed.
			CurrentEra::set(4);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(100), 100, 0));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Withdrawn { member: 100, pool_id: 1, points: 25, balance: 25 },
					Event::MemberRemoved { pool_id: 1, member: 100 }
				]
			);
		})
	}

	#[test]
	fn full_multi_step_withdrawing_depositor() {
		ExtBuilder::default().ed(1).build_and_execute(|| {
			// given
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 7));

			// progress one era and unbond the leftover.
			CurrentEra::set(1);
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond(Origin::signed(10), 10, 3));
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(3 => 7, 4 => 3)
			);

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(10), 10, 0),
				Error::<Runtime>::CannotWithdrawAny
			);

			// now the 7 should be free.
			CurrentEra::set(3);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Unbonded { member: 10, pool_id: 1, points: 7, balance: 7 },
					Event::Unbonded { member: 10, pool_id: 1, points: 3, balance: 3 },
					Event::Withdrawn { member: 10, pool_id: 1, points: 7, balance: 7 }
				]
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().unbonding_eras,
				member_unbonding_eras!(4 => 3)
			);

			// the 25 should be free now, and the member removed.
			CurrentEra::set(4);
			assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 10, 0));
			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Withdrawn { member: 10, pool_id: 1, points: 3, balance: 3 },
					Event::MemberRemoved { pool_id: 1, member: 10 },
					// the pool is also destroyed now.
					Event::Destroyed { pool_id: 1 },
				]
			);
		})
	}
}

mod create {
	use super::*;

	#[test]
	fn create_works() {
		ExtBuilder::default().build_and_execute(|| {
			// next pool id is 2.
			let next_pool_stash = Pools::create_bonded_account(2);
			let ed = Balances::minimum_balance();

			assert!(!BondedPools::<Runtime>::contains_key(2));
			assert!(!RewardPools::<Runtime>::contains_key(2));
			assert!(!PoolMembers::<Runtime>::contains_key(11));
			assert_eq!(StakingMock::active_stake(&next_pool_stash), None);

			Balances::make_free_balance_be(&11, StakingMock::minimum_bond() + ed);
			assert_ok!(Pools::create(
				Origin::signed(11),
				StakingMock::minimum_bond(),
				123,
				456,
				789
			));

			assert_eq!(Balances::free_balance(&11), 0);
			assert_eq!(
				PoolMembers::<Runtime>::get(11).unwrap(),
				PoolMember {
					pool_id: 2,
					points: StakingMock::minimum_bond(),
					..Default::default()
				}
			);
			assert_eq!(
				BondedPool::<Runtime>::get(2).unwrap(),
				BondedPool {
					id: 2,
					inner: BondedPoolInner {
						points: StakingMock::minimum_bond(),
						member_counter: 1,
						state: PoolState::Open,
						roles: PoolRoles {
							depositor: 11,
							root: Some(123),
							nominator: Some(456),
							state_toggler: Some(789)
						}
					}
				}
			);
			assert_eq!(
				StakingMock::active_stake(&next_pool_stash).unwrap(),
				StakingMock::minimum_bond()
			);
			assert_eq!(
				RewardPools::<Runtime>::get(2).unwrap(),
				RewardPool {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
				}
			);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Created { depositor: 11, pool_id: 2 },
					Event::Bonded { member: 11, pool_id: 2, bonded: 10, joined: true }
				]
			);
		});
	}

	#[test]
	fn create_errors_correctly() {
		ExtBuilder::default().with_check(0).build_and_execute(|| {
			assert_noop!(
				Pools::create(Origin::signed(10), 420, 123, 456, 789),
				Error::<Runtime>::AccountBelongsToOtherPool
			);

			// Given
			assert_eq!(MinCreateBond::<Runtime>::get(), 2);
			assert_eq!(StakingMock::minimum_bond(), 10);

			// Then
			assert_noop!(
				Pools::create(Origin::signed(11), 9, 123, 456, 789),
				Error::<Runtime>::MinimumBondNotMet
			);

			// Given
			MinCreateBond::<Runtime>::put(20);

			// Then
			assert_noop!(
				Pools::create(Origin::signed(11), 19, 123, 456, 789),
				Error::<Runtime>::MinimumBondNotMet
			);

			// Given
			BondedPool::<Runtime> {
				id: 2,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 10,
					member_counter: 1,
					roles: DEFAULT_ROLES,
				},
			}
			.put();
			assert_eq!(MaxPools::<Runtime>::get(), Some(2));
			assert_eq!(BondedPools::<Runtime>::count(), 2);

			// Then
			assert_noop!(
				Pools::create(Origin::signed(11), 20, 123, 456, 789),
				Error::<Runtime>::MaxPools
			);

			// Given
			assert_eq!(PoolMembers::<Runtime>::count(), 1);
			MaxPools::<Runtime>::put(3);
			MaxPoolMembers::<Runtime>::put(1);
			Balances::make_free_balance_be(&11, 5 + 20);

			// Then
			let create = Call::Pools(crate::Call::<Runtime>::create {
				amount: 20,
				root: 11,
				nominator: 11,
				state_toggler: 11,
			});
			assert_noop!(create.dispatch(Origin::signed(11)), Error::<Runtime>::MaxPoolMembers);
		});
	}
}

mod nominate {
	use super::*;

	#[test]
	fn nominate_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Depositor can't nominate
			assert_noop!(
				Pools::nominate(Origin::signed(10), 1, vec![21]),
				Error::<Runtime>::NotNominator
			);

			// State toggler can't nominate
			assert_noop!(
				Pools::nominate(Origin::signed(902), 1, vec![21]),
				Error::<Runtime>::NotNominator
			);

			// Root can nominate
			assert_ok!(Pools::nominate(Origin::signed(900), 1, vec![21]));
			assert_eq!(Nominations::get().unwrap(), vec![21]);

			// Nominator can nominate
			assert_ok!(Pools::nominate(Origin::signed(901), 1, vec![31]));
			assert_eq!(Nominations::get().unwrap(), vec![31]);

			// Can't nominate for a pool that doesn't exist
			assert_noop!(
				Pools::nominate(Origin::signed(902), 123, vec![21]),
				Error::<Runtime>::PoolNotFound
			);
		});
	}
}

mod set_state {
	use super::*;

	#[test]
	fn set_state_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_ok!(BondedPool::<Runtime>::get(1).unwrap().ok_to_be_open(0));

			// Only the root and state toggler can change the state when the pool is ok to be open.
			assert_noop!(
				Pools::set_state(Origin::signed(10), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state(Origin::signed(901), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// Root can change state
			assert_ok!(Pools::set_state(Origin::signed(900), 1, PoolState::Blocked));

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::StateChanged { pool_id: 1, new_state: PoolState::Blocked }
				]
			);

			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Blocked);

			// State toggler can change state
			assert_ok!(Pools::set_state(Origin::signed(902), 1, PoolState::Destroying));
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// If the pool is destroying, then no one can set state
			assert_noop!(
				Pools::set_state(Origin::signed(900), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state(Origin::signed(902), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// If the pool is not ok to be open, then anyone can set it to destroying

			// Given
			unsafe_set_state(1, PoolState::Open).unwrap();
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			bonded_pool.points = 100;
			bonded_pool.put();
			// When
			assert_ok!(Pools::set_state(Origin::signed(11), 1, PoolState::Destroying));
			// Then
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// Given
			Balances::make_free_balance_be(&default_bonded_account(), Balance::max_value() / 10);
			unsafe_set_state(1, PoolState::Open).unwrap();
			// When
			assert_ok!(Pools::set_state(Origin::signed(11), 1, PoolState::Destroying));
			// Then
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// If the pool is not ok to be open, it cannot be permissionleslly set to a state that
			// isn't destroying
			unsafe_set_state(1, PoolState::Open).unwrap();
			assert_noop!(
				Pools::set_state(Origin::signed(11), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::StateChanged { pool_id: 1, new_state: PoolState::Destroying },
					Event::StateChanged { pool_id: 1, new_state: PoolState::Destroying },
					Event::StateChanged { pool_id: 1, new_state: PoolState::Destroying }
				]
			);
		});
	}
}

mod set_metadata {
	use super::*;

	#[test]
	fn set_metadata_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Root can set metadata
			assert_ok!(Pools::set_metadata(Origin::signed(900), 1, vec![1, 1]));
			assert_eq!(Metadata::<Runtime>::get(1), vec![1, 1]);

			// State toggler can set metadata
			assert_ok!(Pools::set_metadata(Origin::signed(902), 1, vec![2, 2]));
			assert_eq!(Metadata::<Runtime>::get(1), vec![2, 2]);

			// Depositor can't set metadata
			assert_noop!(
				Pools::set_metadata(Origin::signed(10), 1, vec![3, 3]),
				Error::<Runtime>::DoesNotHavePermission
			);

			// Nominator can't set metadata
			assert_noop!(
				Pools::set_metadata(Origin::signed(901), 1, vec![3, 3]),
				Error::<Runtime>::DoesNotHavePermission
			);

			// Metadata cannot be longer than `MaxMetadataLen`
			assert_noop!(
				Pools::set_metadata(Origin::signed(900), 1, vec![1, 1, 1]),
				Error::<Runtime>::MetadataExceedsMaxLen
			);
		});
	}
}

mod set_configs {
	use super::*;

	#[test]
	fn set_configs_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Setting works
			assert_ok!(Pools::set_configs(
				Origin::root(),
				ConfigOp::Set(1 as Balance),
				ConfigOp::Set(2 as Balance),
				ConfigOp::Set(3u32),
				ConfigOp::Set(4u32),
				ConfigOp::Set(5u32),
			));
			assert_eq!(MinJoinBond::<Runtime>::get(), 1);
			assert_eq!(MinCreateBond::<Runtime>::get(), 2);
			assert_eq!(MaxPools::<Runtime>::get(), Some(3));
			assert_eq!(MaxPoolMembers::<Runtime>::get(), Some(4));
			assert_eq!(MaxPoolMembersPerPool::<Runtime>::get(), Some(5));

			// Noop does nothing
			assert_storage_noop!(assert_ok!(Pools::set_configs(
				Origin::root(),
				ConfigOp::Noop,
				ConfigOp::Noop,
				ConfigOp::Noop,
				ConfigOp::Noop,
				ConfigOp::Noop,
			)));

			// Removing works
			assert_ok!(Pools::set_configs(
				Origin::root(),
				ConfigOp::Remove,
				ConfigOp::Remove,
				ConfigOp::Remove,
				ConfigOp::Remove,
				ConfigOp::Remove,
			));
			assert_eq!(MinJoinBond::<Runtime>::get(), 0);
			assert_eq!(MinCreateBond::<Runtime>::get(), 0);
			assert_eq!(MaxPools::<Runtime>::get(), None);
			assert_eq!(MaxPoolMembers::<Runtime>::get(), None);
			assert_eq!(MaxPoolMembersPerPool::<Runtime>::get(), None);
		});
	}
}

mod bond_extra {
	use super::*;
	use crate::Event;

	#[test]
	fn bond_extra_from_free_balance_creator() {
		ExtBuilder::default().build_and_execute(|| {
			// 10 is the owner and a member in pool 1, give them some more funds.
			Balances::make_free_balance_be(&10, 100);

			// given
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 10);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 10);
			assert_eq!(Balances::free_balance(10), 100);

			// when
			assert_ok!(Pools::bond_extra(Origin::signed(10), BondExtra::FreeBalance(10)));

			// then
			assert_eq!(Balances::free_balance(10), 90);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 20);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 20);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: false }
				]
			);

			// when
			assert_ok!(Pools::bond_extra(Origin::signed(10), BondExtra::FreeBalance(20)));

			// then
			assert_eq!(Balances::free_balance(10), 70);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 40);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 40);

			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::Bonded { member: 10, pool_id: 1, bonded: 20, joined: false }]
			);
		})
	}

	#[test]
	fn bond_extra_from_rewards_creator() {
		ExtBuilder::default().build_and_execute(|| {
			// put some money in the reward account, all of which will belong to 10 as the only
			// member of the pool.
			Balances::make_free_balance_be(&default_reward_account(), 7);
			// ... if which only 2 is claimable to make sure the reward account does not die.
			let claimable_reward = 7 - ExistentialDeposit::get();

			// given
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 10);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 10);
			assert_eq!(Balances::free_balance(10), 5);

			// when
			assert_ok!(Pools::bond_extra(Origin::signed(10), BondExtra::Rewards));

			// then
			assert_eq!(Balances::free_balance(10), 5);
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 10 + claimable_reward);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 10 + claimable_reward);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::PaidOut { member: 10, pool_id: 1, payout: claimable_reward },
					Event::Bonded {
						member: 10,
						pool_id: 1,
						bonded: claimable_reward,
						joined: false
					}
				]
			);
		})
	}

	#[test]
	fn bond_extra_from_rewards_joiner() {
		ExtBuilder::default().add_members(vec![(20, 20)]).build_and_execute(|| {
			// put some money in the reward account, all of which will belong to 10 as the only
			// member of the pool.
			Balances::make_free_balance_be(&default_reward_account(), 8);
			// ... if which only 3 is claimable to make sure the reward account does not die.
			let claimable_reward = 8 - ExistentialDeposit::get();
			// NOTE: easier to read of we use 3, so let's use the number instead of variable.
			assert_eq!(claimable_reward, 3, "test is correct if rewards are divisible by 3");

			// given
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 10);
			assert_eq!(PoolMembers::<Runtime>::get(20).unwrap().points, 20);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 30);
			assert_eq!(Balances::free_balance(10), 5);
			assert_eq!(Balances::free_balance(20), 20);

			// when
			assert_ok!(Pools::bond_extra(Origin::signed(10), BondExtra::Rewards));

			// then
			assert_eq!(Balances::free_balance(10), 5);
			// 10's share of the reward is 1/3, since they gave 10/30 of the total shares.
			assert_eq!(PoolMembers::<Runtime>::get(10).unwrap().points, 10 + 1);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 30 + 1);

			// when
			assert_ok!(Pools::bond_extra(Origin::signed(20), BondExtra::Rewards));

			// then
			assert_eq!(Balances::free_balance(20), 20);
			// 20's share of the rewards is the other 2/3 of the rewards, since they have 20/30 of
			// the shares
			assert_eq!(PoolMembers::<Runtime>::get(20).unwrap().points, 20 + 2);
			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 30 + 3);

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::Bonded { member: 20, pool_id: 1, bonded: 20, joined: true },
					Event::PaidOut { member: 10, pool_id: 1, payout: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 1, joined: false },
					Event::PaidOut { member: 20, pool_id: 1, payout: 2 },
					Event::Bonded { member: 20, pool_id: 1, bonded: 2, joined: false }
				]
			);
		})
	}
}

mod update_roles {
	use super::*;

	#[test]
	fn update_roles_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(
				BondedPools::<Runtime>::get(1).unwrap().roles,
				PoolRoles {
					depositor: 10,
					root: Some(900),
					nominator: Some(901),
					state_toggler: Some(902)
				},
			);

			// non-existent pools
			assert_noop!(
				Pools::update_roles(
					Origin::signed(1),
					2,
					ConfigOp::Set(5),
					ConfigOp::Set(6),
					ConfigOp::Set(7)
				),
				Error::<Runtime>::PoolNotFound,
			);

			// depositor cannot change roles.
			assert_noop!(
				Pools::update_roles(
					Origin::signed(1),
					1,
					ConfigOp::Set(5),
					ConfigOp::Set(6),
					ConfigOp::Set(7)
				),
				Error::<Runtime>::DoesNotHavePermission,
			);

			// nominator cannot change roles.
			assert_noop!(
				Pools::update_roles(
					Origin::signed(901),
					1,
					ConfigOp::Set(5),
					ConfigOp::Set(6),
					ConfigOp::Set(7)
				),
				Error::<Runtime>::DoesNotHavePermission,
			);
			// state-toggler
			assert_noop!(
				Pools::update_roles(
					Origin::signed(902),
					1,
					ConfigOp::Set(5),
					ConfigOp::Set(6),
					ConfigOp::Set(7)
				),
				Error::<Runtime>::DoesNotHavePermission,
			);

			// but root can
			assert_ok!(Pools::update_roles(
				Origin::signed(900),
				1,
				ConfigOp::Set(5),
				ConfigOp::Set(6),
				ConfigOp::Set(7)
			));

			assert_eq!(
				pool_events_since_last_call(),
				vec![
					Event::Created { depositor: 10, pool_id: 1 },
					Event::Bonded { member: 10, pool_id: 1, bonded: 10, joined: true },
					Event::RolesUpdated {
						root: Some(5),
						state_toggler: Some(7),
						nominator: Some(6)
					}
				]
			);
			assert_eq!(
				BondedPools::<Runtime>::get(1).unwrap().roles,
				PoolRoles {
					depositor: 10,
					root: Some(5),
					nominator: Some(6),
					state_toggler: Some(7)
				},
			);

			// also root origin can
			assert_ok!(Pools::update_roles(
				Origin::root(),
				1,
				ConfigOp::Set(1),
				ConfigOp::Set(2),
				ConfigOp::Set(3)
			));

			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::RolesUpdated {
					root: Some(1),
					state_toggler: Some(3),
					nominator: Some(2)
				}]
			);
			assert_eq!(
				BondedPools::<Runtime>::get(1).unwrap().roles,
				PoolRoles {
					depositor: 10,
					root: Some(1),
					nominator: Some(2),
					state_toggler: Some(3)
				},
			);

			// Noop works
			assert_ok!(Pools::update_roles(
				Origin::root(),
				1,
				ConfigOp::Set(11),
				ConfigOp::Noop,
				ConfigOp::Noop
			));

			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::RolesUpdated {
					root: Some(11),
					state_toggler: Some(3),
					nominator: Some(2)
				}]
			);

			assert_eq!(
				BondedPools::<Runtime>::get(1).unwrap().roles,
				PoolRoles {
					depositor: 10,
					root: Some(11),
					nominator: Some(2),
					state_toggler: Some(3)
				},
			);

			// Remove works
			assert_ok!(Pools::update_roles(
				Origin::root(),
				1,
				ConfigOp::Set(69),
				ConfigOp::Remove,
				ConfigOp::Remove
			));

			assert_eq!(
				pool_events_since_last_call(),
				vec![Event::RolesUpdated { root: Some(69), state_toggler: None, nominator: None }]
			);

			assert_eq!(
				BondedPools::<Runtime>::get(1).unwrap().roles,
				PoolRoles { depositor: 10, root: Some(69), nominator: None, state_toggler: None },
			);
		})
	}
}
