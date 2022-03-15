use super::*;
use crate::mock::*;
use frame_support::{assert_noop, assert_ok, assert_storage_noop};

macro_rules! sub_pools_with_era {
	($($k:expr => $v:expr),* $(,)?) => {{
		use sp_std::iter::{Iterator, IntoIterator};
		let not_bounded: BTreeMap<_, _> = Iterator::collect(IntoIterator::into_iter([$(($k, $v),)*]));
		SubPoolsWithEra::try_from(not_bounded).unwrap()
	}};
}

pub const DEFAULT_ROLES: PoolRoles<AccountId> =
	PoolRoles { depositor: 10, root: 900, nominator: 901, state_toggler: 902 };

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(BondedPools::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(Delegators::<Runtime>::count(), 1);
		assert_eq!(StakingMock::bonding_duration(), 3);

		let last_pool = LastPoolId::<Runtime>::get();
		assert_eq!(
			BondedPool::<Runtime>::get(last_pool).unwrap(),
			BondedPool::<Runtime> {
				id: last_pool,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 10,
					delegator_counter: 1,
					roles: DEFAULT_ROLES
				},
			}
		);
		assert_eq!(
			RewardPools::<Runtime>::get(last_pool).unwrap(),
			RewardPool::<Runtime> { balance: 0, points: 0.into(), total_earnings: 0 }
		);
		assert_eq!(
			Delegators::<Runtime>::get(10).unwrap(),
			Delegator::<Runtime> {
				pool_id: last_pool,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None
			}
		)
	})
}

#[test]
fn exercise_delegator_life_cycle() {
	// todo!()
	// create pool
	// join pool
	// claim rewards
	// get more rewards
	//
}

mod bonded_pool {
	use super::*;
	#[test]
	fn points_to_issue_works() {
		let mut bonded_pool = BondedPool::<Runtime> {
			id: 123123,
			inner: BondedPoolInner {
				state: PoolState::Open,
				points: 100,
				delegator_counter: 1,
				roles: DEFAULT_ROLES,
			},
		};

		// 1 points : 1 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
		assert_eq!(bonded_pool.points_to_issue(10), 10);
		assert_eq!(bonded_pool.points_to_issue(0), 0);

		// 2 points : 1 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 50);
		assert_eq!(bonded_pool.points_to_issue(10), 20);

		// 1 points : 2 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
		bonded_pool.points = 50;
		assert_eq!(bonded_pool.points_to_issue(10), 5);

		// 100 points : 0 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 0);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.points_to_issue(10), 100 * 10);

		// 0 points : 100 balance
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.points_to_issue(10), 10);

		// 10 points : 3 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 30);
		assert_eq!(bonded_pool.points_to_issue(10), 33);

		// 2 points : 3 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 300);
		bonded_pool.points = 200;
		assert_eq!(bonded_pool.points_to_issue(10), 6);

		// 4 points : 9 balance ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 900);
		bonded_pool.points = 400;
		assert_eq!(bonded_pool.points_to_issue(90), 40);
	}

	#[test]
	fn balance_to_unbond_works() {
		// 1 balance : 1 points ratio
		let mut bonded_pool = BondedPool::<Runtime> {
			id: 123123,
			inner: BondedPoolInner {
				state: PoolState::Open,
				points: 100,
				delegator_counter: 1,
				roles: DEFAULT_ROLES,
			},
		};

		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
		assert_eq!(bonded_pool.balance_to_unbond(10), 10);
		assert_eq!(bonded_pool.balance_to_unbond(0), 0);

		// 2 balance : 1 points ratio
		bonded_pool.points = 50;
		assert_eq!(bonded_pool.balance_to_unbond(10), 20);

		// 100 balance : 0 points ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 0);
		bonded_pool.points = 0;
		assert_eq!(bonded_pool.balance_to_unbond(10), 0);

		// 0 balance : 100 points ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 0);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.balance_to_unbond(10), 0);

		// 10 balance : 3 points ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 100);
		bonded_pool.points = 30;
		assert_eq!(bonded_pool.balance_to_unbond(10), 33);

		// 2 balance : 3 points ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 200);
		bonded_pool.points = 300;
		assert_eq!(bonded_pool.balance_to_unbond(10), 6);

		// 4 balance : 9 points ratio
		StakingMock::set_bonded_balance(bonded_pool.bonded_account(), 400);
		bonded_pool.points = 900;
		assert_eq!(bonded_pool.balance_to_unbond(90), 40);
	}

	#[test]
	fn ok_to_join_with_works() {
		ExtBuilder::default().build_and_execute(|| {
			let pool = BondedPool::<Runtime> {
				id: 123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					delegator_counter: 1,
					roles: DEFAULT_ROLES,
				},
			};

			// Simulate a 100% slashed pool
			StakingMock::set_bonded_balance(pool.bonded_account(), 0);
			assert_noop!(pool.ok_to_join(), Error::<Runtime>::OverflowRisk);

			// Simulate a 89%
			StakingMock::set_bonded_balance(pool.bonded_account(), 11);
			assert_ok!(pool.ok_to_join());

			// Simulate a 90% slashed pool
			StakingMock::set_bonded_balance(pool.bonded_account(), 10);
			assert_noop!(pool.ok_to_join(), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(pool.bonded_account(), Balance::MAX / 10);
			// New bonded balance would be over 1/10th of Balance type
			assert_noop!(pool.ok_to_join(), Error::<Runtime>::OverflowRisk);
			// and a sanity check
			StakingMock::set_bonded_balance(pool.bonded_account(), Balance::MAX / 10 - 1);
			assert_ok!(pool.ok_to_join());
		});
	}
}

mod reward_pool {}

mod unbond_pool {
	use super::*;

	#[test]
	fn points_to_issue_works() {
		// 1 points : 1 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 100 };
		assert_eq!(unbond_pool.points_to_issue(10), 10);
		assert_eq!(unbond_pool.points_to_issue(0), 0);

		// 2 points : 1 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 50 };
		assert_eq!(unbond_pool.points_to_issue(10), 20);

		// 1 points : 2 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 50, balance: 100 };
		assert_eq!(unbond_pool.points_to_issue(10), 5);

		// 100 points : 0 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 0 };
		assert_eq!(unbond_pool.points_to_issue(10), 100 * 10);

		// 0 points : 100 balance
		let unbond_pool = UnbondPool::<Runtime> { points: 0, balance: 100 };
		assert_eq!(unbond_pool.points_to_issue(10), 10);

		// 10 points : 3 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 30 };
		assert_eq!(unbond_pool.points_to_issue(10), 33);

		// 2 points : 3 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 200, balance: 300 };
		assert_eq!(unbond_pool.points_to_issue(10), 6);

		// 4 points : 9 balance ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 400, balance: 900 };
		assert_eq!(unbond_pool.points_to_issue(90), 40);
	}

	#[test]
	fn balance_to_unbond_works() {
		// 1 balance : 1 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 100 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 10);
		assert_eq!(unbond_pool.balance_to_unbond(0), 0);

		// 1 balance : 2 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 50 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 5);

		// 2 balance : 1 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 50, balance: 100 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 20);

		// 100 balance : 0 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 0, balance: 100 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 0);

		// 0 balance : 100 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 100, balance: 0 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 0);

		// 10 balance : 3 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 30, balance: 100 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 33);

		// 2 balance : 3 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 300, balance: 200 };
		assert_eq!(unbond_pool.balance_to_unbond(10), 6);

		// 4 balance : 9 points ratio
		let unbond_pool = UnbondPool::<Runtime> { points: 900, balance: 400 };
		assert_eq!(unbond_pool.balance_to_unbond(90), 40);
	}
}

mod sub_pools {
	use super::*;

	#[test]
	fn maybe_merge_pools_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TotalUnbondingPools::<Runtime>::get(), 5);

			// Given
			let mut sub_pool_0 = SubPools::<Runtime> {
				no_era: UnbondPool::<Runtime>::default(),
				with_era: sub_pools_with_era! {
					0 => UnbondPool::<Runtime> { points: 10, balance: 10 },
					1 => UnbondPool::<Runtime> { points: 10, balance: 10 },
					2 => UnbondPool::<Runtime> { points: 20, balance: 20 },
					3 => UnbondPool::<Runtime> { points: 30, balance: 30 },
					4 => UnbondPool::<Runtime> { points: 40, balance: 40 },
				},
			};

			// When `current_era < TotalUnbondingPools`,
			let sub_pool_1 = sub_pool_0.clone().maybe_merge_pools(3);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When `current_era == TotalUnbondingPools`,
			let sub_pool_1 = sub_pool_1.maybe_merge_pools(4);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When  `current_era - TotalUnbondingPools == 0`,
			let mut sub_pool_1 = sub_pool_1.maybe_merge_pools(5);

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
			let sub_pool_2 = sub_pool_1.maybe_merge_pools(6);
			let era_1_pool = sub_pool_0.with_era.remove(&1).unwrap();

			// Then era 1 is merged into the `no_era` pool
			sub_pool_0.no_era.points += era_1_pool.points;
			sub_pool_0.no_era.balance += era_1_pool.balance;
			assert_eq!(sub_pool_2, sub_pool_0);

			// When `current_era - TotalUnbondingPools == 5`, so all pools with era <= 4 are removed
			let sub_pool_3 = sub_pool_2.maybe_merge_pools(10);

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
		let bonded = |points, delegator_counter| BondedPool::<Runtime> {
			id: 1,
			inner: BondedPoolInner {
				state: PoolState::Open,
				points,
				delegator_counter,
				roles: DEFAULT_ROLES,
			},
		};
		ExtBuilder::default().build_and_execute(|| {
			// Given
			Balances::make_free_balance_be(&11, ExistentialDeposit::get() + 2);
			assert!(!Delegators::<Runtime>::contains_key(&11));

			// When
			assert_ok!(Pools::join(Origin::signed(11), 2, 1));

			// then
			assert_eq!(
				Delegators::<Runtime>::get(&11).unwrap(),
				Delegator::<Runtime> {
					pool_id: 1,
					points: 2,
					reward_pool_total_earnings: 0,
					unbonding_era: None
				}
			);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap(), bonded(12, 2));

			// Given
			// The bonded balance is slashed in half
			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), 6);

			// And
			Balances::make_free_balance_be(&12, ExistentialDeposit::get() + 12);
			assert!(!Delegators::<Runtime>::contains_key(&12));

			// When
			assert_ok!(Pools::join(Origin::signed(12), 12, 1));

			// Then
			assert_eq!(
				Delegators::<Runtime>::get(&12).unwrap(),
				Delegator::<Runtime> {
					pool_id: 1,
					points: 24,
					reward_pool_total_earnings: 0,
					unbonding_era: None
				}
			);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap(), bonded(12 + 24, 3));
		});
	}

	#[test]
	fn join_errors_correctly() {
		ExtBuilder::default().build_and_execute_no_checks(|| {
			// 10 is already part of the default pool created.
			assert_eq!(Delegators::<Runtime>::get(&10).unwrap().pool_id, 1);

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
					delegator_counter: 1,
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

			// Force the points:balance ratio to 100/10
			StakingMock::set_bonded_balance(Pools::create_bonded_account(123), 10);
			assert_noop!(Pools::join(Origin::signed(11), 420, 123), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(Pools::create_bonded_account(123), Balance::MAX / 10);
			// Balance is gt 1/10 of Balance::MAX
			assert_noop!(Pools::join(Origin::signed(11), 5, 123), Error::<Runtime>::OverflowRisk);

			StakingMock::set_bonded_balance(Pools::create_bonded_account(1), 10);

			// Cannot join a pool that isn't open
			unsafe_set_state(123, PoolState::Blocked).unwrap();
			assert_noop!(Pools::join(Origin::signed(11), 10, 123), Error::<Runtime>::NotOpen);

			unsafe_set_state(123, PoolState::Destroying).unwrap();
			assert_noop!(Pools::join(Origin::signed(11), 10, 123), Error::<Runtime>::NotOpen);

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
	#[should_panic = "Defensive failure has been triggered!"]
	fn join_panics_when_reward_pool_not_found() {
		// TODO: but we should fail defensively..
		ExtBuilder::default().build_and_execute(|| {
			StakingMock::set_bonded_balance(Pools::create_bonded_account(123), 100);
			BondedPool::<Runtime> {
				id: 123,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 100,
					delegator_counter: 1,
					roles: DEFAULT_ROLES,
				},
			}
			.put();
			let _ = Pools::join(Origin::signed(11), 420, 123);
		});
	}

	#[test]
	fn join_max_delegator_limits_are_respected() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(MaxDelegatorsPerPool::<Runtime>::get(), Some(3));
			for i in 1..3 {
				let account = i + 100;
				Balances::make_free_balance_be(&account, 100 + Balances::minimum_balance());

				assert_ok!(Pools::join(Origin::signed(account), 100, 1));
			}

			Balances::make_free_balance_be(&103, 100 + Balances::minimum_balance());

			// Then
			assert_noop!(Pools::join(Origin::signed(103), 100, 1), Error::<Runtime>::MaxDelegators);

			// Given
			assert_eq!(Delegators::<Runtime>::count(), 3);
			assert_eq!(MaxDelegators::<Runtime>::get(), Some(4));

			Balances::make_free_balance_be(&104, 100 + Balances::minimum_balance());
			assert_ok!(Pools::create(Origin::signed(104), 100, 104, 104, 104));

			let pool_account = BondedPools::<Runtime>::iter()
				.find(|(_, bonded_pool)| bonded_pool.roles.depositor == 104)
				.map(|(pool_account, _)| pool_account)
				.unwrap();

			// Then
			assert_noop!(
				Pools::join(Origin::signed(103), 100, pool_account),
				Error::<Runtime>::MaxDelegators
			);
		});
	}
}

mod claim_payout {
	use super::*;

	fn del(points: Balance, reward_pool_total_earnings: Balance) -> Delegator<Runtime> {
		Delegator { pool_id: 1, points, reward_pool_total_earnings, unbonding_era: None }
	}

	fn rew(balance: Balance, points: u32, total_earnings: Balance) -> RewardPool<Runtime> {
		RewardPool { balance, points: points.into(), total_earnings }
	}

	#[test]
	fn claim_payout_works() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				// Given each delegator currently has a free balance of
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				let reward_account = Pools::create_reward_account(1);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&reward_account, 100);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&reward_account), 90);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&reward_account), 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&reward_account), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&reward_account, 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(45, 5_000 - 50 * 10, 150));
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&reward_account), 45);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(25, 4_500 - 50 * 40, 150));
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&reward_account), 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&reward_account, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&reward_account), 75);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(
						25,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * bonded_pool.points(100)
						// del points = delegator.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				assert_eq!(Balances::free_balance(&50), 50 + 50);
				assert_eq!(Balances::free_balance(&reward_account), 25);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// We expect a payout of 5
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(20, 2_500 - 10 * 50, 200));
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&reward_account), 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&reward_account, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&reward_account), 420);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// We expect a payout of 40
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(
						380,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * bonded_pool.points(100)
						// del points = delegator.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				assert_eq!(Balances::free_balance(&10), 20 + 40);
				assert_eq!(Balances::free_balance(&reward_account), 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&reward_account, |a| a.free += 20));
				assert_eq!(Balances::free_balance(&reward_account), 400);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&reward_account), 398);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&reward_account), 210);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&reward_account), 0);
			});
	}

	#[test]
	fn do_reward_payout_correctly_sets_pool_state_to_destroying() {
		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			let reward_account = Pools::create_reward_account(1);

			// --- reward_pool.total_earnings saturates

			// Given
			Balances::make_free_balance_be(&reward_account, Balance::MAX);

			// When
			assert_ok!(Pools::do_reward_payout(10, &mut delegator, &mut bonded_pool));

			// Then
			assert!(bonded_pool.is_destroying());

			// -- current_points saturates (reward_pool.points + new_earnings * bonded_pool.points)

			// Given
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			// Force new_earnings * bonded_pool.points == 100
			Balances::make_free_balance_be(&reward_account, 10);
			assert_eq!(bonded_pool.points, 10);
			// Force reward_pool.points == U256::MAX - new_earnings * bonded_pool.points
			reward_pool.points = U256::MAX - U256::from(100u32);
			RewardPools::<Runtime>::insert(1, reward_pool.clone());

			// When
			assert_ok!(Pools::do_reward_payout(10, &mut delegator, &mut bonded_pool));

			// Then
			assert!(bonded_pool.is_destroying());
		});
	}

	#[test]
	fn calculate_delegator_payout_errors_if_a_delegator_is_unbonding() {
		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			delegator.unbonding_era = Some(0 + 3);

			assert_noop!(
				Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut delegator
				),
				Error::<Runtime>::AlreadyUnbonding
			);
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_1() {
		let del = |reward_pool_total_earnings| del(10, reward_pool_total_earnings);

		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			let reward_account = Pools::create_reward_account(1);

			// Given no rewards have been earned
			// When
			let payout = Pools::calculate_delegator_payout(
				&mut bonded_pool,
				&mut reward_pool,
				&mut delegator,
			)
			.unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(delegator, del(0));
			assert_eq!(reward_pool, rew(0, 0, 0));

			// Given the pool has earned some rewards for the first time
			Balances::make_free_balance_be(&reward_account, 5);

			// When
			let payout = Pools::calculate_delegator_payout(
				&mut bonded_pool,
				&mut reward_pool,
				&mut delegator,
			)
			.unwrap();

			// Then
			assert_eq!(payout, 5); //  (10 * 5 del virtual points / 10 * 5 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 5));
			assert_eq!(delegator, del(5));

			// Given the pool has earned rewards again
			Balances::make_free_balance_be(&reward_account, 10);

			// When
			let payout = Pools::calculate_delegator_payout(
				&mut bonded_pool,
				&mut reward_pool,
				&mut delegator,
			)
			.unwrap();

			// Then
			assert_eq!(payout, 10); // (10 * 10 del virtual points / 10 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 15));
			assert_eq!(delegator, del(15));

			// Given the pool has earned no new rewards
			Balances::make_free_balance_be(&reward_account, 0);

			// When
			let payout = Pools::calculate_delegator_payout(
				&mut bonded_pool,
				&mut reward_pool,
				&mut delegator,
			)
			.unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(reward_pool, rew(0, 0, 15));
			assert_eq!(delegator, del(15));
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_3() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				let mut reward_pool = RewardPools::<Runtime>::get(1).unwrap();
				// Delegator with 10 points
				let mut del_10 = Delegators::<Runtime>::get(10).unwrap();
				// Delegator with 40 points
				let mut del_40 = Delegators::<Runtime>::get(40).unwrap();
				// Delegator with 50 points
				let mut del_50 = Delegators::<Runtime>::get(50).unwrap();

				// Given we have a total of 100 points split among the delegators
				assert_eq!(del_50.points + del_40.points + del_10.points, 100);
				assert_eq!(bonded_pool.points, 100);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&default_reward_account(), 100);

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_10,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 10); // (10 del virtual points / 100 pool points) * 100 pool balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(reward_pool, rew(90, 100 * 100 - 100 * 10, 100));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 10));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_40,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 40); // (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(del_40, del(40, 100));
				assert_eq!(
					reward_pool,
					rew(
						50,
						// old pool points - delegator virtual points
						9_000 - 100 * 40,
						100
					)
				);
				// Mock the reward pool transferring the payout to del_40
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 40));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_50,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 50); // (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(reward_pool, rew(0, 0, 100));
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 50));

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&default_reward_account(), 50);

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_10,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 5); // (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(reward_pool, rew(45, 5_000 - 50 * 10, 150));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 5));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_40,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 20); // (2,000 del virtual points / 4,500 pool points) * 45 pool balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(reward_pool, rew(25, 4_500 - 50 * 40, 150));
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 20));

				// Given del_50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 50));
				assert_eq!(Balances::free_balance(&default_reward_account()), 75);

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_50,
				)
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
						// del points = delegator.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 50));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_10,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 5);
				assert_eq!(del_10, del(10, 200));
				assert_eq!(reward_pool, rew(20, 2_500 - 10 * 50, 200));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 5));

				// Given del_40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 400));
				assert_eq!(Balances::free_balance(&default_reward_account()), 420);

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_10,
				)
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
						// del points = delegator.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 40));

				// Given del_40 + del_50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 20));
				assert_eq!(Balances::free_balance(&default_reward_account()), 400);

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_10,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 2); // (200 del virtual points / 38,000 pool points) * 400 pool balance
				assert_eq!(del_10, del(10, 620));
				assert_eq!(reward_pool, rew(398, (38_000 + 20 * 100) - 10 * 20, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 2));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_40,
				)
				.unwrap();

				// Then
				assert_eq!(payout, 188); // (18,800 del virtual points /  39,800 pool points) * 399 pool balance
				assert_eq!(del_40, del(40, 620));
				assert_eq!(reward_pool, rew(210, 39_800 - 40 * 470, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free -= 188));

				// When
				let payout = Pools::calculate_delegator_payout(
					&mut bonded_pool,
					&mut reward_pool,
					&mut del_50,
				)
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
			.add_delegators(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();

				// Given the bonded pool has 100 points
				assert_eq!(bonded_pool.points, 100);
				// Each delegator currently has a free balance of
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&default_reward_account(), 100);

				let mut del_10 = Delegators::get(10).unwrap();
				let mut del_40 = Delegators::get(40).unwrap();
				let mut del_50 = Delegators::get(50).unwrap();

				// When
				assert_ok!(Pools::do_reward_payout(10, &mut del_10, &mut bonded_pool));

				// Then
				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&default_reward_account()), 90);

				// When
				assert_ok!(Pools::do_reward_payout(40, &mut del_40, &mut bonded_pool));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(del_40, del(40, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&1).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), 50);

				// When
				assert_ok!(Pools::do_reward_payout(50, &mut del_50, &mut bonded_pool));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&default_reward_account(), 50);

				// When
				assert_ok!(Pools::do_reward_payout(10, &mut del_10, &mut bonded_pool));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(RewardPools::<Runtime>::get(&1).unwrap(), rew(45, 5_000 - 50 * 10, 150));
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), 45);

				// When
				assert_ok!(Pools::do_reward_payout(40, &mut del_40, &mut bonded_pool));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(RewardPools::<Runtime>::get(1).unwrap(), rew(25, 4_500 - 50 * 40, 150));
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&default_reward_account()), 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 50));
				assert_eq!(Balances::free_balance(&default_reward_account()), 75);

				// When
				assert_ok!(Pools::do_reward_payout(50, &mut del_50, &mut bonded_pool));

				// Then
				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(del_50, del(50, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(1).unwrap(),
					rew(
						25,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * bonded_pool.points(100)
						// del points = delegator.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				assert_eq!(Balances::free_balance(&50), 50 + 50);
				assert_eq!(Balances::free_balance(&default_reward_account()), 25);

				// When
				assert_ok!(Pools::do_reward_payout(10, &mut del_10, &mut bonded_pool));

				// Then
				// We expect a payout of 5
				assert_eq!(del_10, del(10, 200));
				assert_eq!(RewardPools::<Runtime>::get(1).unwrap(), rew(20, 2_500 - 10 * 50, 200));
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&default_reward_account()), 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 400));
				assert_eq!(Balances::free_balance(&default_reward_account()), 420);

				// When
				assert_ok!(Pools::do_reward_payout(10, &mut del_10, &mut bonded_pool));

				// Then
				// We expect a payout of 40
				assert_eq!(del_10, del(10, 600));
				assert_eq!(
					RewardPools::<Runtime>::get(1).unwrap(),
					rew(
						380,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * bonded_pool.points(100)
						// del points = delegator.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				assert_eq!(Balances::free_balance(&10), 20 + 40);
				assert_eq!(Balances::free_balance(&default_reward_account()), 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&default_reward_account(), |a| a.free += 20));
				assert_eq!(Balances::free_balance(&default_reward_account()), 400);

				// When
				assert_ok!(Pools::do_reward_payout(10, &mut del_10, &mut bonded_pool));

				// Then
				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(del_10, del(10, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(1).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&default_reward_account()), 398);

				// When
				assert_ok!(Pools::do_reward_payout(40, &mut del_40, &mut bonded_pool));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(del_40, del(40, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(1).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&default_reward_account()), 210);

				// When
				assert_ok!(Pools::do_reward_payout(50, &mut del_50, &mut bonded_pool));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(del_50, del(50, 620));
				assert_eq!(RewardPools::<Runtime>::get(1).unwrap(), rew(0, 21_000 - 50 * 420, 620));
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&default_reward_account()), 0);
			});
	}

	#[test]
	fn do_reward_payout_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();

			// The only place this can return an error is with the balance transfer from the
			// reward  account to the delegator, and as far as this comment author can tell this
			// can only if storage is in a bad state prior to `do_reward_payout` being called.

			// Given
			delegator.points = 15;
			assert_eq!(bonded_pool.points, 10);
			Balances::make_free_balance_be(&default_reward_account(), 10);

			// Then
			// Expect attempt payout of 15/10 * 10 when free balance is actually 10
			assert_noop!(
				Pools::do_reward_payout(10, &mut delegator, &mut bonded_pool),
				pallet_balances::Error::<Runtime>::InsufficientBalance
			);
		});
	}
}

mod unbond {
	use super::*;

	#[test]
	fn unbond_other_of_1_works() {
		ExtBuilder::default().build_and_execute(|| {
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
				sub_pools_with_era! { 0 + 3 => UnbondPool::<Runtime> { points: 10, balance: 10 }}
			);

			assert_eq!(
				BondedPool::<Runtime>::get(1).unwrap(),
				BondedPool {
					id: 1,
					inner: BondedPoolInner {
						state: PoolState::Destroying,
						points: 0,
						delegator_counter: 1,
						roles: DEFAULT_ROLES,
					}
				}
			);

			assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 0);
		});
	}

	#[test]
	fn unbond_other_of_3_works() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given a slash from 600 -> 100
				StakingMock::set_bonded_balance(default_bonded_account(), 100);
				// and unclaimed rewards of 600.
				Balances::make_free_balance_be(&default_reward_account(), 600);

				// When
				assert_ok!(Pools::unbond_other(Origin::signed(40), 40));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 6, balance: 6 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Open,
							points: 560,
							delegator_counter: 3,
							roles: DEFAULT_ROLES,
						}
					}
				);

				assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 94);
				assert_eq!(Delegators::<Runtime>::get(40).unwrap().unbonding_era, Some(0 + 3));
				assert_eq!(Balances::free_balance(&40), 40 + 40); // We claim rewards when unbonding

				// When
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(550), 550));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 98, balance: 98 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Destroying,
							points: 10,
							delegator_counter: 3,
							roles: DEFAULT_ROLES
						}
					}
				);
				assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 2);
				assert_eq!(Delegators::<Runtime>::get(550).unwrap().unbonding_era, Some(0 + 3));
				assert_eq!(Balances::free_balance(&550), 550 + 550);

				// When
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 100, balance: 100 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							state: PoolState::Destroying,
							points: 0,
							delegator_counter: 3,
							roles: DEFAULT_ROLES
						}
					}
				);
				assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 0);
				assert_eq!(Delegators::<Runtime>::get(550).unwrap().unbonding_era, Some(0 + 3));
				assert_eq!(Balances::free_balance(&550), 550 + 550);
			});
	}

	#[test]
	fn unbond_other_merges_older_pools() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(StakingMock::bonding_duration(), 3);
			SubPoolsStorage::<Runtime>::insert(
				1,
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
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

			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: UnbondPool { balance: 10 + 20, points: 100 + 20 },
					with_era: sub_pools_with_era! {
						2 + 3 => UnbondPool { balance: 101, points: 101},
						current_era + 3 => UnbondPool { balance: 10, points: 10 },
					},
				},
			)
		});
	}

	#[test]
	fn unbond_other_kick_works() {
		// Kick: the pool is blocked and the caller is either the root or state-toggler.
		ExtBuilder::default()
			.add_delegators(vec![(100, 100), (200, 200)])
			.build_and_execute(|| {
				// Given
				unsafe_set_state(1, PoolState::Blocked).unwrap();
				let bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
				assert_eq!(bonded_pool.roles.root, 900);
				assert_eq!(bonded_pool.roles.nominator, 901);
				assert_eq!(bonded_pool.roles.state_toggler, 902);

				// When the nominator trys to kick, then its a noop
				assert_noop!(
					Pools::unbond_other(Origin::signed(901), 100),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// When the root kicks then its ok
				assert_ok!(Pools::unbond_other(Origin::signed(900), 100));

				// When the state toggler kicks then its ok
				assert_ok!(Pools::unbond_other(Origin::signed(902), 200));

				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							roles: DEFAULT_ROLES,
							state: PoolState::Blocked,
							points: 10, // Only 10 points because 200 + 100 was unbonded
							delegator_counter: 3,
						}
					}
				);
				assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 10);
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 + 3 => UnbondPool { points: 100 + 200, balance: 100 + 200 }
						},
					}
				);
				assert_eq!(
					UNBONDING_BALANCE_MAP
						.with(|m| *m.borrow_mut().get(&default_bonded_account()).unwrap()),
					100 + 200
				);
			});
	}

	#[test]
	fn unbond_other_with_non_admins_works() {
		// Scenarios where non-admin accounts can unbond others
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given the pool is blocked
			unsafe_set_state(1, PoolState::Blocked).unwrap();

			// A permissionless unbond attempt errors
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 100),
				Error::<Runtime>::NotKickerOrDestroying
			);

			// Given the pool is destroying
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// The depositor cannot be unbonded until they are the last delegator
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 10),
				Error::<Runtime>::NotOnlyDelegator
			);

			// Any account can unbond a delegator that is not the depositor
			assert_ok!(Pools::unbond_other(Origin::signed(420), 100));

			// Given the pool is blocked
			unsafe_set_state(1, PoolState::Blocked).unwrap();

			// The depositor cannot be unbonded
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 10),
				Error::<Runtime>::NotDestroying
			);

			// Given the pools is destroying
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// The depositor can be unbonded
			assert_ok!(Pools::unbond_other(Origin::signed(420), 10));

			assert_eq!(BondedPools::<Runtime>::get(1).unwrap().points, 0);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
						0 + 3 => UnbondPool { points: 110, balance: 110 }
					}
				}
			);
			assert_eq!(StakingMock::bonded_balance(&default_bonded_account()).unwrap(), 0);
			assert_eq!(
				UNBONDING_BALANCE_MAP
					.with(|m| *m.borrow_mut().get(&default_bonded_account()).unwrap()),
				110
			);
		});
	}

	#[test]
	#[should_panic = "Defensive failure has been triggered!"]
	fn unbond_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::unbond_other(Origin::signed(11), 11),
				Error::<Runtime>::DelegatorNotFound
			);

			// Add the delegator
			let delegator = Delegator {
				pool_id: 2,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator);

			let _ = Pools::unbond_other(Origin::signed(11), 11);
		});
	}

	#[test]
	#[should_panic = "Defensive failure has been triggered!"]
	fn unbond_panics_when_reward_pool_not_found() {
		ExtBuilder::default().build_and_execute(|| {
			let delegator = Delegator {
				pool_id: 2,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator);
			BondedPool::<Runtime> {
				id: 1,
				inner: BondedPoolInner {
					state: PoolState::Open,
					points: 10,
					delegator_counter: 1,
					roles: DEFAULT_ROLES,
				},
			}
			.put();

			let _ = Pools::unbond_other(Origin::signed(11), 11);
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
			assert_eq!(StakingMock::bonded_balance(&default_bonded_account()), Some(5));
			assert_eq!(StakingMock::locked_balance(&default_bonded_account()), Some(10));
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);

			// When
			assert_ok!(Pools::pool_withdraw_unbonded(Origin::signed(10), 1, 0));

			// Then there unbonding balance is no longer locked
			assert_eq!(StakingMock::bonded_balance(&default_bonded_account()), Some(5));
			assert_eq!(StakingMock::locked_balance(&default_bonded_account()), Some(5));
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);
		});
	}
}

mod withdraw_unbonded_other {
	use super::*;

	#[test]
	fn withdraw_unbonded_other_works_against_slashed_no_era_sub_pool() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given
				assert_eq!(StakingMock::bonding_duration(), 3);
				assert_ok!(Pools::unbond_other(Origin::signed(550), 550));
				assert_ok!(Pools::unbond_other(Origin::signed(40), 40));
				assert_eq!(Balances::free_balance(&default_bonded_account()), 600);

				let mut current_era = 1;
				CurrentEra::set(current_era);
				// In a new era, unbond the depositor
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				let mut sub_pools = SubPoolsStorage::<Runtime>::get(1).unwrap();
				// TODO: [now] in the future we could use StakingMock::unbond_era_for(current_era)
				// instead of current_era + 3.
				let unbond_pool = sub_pools.with_era.get_mut(&(current_era + 3)).unwrap();
				// Sanity check
				assert_eq!(*unbond_pool, UnbondPool { points: 10, balance: 10 });

				// Simulate a slash to the pool with_era(current_era), decreasing the balance by
				// half
				unbond_pool.balance = 5;
				SubPoolsStorage::<Runtime>::insert(1, sub_pools);
				// Update the equivalent of the unbonding chunks for the `StakingMock`
				UNBONDING_BALANCE_MAP
					.with(|m| *m.borrow_mut().get_mut(&default_bonded_account()).unwrap() -= 5);
				Balances::make_free_balance_be(&default_bonded_account(), 595);

				// Advance the current_era to ensure all `with_era` pools will be merged into
				// `no_era` pool
				current_era += TotalUnbondingPools::<Runtime>::get();
				CurrentEra::set(current_era);

				// Simulate some other call to unbond that would merge `with_era` pools into
				// `no_era`
				let sub_pools =
					SubPoolsStorage::<Runtime>::get(1).unwrap().maybe_merge_pools(current_era + 3);
				SubPoolsStorage::<Runtime>::insert(1, sub_pools);
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: UnbondPool { points: 550 + 40 + 10, balance: 550 + 40 + 5 },
						with_era: Default::default()
					}
				);

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().no_era,
					UnbondPool { points: 40 + 10, balance: 40 + 5 + 5 }
				);
				assert_eq!(Balances::free_balance(&550), 550 + 545);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 50);
				assert!(!Delegators::<Runtime>::contains_key(550));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(40), 40, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap().no_era,
					UnbondPool { points: 10, balance: 10 }
				);
				assert_eq!(Balances::free_balance(&40), 40 + 40);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 50 - 40);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

				// Then
				assert_eq!(Balances::free_balance(&10), 10 + 10);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 0);
				assert!(!Delegators::<Runtime>::contains_key(10));
				// Pools are removed from storage because the depositor left
				assert!(!SubPoolsStorage::<Runtime>::contains_key(1),);
				assert!(!RewardPools::<Runtime>::contains_key(1),);
				assert!(!BondedPools::<Runtime>::contains_key(1),);
			});
	}

	// This test also documents the case when the pools free balance goes below ED before all
	// delegators have unbonded.
	#[test]
	fn withdraw_unbonded_other_works_against_slashed_with_era_sub_pools() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given
				StakingMock::set_bonded_balance(default_bonded_account(), 100); // slash bonded balance
				Balances::make_free_balance_be(&default_bonded_account(), 100);
				assert_eq!(StakingMock::locked_balance(&default_bonded_account()), Some(100));

				assert_ok!(Pools::unbond_other(Origin::signed(40), 40));
				assert_ok!(Pools::unbond_other(Origin::signed(550), 550));
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				SubPoolsStorage::<Runtime>::insert(
					1,
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! { 0 + 3 => UnbondPool { points: 600, balance: 100 }},
					},
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(40), 40, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 560, balance: 94 }}
				);
				assert_eq!(Balances::free_balance(&40), 40 + 6);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 94);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&1).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 2 }}
				);
				assert_eq!(Balances::free_balance(&550), 550 + 92);
				// The account was dusted because it went below ED(5)
				assert_eq!(Balances::free_balance(&default_bonded_account()), 0);
				assert!(!Delegators::<Runtime>::contains_key(550));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

				// Then
				assert_eq!(Balances::free_balance(&10), 10 + 0);
				assert_eq!(Balances::free_balance(&default_bonded_account()), 0);
				assert!(!Delegators::<Runtime>::contains_key(10));
				// Pools are removed from storage because the depositor left
				assert!(!SubPoolsStorage::<Runtime>::contains_key(1),);
				assert!(!RewardPools::<Runtime>::contains_key(1),);
				assert!(!BondedPools::<Runtime>::contains_key(1),);
			});
	}

	#[test]
	fn withdraw_unbonded_other_handles_faulty_sub_pool_accounting() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(Balances::minimum_balance(), 5);
			assert_eq!(Balances::free_balance(&10), 10);
			assert_eq!(Balances::free_balance(&default_bonded_account()), 10);
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			// Simulate a slash that is not accounted for in the sub pools.
			Balances::make_free_balance_be(&default_bonded_account(), 5);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap().with_era,
				//------------------------------balance decrease is not account for
				sub_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 10 } }
			);

			CurrentEra::set(0 + 3);

			// When
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

			// Then
			assert_eq!(Balances::free_balance(10), 10 + 5);
			assert_eq!(Balances::free_balance(&default_bonded_account()), 0);
		});
	}

	#[test]
	fn withdraw_unbonded_other_errors_correctly() {
		ExtBuilder::default().build_and_execute_no_checks(|| {
			// Insert the sub-pool
			let sub_pools = SubPools {
				no_era: Default::default(),
				with_era: sub_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 10  }},
			};
			SubPoolsStorage::<Runtime>::insert(123, sub_pools.clone());

			assert_noop!(
				Pools::withdraw_unbonded_other(Origin::signed(11), 11, 0),
				Error::<Runtime>::DelegatorNotFound
			);

			let mut delegator = Delegator {
				pool_id: 1,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator.clone());

			// The delegator has not called `unbond`
			assert_noop!(
				Pools::withdraw_unbonded_other(Origin::signed(11), 11, 0),
				Error::<Runtime>::NotUnbonding
			);

			// Simulate calling `unbond`
			delegator.unbonding_era = Some(0 + 3);
			Delegators::<Runtime>::insert(11, delegator.clone());

			// We are still in the bonding duration
			assert_noop!(
				Pools::withdraw_unbonded_other(Origin::signed(11), 11, 0),
				Error::<Runtime>::NotUnbondedYet
			);

			// If we error the delegator does not get removed
			assert_eq!(Delegators::<Runtime>::get(&11), Some(delegator));
			// and the sub pools do not get updated.
			assert_eq!(SubPoolsStorage::<Runtime>::get(123).unwrap(), sub_pools)
		});
	}

	#[test]
	fn withdraw_unbonded_other_kick() {
		ExtBuilder::default()
			.add_delegators(vec![(100, 100), (200, 200)])
			.build_and_execute(|| {
				// Given
				assert_ok!(Pools::unbond_other(Origin::signed(100), 100));
				assert_ok!(Pools::unbond_other(Origin::signed(200), 200));
				assert_eq!(
					BondedPool::<Runtime>::get(1).unwrap(),
					BondedPool {
						id: 1,
						inner: BondedPoolInner {
							points: 10,
							state: PoolState::Open,
							delegator_counter: 3,
							roles: DEFAULT_ROLES
						}
					}
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// Cannot kick when pool is open
				assert_noop!(
					Pools::withdraw_unbonded_other(Origin::signed(902), 100, 0),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// Given
				unsafe_set_state(1, PoolState::Blocked).unwrap();

				// Cannot kick as a nominator
				assert_noop!(
					Pools::withdraw_unbonded_other(Origin::signed(901), 100, 0),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// Can kick as root
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(900), 100, 0));

				// Can kick as state toggler
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(900), 200, 0));

				assert_eq!(Balances::free_balance(100), 100 + 100);
				assert_eq!(Balances::free_balance(200), 200 + 200);
				assert!(!Delegators::<Runtime>::contains_key(100));
				assert!(!Delegators::<Runtime>::contains_key(200));
				assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default());
			});
	}

	#[test]
	fn withdraw_unbonded_other_destroying_permissionless() {
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given
			assert_ok!(Pools::unbond_other(Origin::signed(100), 100));
			assert_eq!(
				BondedPool::<Runtime>::get(1).unwrap(),
				BondedPool {
					id: 1,
					inner: BondedPoolInner {
						points: 10,
						state: PoolState::Open,
						delegator_counter: 2,
						roles: DEFAULT_ROLES,
					}
				}
			);
			CurrentEra::set(StakingMock::bonding_duration());
			assert_eq!(Balances::free_balance(100), 100);

			// Cannot permissionlessly withdraw
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 100),
				Error::<Runtime>::NotKickerOrDestroying
			);

			// Given
			unsafe_set_state(1, PoolState::Destroying).unwrap();

			// Can permissionlesly withdraw a delegator that is not the depositor
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 100, 0));

			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), Default::default(),);
			assert_eq!(Balances::free_balance(100), 100 + 100);
			assert!(!Delegators::<Runtime>::contains_key(100));
		});
	}

	#[test]
	fn withdraw_unbonded_other_depositor_with_era_pool() {
		ExtBuilder::default()
			.add_delegators(vec![(100, 100), (200, 200)])
			.build_and_execute(|| {
				// Given
				assert_ok!(Pools::unbond_other(Origin::signed(100), 100));

				let mut current_era = 1;
				CurrentEra::set(current_era);

				assert_ok!(Pools::unbond_other(Origin::signed(200), 200));
				unsafe_set_state(1, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 + 3 => UnbondPool { points: 100, balance: 100},
							1 + 3 => UnbondPool { points: 200 + 10, balance: 200 + 10 }
						}
					}
				);
				// Skip ahead eras to where its valid for the delegators to withdraw
				current_era += StakingMock::bonding_duration();
				CurrentEra::set(current_era);

				// Cannot withdraw the depositor if their is a delegator in another `with_era` pool.
				assert_noop!(
					Pools::withdraw_unbonded_other(Origin::signed(420), 10, 0),
					Error::<Runtime>::NotOnlyDelegator
				);

				// Given
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 100, 0));
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							// Note that era 0+3 unbond pool is destroyed because points went to 0
							1 + 3 => UnbondPool { points: 200 + 10, balance: 200 + 10 }
						}
					}
				);

				// Cannot withdraw if their is another delegator in the depositors `with_era` pool
				assert_noop!(
					Pools::unbond_other(Origin::signed(420), 10),
					Error::<Runtime>::NotOnlyDelegator
				);

				// Given
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 200, 0));
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(1).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							1 + 3 => UnbondPool { points: 10, balance: 10 }
						}
					}
				);

				// The depositor can withdraw
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 10, 0));
				assert!(!Delegators::<Runtime>::contains_key(10));
				assert_eq!(Balances::free_balance(10), 10 + 10);
				// Pools are removed from storage because the depositor left
				assert!(!SubPoolsStorage::<Runtime>::contains_key(1));
				assert!(!RewardPools::<Runtime>::contains_key(1));
				assert!(!BondedPools::<Runtime>::contains_key(1));
			});
	}

	#[test]
	fn withdraw_unbonded_other_depositor_no_era_pool() {
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given
			assert_ok!(Pools::unbond_other(Origin::signed(100), 100));
			unsafe_set_state(1, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));
			// Skip ahead to an era where the `with_era` pools can get merged into the `no_era`
			// pool.
			let current_era = TotalUnbondingPools::<Runtime>::get();
			CurrentEra::set(current_era);

			// Simulate some other withdraw that caused the pool to merge
			let sub_pools =
				SubPoolsStorage::<Runtime>::get(1).unwrap().maybe_merge_pools(current_era + 3);
			SubPoolsStorage::<Runtime>::insert(1, sub_pools);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: UnbondPool { points: 100 + 10, balance: 100 + 10 },
					with_era: Default::default(),
				}
			);

			// Cannot withdraw depositor with another delegator in the `no_era` pool
			assert_noop!(
				Pools::withdraw_unbonded_other(Origin::signed(420), 10, 0),
				Error::<Runtime>::NotOnlyDelegator
			);

			// Given
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 100, 0));
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(1).unwrap(),
				SubPools {
					no_era: UnbondPool { points: 10, balance: 10 },
					with_era: Default::default(),
				}
			);

			// The depositor can withdraw
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 10, 0));
			assert!(!Delegators::<Runtime>::contains_key(10));
			assert_eq!(Balances::free_balance(10), 10 + 10);
			// Pools are removed from storage because the depositor left
			assert!(!SubPoolsStorage::<Runtime>::contains_key(1));
			assert!(!RewardPools::<Runtime>::contains_key(1));
			assert!(!BondedPools::<Runtime>::contains_key(1));
		});
	}
}

mod create {
	use super::*;

	#[test]
	fn create_works() {
		ExtBuilder::default().build_and_execute(|| {
			// next pool id is 2.
			let next_pool_stash = Pools::create_bonded_account(2);

			assert!(!BondedPools::<Runtime>::contains_key(2));
			assert!(!RewardPools::<Runtime>::contains_key(2));
			assert!(!Delegators::<Runtime>::contains_key(11));
			assert_eq!(StakingMock::bonded_balance(&next_pool_stash), None);

			Balances::make_free_balance_be(&11, StakingMock::minimum_bond());
			assert_ok!(Pools::create(
				Origin::signed(11),
				StakingMock::minimum_bond(),
				123,
				456,
				789
			));

			assert_eq!(Balances::free_balance(&11), 0);
			assert_eq!(
				Delegators::<Runtime>::get(11).unwrap(),
				Delegator {
					pool_id: 2,
					points: StakingMock::minimum_bond(),
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None
				}
			);
			assert_eq!(
				BondedPool::<Runtime>::get(2).unwrap(),
				BondedPool {
					id: 2,
					inner: BondedPoolInner {
						points: StakingMock::minimum_bond(),
						delegator_counter: 1,
						state: PoolState::Open,
						roles: PoolRoles {
							depositor: 11,
							root: 123,
							nominator: 456,
							state_toggler: 789
						}
					}
				}
			);
			assert_eq!(
				StakingMock::bonded_balance(&next_pool_stash).unwrap(),
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
		});
	}

	#[test]
	fn create_errors_correctly() {
		ExtBuilder::default().build_and_execute_no_checks(|| {
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
					delegator_counter: 1,
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
			assert_eq!(Delegators::<Runtime>::count(), 1);
			MaxPools::<Runtime>::put(3);
			MaxDelegators::<Runtime>::put(1);

			// Then
			assert_noop!(
				Pools::create(Origin::signed(11), 20, 11, 11, 11),
				Error::<Runtime>::MaxDelegators
			);
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
			assert_eq!(Nominations::get(), vec![21]);

			// Nominator can nominate
			assert_ok!(Pools::nominate(Origin::signed(901), 1, vec![31]));
			assert_eq!(Nominations::get(), vec![31]);

			// Can't nominate for a pool that doesn't exist
			assert_noop!(
				Pools::nominate(Origin::signed(902), 123, vec![21]),
				Error::<Runtime>::PoolNotFound
			);
		});
	}
}

mod set_state_other {
	use super::*;

	#[test]
	fn set_state_other_works() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_ok!(BondedPool::<Runtime>::get(1).unwrap().ok_to_be_open());

			// Only the root and state toggler can change the state when the pool is ok to be open.
			assert_noop!(
				Pools::set_state_other(Origin::signed(10), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state_other(Origin::signed(901), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// Root can change state
			assert_ok!(Pools::set_state_other(Origin::signed(900), 1, PoolState::Blocked));
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Blocked);

			// State toggler can change state
			assert_ok!(Pools::set_state_other(Origin::signed(902), 1, PoolState::Destroying));
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// If the pool is destroying, then no one can set state
			assert_noop!(
				Pools::set_state_other(Origin::signed(900), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state_other(Origin::signed(902), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// If the pool is not ok to be open, then anyone can set it to destroying

			// Given
			unsafe_set_state(1, PoolState::Open).unwrap();
			let mut bonded_pool = BondedPool::<Runtime>::get(1).unwrap();
			bonded_pool.points = 100;
			bonded_pool.put();
			// When
			assert_ok!(Pools::set_state_other(Origin::signed(11), 1, PoolState::Destroying));
			// Then
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// Given
			Balances::make_free_balance_be(&default_bonded_account(), Balance::max_value() / 10);
			unsafe_set_state(1, PoolState::Open).unwrap();
			// When
			assert_ok!(Pools::set_state_other(Origin::signed(11), 1, PoolState::Destroying));
			// Then
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().state, PoolState::Destroying);

			// If the pool is not ok to be open, it cannot be permissionleslly set to a state that
			// isn't destroying
			unsafe_set_state(1, PoolState::Open).unwrap();
			assert_noop!(
				Pools::set_state_other(Origin::signed(11), 1, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
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
			assert_eq!(MaxDelegators::<Runtime>::get(), Some(4));
			assert_eq!(MaxDelegatorsPerPool::<Runtime>::get(), Some(5));

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
				ConfigOp::Remove
			));
			assert_eq!(MinJoinBond::<Runtime>::get(), 0);
			assert_eq!(MinCreateBond::<Runtime>::get(), 0);
			assert_eq!(MaxPools::<Runtime>::get(), None);
			assert_eq!(MaxDelegators::<Runtime>::get(), None);
			assert_eq!(MaxDelegatorsPerPool::<Runtime>::get(), None);
		});
	}
}
