use super::*;
use crate::mock::{
	unsafe_set_state, Balance, Balances, CurrentEra, ExistentialDeposit, ExtBuilder, Nominations,
	Origin, Pools, Runtime, StakingMock, PRIMARY_ACCOUNT, REWARDS_ACCOUNT, UNBONDING_BALANCE_MAP,
};
use frame_support::{assert_noop, assert_ok};

macro_rules! sub_pools_with_era {
	($($k:expr => $v:expr),* $(,)?) => {{
		use sp_std::iter::{Iterator, IntoIterator};
		let not_bounded: BTreeMap<_, _> = Iterator::collect(IntoIterator::into_iter([$(($k, $v),)*]));
		SubPoolsWithEra::try_from(not_bounded).unwrap()
	}};
}

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(BondedPools::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(Delegators::<Runtime>::count(), 1);
		assert_eq!(StakingMock::bonding_duration(), 3);

		assert_eq!(
			BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
			BondedPool::<Runtime> {
				depositor: 10,
				state: PoolState::Open,
				points: 10,
				account: PRIMARY_ACCOUNT,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
			}
		);
		assert_eq!(
			RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
			RewardPool::<Runtime> {
				balance: 0,
				points: 0.into(),
				total_earnings: 0,
				account: REWARDS_ACCOUNT
			}
		);
		assert_eq!(
			Delegators::<Runtime>::get(10).unwrap(),
			Delegator::<Runtime> {
				pool: PRIMARY_ACCOUNT,
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
			depositor: 10,
			state: PoolState::Open,
			points: 100,
			account: 123,
			root: 900,
			nominator: 901,
			state_toggler: 902,
			delegator_counter: 1,
		};

		// 1 points : 1 balance ratio
		StakingMock::set_bonded_balance(123, 100);
		assert_eq!(bonded_pool.points_to_issue(10), 10);
		assert_eq!(bonded_pool.points_to_issue(0), 0);

		// 2 points : 1 balance ratio
		StakingMock::set_bonded_balance(123, 50);
		assert_eq!(bonded_pool.points_to_issue(10), 20);

		// 1 points : 2 balance ratio
		StakingMock::set_bonded_balance(123, 100);
		bonded_pool.points = 50;
		assert_eq!(bonded_pool.points_to_issue(10), 5);

		// 100 points : 0 balance ratio
		StakingMock::set_bonded_balance(123, 0);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.points_to_issue(10), 100 * 10);

		// 0 points : 100 balance
		StakingMock::set_bonded_balance(123, 100);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.points_to_issue(10), 10);

		// 10 points : 3 balance ratio
		StakingMock::set_bonded_balance(123, 30);
		assert_eq!(bonded_pool.points_to_issue(10), 33);

		// 2 points : 3 balance ratio
		StakingMock::set_bonded_balance(123, 300);
		bonded_pool.points = 200;
		assert_eq!(bonded_pool.points_to_issue(10), 6);

		// 4 points : 9 balance ratio
		StakingMock::set_bonded_balance(123, 900);
		bonded_pool.points = 400;
		assert_eq!(bonded_pool.points_to_issue(90), 40);
	}

	#[test]
	fn balance_to_unbond_works() {
		// 1 balance : 1 points ratio
		let mut bonded_pool = BondedPool::<Runtime> {
			depositor: 10,
			state: PoolState::Open,
			points: 100,
			account: 123,
			root: 900,
			nominator: 901,
			state_toggler: 902,
			delegator_counter: 1,
		};
		StakingMock::set_bonded_balance(123, 100);
		assert_eq!(bonded_pool.balance_to_unbond(10), 10);
		assert_eq!(bonded_pool.balance_to_unbond(0), 0);

		// 2 balance : 1 points ratio
		bonded_pool.points = 50;
		assert_eq!(bonded_pool.balance_to_unbond(10), 20);

		// 100 balance : 0 points ratio
		StakingMock::set_bonded_balance(123, 0);
		bonded_pool.points = 0;
		assert_eq!(bonded_pool.balance_to_unbond(10), 0);

		// 0 balance : 100 points ratio
		StakingMock::set_bonded_balance(123, 0);
		bonded_pool.points = 100;
		assert_eq!(bonded_pool.balance_to_unbond(10), 0);

		// 10 balance : 3 points ratio
		StakingMock::set_bonded_balance(123, 100);
		bonded_pool.points = 30;
		assert_eq!(bonded_pool.balance_to_unbond(10), 33);

		// 2 balance : 3 points ratio
		StakingMock::set_bonded_balance(123, 200);
		bonded_pool.points = 300;
		assert_eq!(bonded_pool.balance_to_unbond(10), 6);

		// 4 balance : 9 points ratio
		StakingMock::set_bonded_balance(123, 400);
		bonded_pool.points = 900;
		assert_eq!(bonded_pool.balance_to_unbond(90), 40);
	}

	#[test]
	fn ok_to_join_with_works() {
		ExtBuilder::default().build_and_execute(|| {
			let pool = BondedPool::<Runtime> {
				depositor: 10,
				state: PoolState::Open,
				points: 100,
				account: 123,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
			};

			// Simulate a 100% slashed pool
			StakingMock::set_bonded_balance(123, 0);
			assert_noop!(pool.ok_to_join_with(100, &11), Error::<Runtime>::OverflowRisk);

			// Simulate a 89%
			StakingMock::set_bonded_balance(123, 11);
			assert_ok!(pool.ok_to_join_with(100, &11));

			// Simulate a 90% slashed pool
			StakingMock::set_bonded_balance(123, 10);
			assert_noop!(pool.ok_to_join_with(100, &11), Error::<Runtime>::OverflowRisk);

			let bonded = 100;
			StakingMock::set_bonded_balance(123, bonded);
			// New bonded balance would be over 1/10th of Balance type
			assert_noop!(
				pool.ok_to_join_with(Balance::MAX / 10 - bonded, &11),
				Error::<Runtime>::OverflowRisk
			);
			// and a sanity check
			assert_ok!(pool.ok_to_join_with(Balance::MAX / 100 - bonded + 1, &11));
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
			depositor: 10,
			state: PoolState::Open,
			points,
			account: PRIMARY_ACCOUNT,
			root: 900,
			nominator: 901,
			state_toggler: 902,
			delegator_counter,
		};
		ExtBuilder::default().build_and_execute(|| {
			// Given
			Balances::make_free_balance_be(&11, ExistentialDeposit::get() + 2);
			assert!(!Delegators::<Runtime>::contains_key(&11));

			// When
			assert_ok!(Pools::join(Origin::signed(11), 2, PRIMARY_ACCOUNT));

			// then
			assert_eq!(
				Delegators::<Runtime>::get(&11).unwrap(),
				Delegator::<Runtime> {
					pool: PRIMARY_ACCOUNT,
					points: 2,
					reward_pool_total_earnings: 0,
					unbonding_era: None
				}
			);
			assert_eq!(BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), bonded(12, 2));

			// Given
			// The bonded balance is slashed in half
			StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 6);
			// And
			Balances::make_free_balance_be(&12, ExistentialDeposit::get() + 12);
			assert!(!Delegators::<Runtime>::contains_key(&12));

			// When
			assert_ok!(Pools::join(Origin::signed(12), 12, PRIMARY_ACCOUNT));

			// Then
			assert_eq!(
				Delegators::<Runtime>::get(&12).unwrap(),
				Delegator::<Runtime> {
					pool: PRIMARY_ACCOUNT,
					points: 24,
					reward_pool_total_earnings: 0,
					unbonding_era: None
				}
			);
			assert_eq!(BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), bonded(12 + 24, 3));
		});
	}

	#[test]
	fn join_errors_correctly() {
		ExtBuilder::default().build_and_execute_no_checks(|| {
			assert_noop!(
				Pools::join(Origin::signed(10), 420, PRIMARY_ACCOUNT),
				Error::<Runtime>::AccountBelongsToOtherPool
			);

			assert_noop!(Pools::join(Origin::signed(11), 420, 420), Error::<Runtime>::PoolNotFound);

			// Force the pools bonded balance to 0, simulating a 100% slash
			StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 0);
			assert_noop!(
				Pools::join(Origin::signed(11), 420, PRIMARY_ACCOUNT),
				Error::<Runtime>::OverflowRisk
			);

			BondedPool::<Runtime> {
				depositor: 10,
				state: PoolState::Open,
				points: 100,
				account: 123,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
			}
			.put();
			// Force the points:balance ratio to 100/10 (so 10)
			StakingMock::set_bonded_balance(123, 10);
			assert_noop!(Pools::join(Origin::signed(11), 420, 123), Error::<Runtime>::OverflowRisk);

			// Force the points:balance ratio to be a valid 100/100
			StakingMock::set_bonded_balance(123, 100);
			// Cumulative balance is > 1/10 of Balance::MAX
			assert_noop!(
				Pools::join(Origin::signed(11), Balance::MAX / 10 - 100, 123),
				Error::<Runtime>::OverflowRisk
			);

			// Cannot join a pool that isn't open
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Blocked).unwrap();
			assert_noop!(
				Pools::join(Origin::signed(11), 10, PRIMARY_ACCOUNT),
				Error::<Runtime>::NotOpen
			);
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
			assert_noop!(
				Pools::join(Origin::signed(11), 10, PRIMARY_ACCOUNT),
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
	#[should_panic = "Defensive failure has been triggered!"]
	fn join_panics_when_reward_pool_not_found() {
		ExtBuilder::default().build_and_execute(|| {
			StakingMock::set_bonded_balance(123, 100);
			BondedPool::<Runtime> {
				depositor: 10,
				state: PoolState::Open,
				points: 100,
				account: 123,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
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

				assert_ok!(Pools::join(Origin::signed(account), 100, PRIMARY_ACCOUNT));
			}

			Balances::make_free_balance_be(&103, 100 + Balances::minimum_balance());

			// Then
			assert_noop!(
				Pools::join(Origin::signed(103), 100, PRIMARY_ACCOUNT),
				Error::<Runtime>::MaxDelegators
			);

			// Given
			assert_eq!(Delegators::<Runtime>::count(), 3);
			assert_eq!(MaxDelegators::<Runtime>::get(), Some(4));
			Balances::make_free_balance_be(&104, 100 + Balances::minimum_balance());
			assert_ok!(Pools::create(Origin::signed(104), 100, 104, 104, 104));
			let pool_account = BondedPools::<Runtime>::iter()
				.find(|(_, bonded_pool)| bonded_pool.depositor == 104)
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
		Delegator { pool: PRIMARY_ACCOUNT, points, reward_pool_total_earnings, unbonding_era: None }
	}

	fn rew(balance: Balance, points: u32, total_earnings: Balance) -> RewardPool<Runtime> {
		RewardPool { balance, points: points.into(), total_earnings, account: REWARDS_ACCOUNT }
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
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 100);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 90);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(45, 5_000 - 50 * 10, 150)
				);
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 45);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(25, 4_500 - 50 * 40, 150)
				);
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 75);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 25);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// We expect a payout of 5
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(20, 2_500 - 10 * 50, 200)
				);
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 420);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// We expect a payout of 40
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 20));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 400);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 398);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 210);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);
			});
	}

	#[test]
	fn calculate_delegator_payout_errors_if_a_delegator_is_unbonding() {
		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			let reward_pool = RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			delegator.unbonding_era = Some(0 + 3);

			assert_noop!(
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator),
				Error::<Runtime>::AlreadyUnbonding
			);
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_1() {
		let del = |reward_pool_total_earnings| del(10, reward_pool_total_earnings);

		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			let reward_pool = RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			let delegator = Delegators::<Runtime>::get(10).unwrap();

			// Given no rewards have been earned
			// When
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator).unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(delegator, del(0));
			assert_eq!(reward_pool, rew(0, 0, 0));

			// Given the pool has earned some rewards for the first time
			Balances::make_free_balance_be(&reward_pool.account, 5);

			// When
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator).unwrap();

			// Then
			assert_eq!(payout, 5); //  (10 * 5 del virtual points / 10 * 5 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 5));
			assert_eq!(delegator, del(5));

			// Given the pool has earned rewards again
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 10);

			// When
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator).unwrap();

			// Then
			assert_eq!(payout, 10); // (10 * 10 del virtual points / 10 pool points) * 5 pool balance
			assert_eq!(reward_pool, rew(0, 0, 15));
			assert_eq!(delegator, del(15));

			// Given the pool has earned no new rewards
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 0);

			// When
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator).unwrap();

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
				let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
				let reward_pool = RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
				// Delegator with 10 points
				let del_10 = Delegators::<Runtime>::get(10).unwrap();
				// Delegator with 40 points
				let del_40 = Delegators::<Runtime>::get(40).unwrap();
				// Delegator with 50 points
				let del_50 = Delegators::<Runtime>::get(50).unwrap();

				// Given we have a total of 100 points split among the delegators
				assert_eq!(del_50.points + del_40.points + del_10.points, 100);
				assert_eq!(bonded_pool.points, 100);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 100);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 10); // (10 del virtual points / 100 pool points) * 100 pool balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(reward_pool, rew(90, 100 * 100 - 100 * 10, 100));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 10));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_40).unwrap();

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
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 40));

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_50).unwrap();

				// Then
				assert_eq!(payout, 50); // (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(reward_pool, rew(0, 0, 100));
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 50));

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 5); // (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(reward_pool, rew(45, 5_000 - 50 * 10, 150));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 5));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_40).unwrap();

				// Then
				assert_eq!(payout, 20); // (2,000 del virtual points / 4,500 pool points) * 45 pool balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(reward_pool, rew(25, 4_500 - 50 * 40, 150));
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 20));

				// Given del_50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 75);

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_50).unwrap();

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
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 50));

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 5);
				assert_eq!(del_10, del(10, 200));
				assert_eq!(reward_pool, rew(20, 2_500 - 10 * 50, 200));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 5));

				// Given del_40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 420);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_10).unwrap();

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
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 40));

				// Given del_40 + del_50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 20));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 400);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 2); // (200 del virtual points / 38,000 pool points) * 400 pool balance
				assert_eq!(del_10, del(10, 620));
				assert_eq!(reward_pool, rew(398, (38_000 + 20 * 100) - 10 * 20, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 2));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_40).unwrap();

				// Then
				assert_eq!(payout, 188); // (18,800 del virtual points /  39,800 pool points) * 399 pool balance
				assert_eq!(del_40, del(40, 620));
				assert_eq!(reward_pool, rew(210, 39_800 - 40 * 470, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 188));

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&bonded_pool, reward_pool, del_50).unwrap();

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
				let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();

				// Given the bonded pool has 100 points
				assert_eq!(bonded_pool.points, 100);
				// Each delegator currently has a free balance of
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 100);

				// When
				assert_ok!(Pools::do_reward_payout(10, Delegators::get(10).unwrap(), &bonded_pool));

				// Then
				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 90);

				// When
				assert_ok!(Pools::do_reward_payout(40, Delegators::get(40).unwrap(), &bonded_pool));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 50);

				// When
				assert_ok!(Pools::do_reward_payout(50, Delegators::get(50).unwrap(), &bonded_pool));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				assert_ok!(Pools::do_reward_payout(10, Delegators::get(10).unwrap(), &bonded_pool));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(45, 5_000 - 50 * 10, 150)
				);
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 45);

				// When
				assert_ok!(Pools::do_reward_payout(40, Delegators::get(40).unwrap(), &bonded_pool));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(25, 4_500 - 50 * 40, 150)
				);
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 75);

				// When
				assert_ok!(Pools::do_reward_payout(50, Delegators::get(50).unwrap(), &bonded_pool));

				// Then
				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 25);

				// When
				assert_ok!(Pools::do_reward_payout(10, Delegators::get(10).unwrap(), &bonded_pool));

				// Then
				// We expect a payout of 5
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(20, 2_500 - 10 * 50, 200)
				);
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 420);

				// When
				assert_ok!(Pools::do_reward_payout(10, Delegators::get(10).unwrap(), &bonded_pool));

				// Then
				// We expect a payout of 40
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 380);

				// Given del 40 + del 50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 20));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 400);

				// When
				assert_ok!(Pools::do_reward_payout(10, Delegators::get(10).unwrap(), &bonded_pool));

				// Then
				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(Delegators::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 398);

				// When
				assert_ok!(Pools::do_reward_payout(40, Delegators::get(40).unwrap(), &bonded_pool));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(Delegators::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 210);

				// When
				assert_ok!(Pools::do_reward_payout(50, Delegators::get(50).unwrap(), &bonded_pool));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(Delegators::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);
			});
	}

	#[test]
	fn do_reward_payout_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();

			// The only place this can return an error is with the balance transfer from the
			// reward  account to the delegator, and as far as this comment author can tell this
			// can only if storage is in a bad state prior to `do_reward_payout` being called.

			// Given
			delegator.points = 15;
			assert_eq!(bonded_pool.points, 10);
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 10);

			// Then
			// Expect attempt payout of 15/10 * 10 when free balance is actually 10
			assert_noop!(
				Pools::do_reward_payout(10, delegator, &bonded_pool),
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
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
				sub_pools_with_era! { 0 + 3 => UnbondPool::<Runtime> { points: 10, balance: 10 }}
			);

			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				BondedPool {
					depositor: 10,
					state: PoolState::Destroying,
					points: 0,
					account: PRIMARY_ACCOUNT,
					root: 900,
					nominator: 901,
					state_toggler: 902,
					delegator_counter: 1,
				}
			);

			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 0);
		});
	}

	#[test]
	fn unbond_other_of_3_works() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given a slash from 600 -> 100
				StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 100);
				// and unclaimed rewards of 600.
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 600);

				// When
				assert_ok!(Pools::unbond_other(Origin::signed(40), 40));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 6, balance: 6 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool {
						depositor: 10,
						state: PoolState::Open,
						points: 560,
						account: PRIMARY_ACCOUNT,
						root: 900,
						nominator: 901,
						state_toggler: 902,
						delegator_counter: 3,
					}
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 94);
				assert_eq!(Delegators::<Runtime>::get(40).unwrap().unbonding_era, Some(0 + 3));
				assert_eq!(Balances::free_balance(&40), 40 + 40); // We claim rewards when unbonding

				// When
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(550), 550));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 98, balance: 98 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool {
						depositor: 10,
						state: PoolState::Destroying,
						points: 10,
						account: PRIMARY_ACCOUNT,
						root: 900,
						nominator: 901,
						state_toggler: 902,
						delegator_counter: 3,
					}
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 2);
				assert_eq!(Delegators::<Runtime>::get(550).unwrap().unbonding_era, Some(0 + 3));
				assert_eq!(Balances::free_balance(&550), 550 + 550);

				// When
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 100, balance: 100 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool {
						depositor: 10,
						state: PoolState::Destroying,
						points: 0,
						account: PRIMARY_ACCOUNT,
						root: 900,
						nominator: 901,
						state_toggler: 902,
						delegator_counter: 3,
					}
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 0);
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
				PRIMARY_ACCOUNT,
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
						0 + 3 => UnbondPool { balance: 10, points: 100 },
						1 + 3 => UnbondPool { balance: 20, points: 20 },
						2 + 3 => UnbondPool { balance: 101, points: 101}
					},
				},
			);
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();

			// When
			let current_era = 1 + TotalUnbondingPools::<Runtime>::get();
			CurrentEra::set(current_era);

			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Blocked).unwrap();
				let bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
				assert_eq!(bonded_pool.root, 900);
				assert_eq!(bonded_pool.nominator, 901);
				assert_eq!(bonded_pool.state_toggler, 902);

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
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool {
						root: 900,
						nominator: 901,
						state_toggler: 902,
						account: PRIMARY_ACCOUNT,
						depositor: 10,
						state: PoolState::Blocked,
						points: 10, // Only 10 points because 200 + 100 was unbonded
						delegator_counter: 3,
					}
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 10);
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 + 3 => UnbondPool { points: 100 + 200, balance: 100 + 200 }
						},
					}
				);
				assert_eq!(
					UNBONDING_BALANCE_MAP.with(|m| *m.borrow_mut().get(&PRIMARY_ACCOUNT).unwrap()),
					100 + 200
				);
			});
	}

	#[test]
	fn unbond_other_with_non_admins_works() {
		// Scenarios where non-admin accounts can unbond others
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given the pool is blocked
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Blocked).unwrap();

			// A permissionless unbond attempt errors
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 100),
				Error::<Runtime>::NotKickerOrDestroying
			);

			// Given the pool is destroying
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();

			// The depositor cannot be unbonded until they are the last delegator
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 10),
				Error::<Runtime>::NotOnlyDelegator
			);

			// Any account can unbond a delegator that is not the depositor
			assert_ok!(Pools::unbond_other(Origin::signed(420), 100));

			// Given the pool is blocked
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Blocked).unwrap();

			// The depositor cannot be unbonded
			assert_noop!(
				Pools::unbond_other(Origin::signed(420), 10),
				Error::<Runtime>::NotDestroying
			);

			// Given the pools is destroying
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();

			// The depositor can be unbonded
			assert_ok!(Pools::unbond_other(Origin::signed(420), 10));

			assert_eq!(BondedPools::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().points, 0);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
						0 + 3 => UnbondPool { points: 110, balance: 110 }
					}
				}
			);
			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 0);
			assert_eq!(
				UNBONDING_BALANCE_MAP.with(|m| *m.borrow_mut().get(&PRIMARY_ACCOUNT).unwrap()),
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
				pool: 1,
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
				pool: 1,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator);
			BondedPool::<Runtime> {
				depositor: 10,
				state: PoolState::Open,
				points: 10,
				account: 1,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
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
			assert_ok!(StakingMock::unbond(PRIMARY_ACCOUNT, 5));
			// and the pool account only has 10 balance
			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), Some(5));
			assert_eq!(StakingMock::locked_balance(&PRIMARY_ACCOUNT), Some(10));
			assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 10);

			// When
			assert_ok!(Pools::pool_withdraw_unbonded(Origin::signed(10), PRIMARY_ACCOUNT, 0));

			// Then there unbonding balance is no longer locked
			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), Some(5));
			assert_eq!(StakingMock::locked_balance(&PRIMARY_ACCOUNT), Some(5));
			assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 10);
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
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 600);

				let mut current_era = 1;
				CurrentEra::set(current_era);
				// In a new era, unbond the depositor
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				let mut sub_pools = SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
				// TODO: [now] in the future we could use StakingMock::unbond_era_for(current_era)
				// instead of current_era + 3.
				let unbond_pool = sub_pools.with_era.get_mut(&(current_era + 3)).unwrap();
				// Sanity check
				assert_eq!(*unbond_pool, UnbondPool { points: 10, balance: 10 });

				// Simulate a slash to the pool with_era(current_era), decreasing the balance by
				// half
				unbond_pool.balance = 5;
				SubPoolsStorage::<Runtime>::insert(PRIMARY_ACCOUNT, sub_pools);
				// Update the equivalent of the unbonding chunks for the `StakingMock`
				UNBONDING_BALANCE_MAP
					.with(|m| *m.borrow_mut().get_mut(&PRIMARY_ACCOUNT).unwrap() -= 5);
				Balances::make_free_balance_be(&PRIMARY_ACCOUNT, 595);

				// Advance the current_era to ensure all `with_era` pools will be merged into
				// `no_era` pool
				current_era += TotalUnbondingPools::<Runtime>::get();
				CurrentEra::set(current_era);

				// Simulate some other call to unbond that would merge `with_era` pools into
				// `no_era`
				let sub_pools = SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT)
					.unwrap()
					.maybe_merge_pools(current_era + 3);
				SubPoolsStorage::<Runtime>::insert(PRIMARY_ACCOUNT, sub_pools);
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: UnbondPool { points: 550 + 40 + 10, balance: 550 + 40 + 5 },
						with_era: Default::default()
					}
				);

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().no_era,
					UnbondPool { points: 40 + 10, balance: 40 + 5 + 5 }
				);
				assert_eq!(Balances::free_balance(&550), 550 + 545);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 50);
				assert!(!Delegators::<Runtime>::contains_key(550));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(40), 40, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().no_era,
					UnbondPool { points: 10, balance: 10 }
				);
				assert_eq!(Balances::free_balance(&40), 40 + 40);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 50 - 40);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

				// Then
				assert_eq!(Balances::free_balance(&10), 10 + 10);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!Delegators::<Runtime>::contains_key(10));
				// Pools are removed from storage because the depositor left
				assert!(!SubPoolsStorage::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!RewardPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!BondedPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
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
				StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 100); // slash bonded balance
				Balances::make_free_balance_be(&PRIMARY_ACCOUNT, 100);
				assert_eq!(StakingMock::locked_balance(&PRIMARY_ACCOUNT), Some(100));

				assert_ok!(Pools::unbond_other(Origin::signed(40), 40));
				assert_ok!(Pools::unbond_other(Origin::signed(550), 550));
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				SubPoolsStorage::<Runtime>::insert(
					PRIMARY_ACCOUNT,
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
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 560, balance: 94 }}
				);
				assert_eq!(Balances::free_balance(&40), 40 + 6);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 94);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(550), 550, 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 2 }}
				);
				assert_eq!(Balances::free_balance(&550), 550 + 92);
				// The account was dusted because it went below ED(5)
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!Delegators::<Runtime>::contains_key(550));

				// When
				assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

				// Then
				assert_eq!(Balances::free_balance(&10), 10 + 0);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!Delegators::<Runtime>::contains_key(10));
				// Pools are removed from storage because the depositor left
				assert!(!SubPoolsStorage::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!RewardPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!BondedPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
			});
	}

	#[test]
	fn withdraw_unbonded_other_handles_faulty_sub_pool_accounting() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			assert_eq!(Balances::minimum_balance(), 5);
			assert_eq!(Balances::free_balance(&10), 10);
			assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 10);
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

			// Simulate a slash that is not accounted for in the sub pools.
			Balances::make_free_balance_be(&PRIMARY_ACCOUNT, 5);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
				//------------------------------balance decrease is not account for
				sub_pools_with_era! { 0 + 3 => UnbondPool { points: 10, balance: 10 } }
			);

			CurrentEra::set(0 + 3);

			// When
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(10), 10, 0));

			// Then
			assert_eq!(Balances::free_balance(10), 10 + 5);
			assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
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
				pool: PRIMARY_ACCOUNT,
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
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool {
						points: 10,
						state: PoolState::Open,
						depositor: 10,
						account: PRIMARY_ACCOUNT,
						root: 900,
						nominator: 901,
						state_toggler: 902,
						delegator_counter: 3,
					}
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// Cannot kick when pool is open
				assert_noop!(
					Pools::withdraw_unbonded_other(Origin::signed(902), 100, 0),
					Error::<Runtime>::NotKickerOrDestroying
				);

				// Given
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Blocked).unwrap();

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
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					Default::default()
				);
			});
	}

	#[test]
	fn withdraw_unbonded_other_destroying_permissionless() {
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given
			assert_ok!(Pools::unbond_other(Origin::signed(100), 100));
			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				BondedPool {
					points: 10,
					state: PoolState::Open,
					depositor: 10,
					account: PRIMARY_ACCOUNT,
					root: 900,
					nominator: 901,
					state_toggler: 902,
					delegator_counter: 2,
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
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();

			// Can permissionlesly withdraw a delegator that is not the depositor
			assert_ok!(Pools::withdraw_unbonded_other(Origin::signed(420), 100, 0));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				Default::default(),
			);
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
				unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
				assert_ok!(Pools::unbond_other(Origin::signed(10), 10));

				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				assert!(!SubPoolsStorage::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!RewardPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
				assert!(!BondedPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT),);
			});
	}

	#[test]
	fn withdraw_unbonded_other_depositor_no_era_pool() {
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given
			assert_ok!(Pools::unbond_other(Origin::signed(100), 100));
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Destroying).unwrap();
			assert_ok!(Pools::unbond_other(Origin::signed(10), 10));
			// Skip ahead to an era where the `with_era` pools can get merged into the `no_era`
			// pool.
			let current_era = TotalUnbondingPools::<Runtime>::get();
			CurrentEra::set(current_era);

			// Simulate some other withdraw that caused the pool to merge
			let sub_pools = SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT)
				.unwrap()
				.maybe_merge_pools(current_era + 3);
			SubPoolsStorage::<Runtime>::insert(&PRIMARY_ACCOUNT, sub_pools);
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
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
			assert!(!SubPoolsStorage::<Runtime>::contains_key(&PRIMARY_ACCOUNT));
			assert!(!RewardPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT));
			assert!(!BondedPools::<Runtime>::contains_key(&PRIMARY_ACCOUNT));
		});
	}
}

mod create {
	use super::*;

	#[test]
	fn create_works() {
		ExtBuilder::default().build_and_execute(|| {
			let stash = 3548237456;

			assert!(!BondedPools::<Runtime>::contains_key(1));
			assert!(!RewardPools::<Runtime>::contains_key(1));
			assert!(!Delegators::<Runtime>::contains_key(11));
			assert_eq!(StakingMock::bonded_balance(&stash), None);

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
					pool: stash,
					points: StakingMock::minimum_bond(),
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None
				}
			);
			assert_eq!(
				BondedPool::<Runtime>::get(&stash).unwrap(),
				BondedPool {
					points: StakingMock::minimum_bond(),
					depositor: 11,
					state: PoolState::Open,
					account: stash.clone(),
					root: 123,
					nominator: 456,
					state_toggler: 789,
					delegator_counter: 1,
				}
			);
			assert_eq!(StakingMock::bonded_balance(&stash).unwrap(), StakingMock::minimum_bond());
			assert_eq!(
				RewardPools::<Runtime>::get(stash).unwrap(),
				RewardPool {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account: 1657614948
				}
			);
		});
	}

	#[test]
	fn create_errors_correctly() {
		ExtBuilder::default().build_and_execute_no_checks(|| {
			assert_noop!(
				Pools::create(Origin::signed(10), 10, 123, 456, 789),
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
				depositor: 10,
				state: PoolState::Open,
				points: 10,
				account: 123,
				root: 900,
				nominator: 901,
				state_toggler: 902,
				delegator_counter: 1,
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
				Pools::nominate(Origin::signed(10), PRIMARY_ACCOUNT, vec![21]),
				Error::<Runtime>::NotNominator
			);

			// State toggler can't nominate
			assert_noop!(
				Pools::nominate(Origin::signed(902), PRIMARY_ACCOUNT, vec![21]),
				Error::<Runtime>::NotNominator
			);

			// Root can nominate
			assert_ok!(Pools::nominate(Origin::signed(900), PRIMARY_ACCOUNT, vec![21]));
			assert_eq!(Nominations::get(), vec![21]);

			// Nominator can nominate
			assert_ok!(Pools::nominate(Origin::signed(901), PRIMARY_ACCOUNT, vec![31]));
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
			// Only the root and state toggler can change the state when the pool is ok to be open.
			assert_ok!(BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().ok_to_be_open());
			assert_noop!(
				Pools::set_state_other(Origin::signed(10), PRIMARY_ACCOUNT, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state_other(Origin::signed(901), PRIMARY_ACCOUNT, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// Root can change state
			assert_ok!(Pools::set_state_other(
				Origin::signed(900),
				PRIMARY_ACCOUNT,
				PoolState::Blocked
			));
			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().state,
				PoolState::Blocked
			);

			// State toggler can change state
			assert_ok!(Pools::set_state_other(
				Origin::signed(902),
				PRIMARY_ACCOUNT,
				PoolState::Destroying
			));
			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().state,
				PoolState::Destroying
			);

			// If the pool is destroying, then no one can set state
			assert_noop!(
				Pools::set_state_other(Origin::signed(900), PRIMARY_ACCOUNT, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);
			assert_noop!(
				Pools::set_state_other(Origin::signed(902), PRIMARY_ACCOUNT, PoolState::Blocked),
				Error::<Runtime>::CanNotChangeState
			);

			// If the pool is not ok to be open, then anyone can set it to destroying

			// Given
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Open).unwrap();
			let mut bonded_pool = BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
			bonded_pool.points = 100;
			bonded_pool.put();
			// When
			assert_ok!(Pools::set_state_other(
				Origin::signed(11),
				PRIMARY_ACCOUNT,
				PoolState::Destroying
			));
			// Then
			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().state,
				PoolState::Destroying
			);

			// Given
			Balances::make_free_balance_be(&PRIMARY_ACCOUNT, Balance::max_value() / 10);
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Open).unwrap();
			// When
			assert_ok!(Pools::set_state_other(
				Origin::signed(11),
				PRIMARY_ACCOUNT,
				PoolState::Destroying
			));
			// Then
			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().state,
				PoolState::Destroying
			);

			// If the pool is not ok to be open, it cannot be permissionleslly set to a state that
			// isn't destroying
			unsafe_set_state(&PRIMARY_ACCOUNT, PoolState::Open).unwrap();
			assert_noop!(
				Pools::set_state_other(Origin::signed(11), PRIMARY_ACCOUNT, PoolState::Blocked),
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
			assert_ok!(Pools::set_metadata(Origin::signed(900), PRIMARY_ACCOUNT, vec![1, 1]));
			assert_eq!(Metadata::<Runtime>::get(PRIMARY_ACCOUNT), vec![1, 1]);

			// State toggler can set metadata
			assert_ok!(Pools::set_metadata(Origin::signed(902), PRIMARY_ACCOUNT, vec![2, 2]));
			assert_eq!(Metadata::<Runtime>::get(PRIMARY_ACCOUNT), vec![2, 2]);

			// Depositor can't set metadata
			assert_noop!(
				Pools::set_metadata(Origin::signed(10), PRIMARY_ACCOUNT, vec![3, 3]),
				Error::<Runtime>::DoesNotHavePermission
			);

			// Nominator can't set metadata
			assert_noop!(
				Pools::set_metadata(Origin::signed(901), PRIMARY_ACCOUNT, vec![3, 3]),
				Error::<Runtime>::DoesNotHavePermission
			);

			// Metadata cannot be longer than `MaxMetadataLen`
			assert_noop!(
				Pools::set_metadata(Origin::signed(900), PRIMARY_ACCOUNT, vec![1, 1, 1]),
				Error::<Runtime>::MetadataExceedsMaxLen
			);
		});
	}
}
