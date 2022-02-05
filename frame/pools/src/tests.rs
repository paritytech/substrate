use super::*;
use crate::mock::{
	Balance, Balances, BondingDuration, CurrentEra, DisableWithdrawUnbonded, ExistentialDeposit,
	ExtBuilder, Origin, Pools, Runtime, StakingMock, PRIMARY_ACCOUNT, REWARDS_ACCOUNT,
	UNBONDING_BALANCE_MAP,
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
		assert_eq!(BondedPoolPoints::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(Delegators::<Runtime>::count(), 1);

		assert_eq!(
			BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
			BondedPool::<Runtime> { points: 10, account: PRIMARY_ACCOUNT }
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
	todo!()
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
		let mut bonded_pool = BondedPool::<Runtime> { points: 100, account: 123 };

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
		let mut bonded_pool = BondedPool::<Runtime> { points: 100, account: 123 };
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
			let pool = BondedPool::<Runtime> { points: 100, account: 123 };

			// Simulate a 100% slashed pool
			StakingMock::set_bonded_balance(123, 0);
			assert_noop!(pool.ok_to_join_with(100), Error::<Runtime>::OverflowRisk);

			// Simulate a 89%
			StakingMock::set_bonded_balance(123, 11);
			assert_ok!(pool.ok_to_join_with(100));

			// Simulate a 90% slashed pool
			StakingMock::set_bonded_balance(123, 10);
			assert_noop!(pool.ok_to_join_with(100), Error::<Runtime>::OverflowRisk);

			let bonded = 100;
			StakingMock::set_bonded_balance(123, bonded);
			// New bonded balance would be over 1/10th of Balance type
			assert_noop!(
				pool.ok_to_join_with(Balance::MAX / 10 - bonded),
				Error::<Runtime>::OverflowRisk
			);
			// and a sanity check
			assert_ok!(pool.ok_to_join_with(Balance::MAX / 100 - bonded + 1),);
		});
	}
}

mod reward_pool {
	use super::*;

	#[test]
	fn update_total_earnings_and_balance_works() {
		// let reward_pool = RewardPool::<Runtime>
		todo!()
	}
}

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
			assert_eq!(MaxUnbonding::<Runtime>::get(), 5);

			// Given
			let mut sub_pool_0 = SubPools::<Runtime> {
				no_era: UnbondPool::<Runtime>::default(),
				with_era: std::collections::BTreeMap::from([
					(0, UnbondPool::<Runtime>::new(10, 10)),
					(1, UnbondPool::<Runtime>::new(10, 10)),
					(2, UnbondPool::<Runtime>::new(20, 20)),
					(3, UnbondPool::<Runtime>::new(30, 30)),
					(4, UnbondPool::<Runtime>::new(40, 40)),
				])
				.try_into()
				.unwrap(),
			};

			// When `current_era < MaxUnbonding`,
			let sub_pool_1 = sub_pool_0.clone().maybe_merge_pools(3);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When `current_era == MaxUnbonding`,
			let sub_pool_1 = sub_pool_1.maybe_merge_pools(4);

			// Then it exits early without modifications
			assert_eq!(sub_pool_1, sub_pool_0);

			// When  `current_era - MaxUnbonding == 0`,
			let mut sub_pool_1 = sub_pool_1.maybe_merge_pools(5);

			// Then era 0 is merged into the `no_era` pool
			sub_pool_0.no_era = sub_pool_0.with_era.remove(&0).unwrap();
			assert_eq!(sub_pool_1, sub_pool_0);

			// Given we have entries for era 1..=5
			sub_pool_1.with_era.try_insert(5, UnbondPool::<Runtime>::new(50, 50)).unwrap();
			sub_pool_0.with_era.try_insert(5, UnbondPool::<Runtime>::new(50, 50)).unwrap();

			// When `current_era - MaxUnbonding == 1`
			let sub_pool_2 = sub_pool_1.maybe_merge_pools(6);
			let era_1_pool = sub_pool_0.with_era.remove(&1).unwrap();

			// Then era 1 is merged into the `no_era` pool
			sub_pool_0.no_era.points += era_1_pool.points;
			sub_pool_0.no_era.balance += era_1_pool.balance;
			assert_eq!(sub_pool_2, sub_pool_0);

			// When `current_era - MaxUnbonding == 5`, so all pools with era <= 4 are removed
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
		let bonded = |points| BondedPool::<Runtime> { points, account: PRIMARY_ACCOUNT };
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
			assert_eq!(BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), bonded(12));

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
			assert_eq!(BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(), bonded(12 + 24));
		});
	}

	// TODO: test transactional storage aspect
	#[test]
	fn join_errors_correctly() {
		use super::*;
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::join(Origin::signed(10), 420, 420),
				Error::<Runtime>::AccountBelongsToOtherPool
			);

			assert_noop!(Pools::join(Origin::signed(11), 420, 420), Error::<Runtime>::PoolNotFound);

			// Force the pools bonded balance to 0, simulating a 100% slash
			StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 0);
			assert_noop!(
				Pools::join(Origin::signed(11), 420, PRIMARY_ACCOUNT),
				Error::<Runtime>::OverflowRisk
			);

			BondedPool::<Runtime>::insert(BondedPool::<Runtime> { points: 100, account: 123 });
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

			assert_noop!(
				Pools::join(Origin::signed(11), 420, 123),
				Error::<Runtime>::RewardPoolNotFound
			);
			RewardPools::<Runtime>::insert(
				1,
				RewardPool::<Runtime> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account: 321,
				},
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
			delegator.unbonding_era = Some(0);

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
	fn unbond_pool_of_1_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(Pools::unbond(Origin::signed(10), 0));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
				sub_pools_with_era! { 0 => UnbondPool::<Runtime> { points: 10, balance: 10 }}
			);

			assert_eq!(
				BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				BondedPool { points: 0, account: PRIMARY_ACCOUNT }
			);

			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 0);
		});
	}

	#[test]
	fn unbond_pool_of_3_works() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given a slash from 600 -> 100
				StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 100);
				// and unclaimed rewards of 600.
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 600);

				// When
				assert_ok!(Pools::unbond(Origin::signed(40), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 6, balance: 6 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool { points: 560, account: PRIMARY_ACCOUNT }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 94);
				assert_eq!(Delegators::<Runtime>::get(40).unwrap().unbonding_era, Some(0));
				assert_eq!(Balances::free_balance(&40), 40 + 40); // We claim rewards when unbonding

				// When
				assert_ok!(Pools::unbond(Origin::signed(10), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 7, balance: 7 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool { points: 550, account: PRIMARY_ACCOUNT }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 93);
				assert_eq!(Delegators::<Runtime>::get(10).unwrap().unbonding_era, Some(0));
				assert_eq!(Balances::free_balance(&10), 10 + 10);

				// When
				assert_ok!(Pools::unbond(Origin::signed(550), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 100, balance: 100 }}
				);
				assert_eq!(
					BondedPool::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
					BondedPool { points: 0, account: PRIMARY_ACCOUNT }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT).unwrap(), 0);
				assert_eq!(Delegators::<Runtime>::get(550).unwrap().unbonding_era, Some(0));
				assert_eq!(Balances::free_balance(&550), 550 + 550);
			});
	}

	#[test]
	fn unbond_merges_older_pools() {
		ExtBuilder::default().build_and_execute(|| {
			// Given
			SubPoolsStorage::<Runtime>::insert(
				PRIMARY_ACCOUNT,
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
						0 => UnbondPool { balance: 10, points: 100 },
						1 => UnbondPool { balance: 20, points: 20 },
						2 => UnbondPool { balance: 101, points: 101}
					},
				},
			);

			// When
			let current_era = 1 + MaxUnbonding::<Runtime>::get();
			CurrentEra::set(current_era);

			assert_ok!(Pools::unbond(Origin::signed(10), 0));

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap(),
				SubPools {
					no_era: UnbondPool { balance: 10 + 20, points: 100 + 20 },
					with_era: sub_pools_with_era! {
						2 => UnbondPool { balance: 101, points: 101},
						current_era => UnbondPool { balance: 10, points: 10 },
					},
				},
			)
		});
	}

	#[test]
	fn unbond_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(Pools::unbond(Origin::signed(11), 0), Error::<Runtime>::DelegatorNotFound);

			// Add the delegator
			let delegator = Delegator {
				pool: 1,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator);

			assert_noop!(Pools::unbond(Origin::signed(11), 0), Error::<Runtime>::PoolNotFound);

			// Add bonded pool to go along with the delegator
			let bonded_pool = BondedPool { points: 10, account: 1 };
			BondedPool::<Runtime>::insert(bonded_pool);

			assert_noop!(
				Pools::unbond(Origin::signed(11), 0),
				Error::<Runtime>::RewardPoolNotFound
			);
		});
	}
}

mod withdraw_unbonded {
	use super::*;

	#[test]
	fn withdraw_unbonded_works_against_slashed_no_era_sub_pool() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given

				Balances::make_free_balance_be(&PRIMARY_ACCOUNT, 0);
				assert_ok!(Pools::unbond(Origin::signed(10), 0));
				assert_ok!(Pools::unbond(Origin::signed(40), 0));

				let mut current_era = 1;
				CurrentEra::set(current_era);

				// In a new era, unbond 550
				assert_ok!(Pools::unbond(Origin::signed(550), 0));

				// Simulate a slash to the pool with_era(current_era)
				let mut sub_pools = SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap();
				let unbond_pool = sub_pools.with_era.get_mut(&current_era).unwrap();

				// Sanity check
				assert_eq!(*unbond_pool, UnbondPool { points: 550, balance: 550 });

				// Decrease the balance by half
				unbond_pool.balance = 275;
				SubPoolsStorage::<Runtime>::insert(PRIMARY_ACCOUNT, sub_pools);

				// Update the equivalent of the unbonding chunks for the `StakingMock`
				UNBONDING_BALANCE_MAP
					.with(|m| *m.borrow_mut().get_mut(&PRIMARY_ACCOUNT).unwrap() -= 275);

				// Advance the current_era to ensure all `with_era` pools will be merged into
				// `no_era` pool
				current_era += MaxUnbonding::<Runtime>::get();
				CurrentEra::set(current_era);

				// Simulate some other call to unbond that would merge `with_era` pools into
				// `no_era`
				let sub_pools = SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT)
					.unwrap()
					.maybe_merge_pools(current_era);
				assert_eq!(
					sub_pools,
					SubPools {
						with_era: Default::default(),
						no_era: UnbondPool { balance: 275 + 40 + 10, points: 550 + 40 + 10 }
					}
				);
				SubPoolsStorage::<Runtime>::insert(PRIMARY_ACCOUNT, sub_pools);

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(550), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().no_era,
					UnbondPool { points: 40 + 10, balance: 275 + 40 + 10 - 297 }
				);
				assert_eq!(Balances::free_balance(&550), 550 + 297);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 275 + 40 + 10 - 297);
				assert!(!Delegators::<Runtime>::contains_key(550));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(40), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().no_era,
					UnbondPool { points: 10, balance: 28 - 22 }
				);
				assert_eq!(Balances::free_balance(&40), 40 + 22);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 28 - 22);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().no_era,
					UnbondPool { points: 0, balance: 0 }
				);
				assert_eq!(Balances::free_balance(&10), 10 + 6);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!Delegators::<Runtime>::contains_key(10));
			});
	}

	#[test]
	fn withdraw_unbonded_works_against_slashed_with_era_sub_pools() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given
				StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 100); // slash bonded balance
				Balances::make_free_balance_be(&PRIMARY_ACCOUNT, 0);

				// Disable withdraw unbonded so unbond calls do not withdraw funds unbonded
				// immediately prior.
				DisableWithdrawUnbonded::set(true);
				assert_ok!(Pools::unbond(Origin::signed(10), 0));
				assert_ok!(Pools::unbond(Origin::signed(40), 0));
				assert_ok!(Pools::unbond(Origin::signed(550), 0));
				DisableWithdrawUnbonded::set(false);

				SubPoolsStorage::<Runtime>::insert(
					PRIMARY_ACCOUNT,
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! { 0 => UnbondPool { points: 600, balance: 100 }},
					},
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(40), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 560, balance: 94 }}
				);
				assert_eq!(Balances::free_balance(&40), 40 + 6);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 94);
				assert!(!Delegators::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 550, balance: 93 }}
				);
				assert_eq!(Balances::free_balance(&10), 10 + 1);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 93);
				assert!(!Delegators::<Runtime>::contains_key(10));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(550), 0));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(&PRIMARY_ACCOUNT).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 0, balance: 0 }}
				);
				assert_eq!(Balances::free_balance(&550), 550 + 93);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!Delegators::<Runtime>::contains_key(550));
			});
	}

	#[test]
	fn withdraw_unbonded_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 0),
				Error::<Runtime>::DelegatorNotFound
			);

			let mut delegator = Delegator {
				pool: 123,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			Delegators::<Runtime>::insert(11, delegator.clone());

			// The delegator has not called `unbond`
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 0),
				Error::<Runtime>::NotUnbonding
			);

			// Simulate calling `unbond`
			delegator.unbonding_era = Some(0);
			Delegators::<Runtime>::insert(11, delegator.clone());

			// We are still in the bonding duration
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 0),
				Error::<Runtime>::NotUnbondedYet
			);

			// Skip ahead to the end of the bonding duration
			CurrentEra::set(StakingMock::bonding_duration());

			// We encounter a system logic error;` the sub-pools would normally be created in
			// `unbond`
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11), 0),
				Error::<Runtime>::SubPoolsNotFound
			);

			// Insert the sub-pool
			let sub_pools = SubPools {
				no_era: Default::default(),
				with_era: sub_pools_with_era! { 0 => UnbondPool { points: 10, balance: 10  }},
			};
			SubPoolsStorage::<Runtime>::insert(123, sub_pools.clone());

			// If we error the delegator does not get removed
			assert_eq!(Delegators::<Runtime>::get(&11), Some(delegator));
			// and the subpools do not get updated.
			assert_eq!(SubPoolsStorage::<Runtime>::get(123).unwrap(), sub_pools)
		});
	}

	#[test]
	#[should_panic = "Defensive failure has been triggered!: Module { index: 1, error: 2, message: Some(\"InsufficientBalance\") }"]
	fn withdraw_unbonded_test_panics_if_funds_cannot_be_transferred() {
		ExtBuilder::default().build_and_execute(|| {
			// Insert a delegator that starts unbonding in era 0
			let delegator = Delegator {
				pool: 123,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: Some(0),
			};
			Delegators::<Runtime>::insert(11, delegator.clone());

			// Skip ahead to the end of the bonding duration
			CurrentEra::set(StakingMock::bonding_duration());

			// Insert the sub-pool
			let sub_pools = SubPools {
				no_era: Default::default(),
				with_era: sub_pools_with_era! { 0 => UnbondPool { points: 10, balance: 10  }},
			};
			SubPoolsStorage::<Runtime>::insert(123, sub_pools.clone());

			// Panics
			let _ = Pools::withdraw_unbonded(Origin::signed(11), 0);
		});
	}
}

mod create {
	use super::*;

	#[test]
	fn create_works() {
		ExtBuilder::default().build_and_execute(|| {
			let stash = 337692978;

			assert!(!BondedPoolPoints::<Runtime>::contains_key(1));
			assert!(!RewardPools::<Runtime>::contains_key(1));
			assert!(!Delegators::<Runtime>::contains_key(11));
			assert_eq!(StakingMock::bonded_balance(&stash), None);

			Balances::make_free_balance_be(&11, StakingMock::minimum_bond());
			assert_ok!(Pools::create(Origin::signed(11), vec![], StakingMock::minimum_bond(), 42));

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
				BondedPool { points: StakingMock::minimum_bond(), account: stash.clone() }
			);
			assert_eq!(StakingMock::bonded_balance(&stash).unwrap(), StakingMock::minimum_bond());
			assert_eq!(
				RewardPools::<Runtime>::get(stash).unwrap(),
				RewardPool {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account: 2844952004
				}
			);
		});
	}

	// TODO check transactional storage aspect
	#[test]
	fn create_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::create(Origin::signed(11), vec![], 420, 0),
				Error::<Runtime>::IdInUse
			);

			assert_noop!(
				Pools::create(Origin::signed(11), vec![], 1, 42),
				Error::<Runtime>::MinimumBondNotMet
			);
		});
	}
}

mod pools_interface {
	use super::*;

	#[test]
	fn slash_pool_works_in_simple_cases() {
		// Slash with no sub pools
		ExtBuilder::default().build_and_execute(|| {
			// When
			let SlashPoolOut { slashed_bonded, slashed_unlocking } =
				Pools::slash_pool(SlashPoolArgs {
					pool_stash: &PRIMARY_ACCOUNT,
					slash_amount: 9,
					slash_era: 0,
					apply_era: 3,
					active_bonded: 10,
				})
				.unwrap();

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
				Default::default()
			);
			assert_eq!(slashed_unlocking, Default::default());
			assert_eq!(slashed_bonded, 1);

			// Slash, some sub pools are in range, some are out
			// Same as above, but a slash amount greater than total slashable
		});

		// Slash, but all sub pools are out of range
		ExtBuilder::default().add_delegators(vec![(100, 100)]).build_and_execute(|| {
			// Given
			// Unbond in era 0
			assert_ok!(Pools::unbond(Origin::signed(10), 0));

			// When
			let SlashPoolOut { slashed_bonded, slashed_unlocking } =
				Pools::slash_pool(SlashPoolArgs {
					pool_stash: &PRIMARY_ACCOUNT,
					slash_amount: 9,
					// We start slashing unbonding pools in `slash_era + 1`
					slash_era: 0,
					apply_era: 3,
					active_bonded: 100,
				})
				.unwrap();

			// Then
			assert_eq!(
				SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
				SubPools {
					no_era: Default::default(),
					with_era: sub_pools_with_era! {
						0 => UnbondPool { points: 10, balance: 10 }
					}
				}
			);
			assert_eq!(slashed_unlocking, Default::default());
			assert_eq!(slashed_bonded, 91);
		});
	}

	// Some sub pools are in range of the slash while others are not.
	#[test]
	fn slash_pool_works_in_complex_cases() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (100, 100), (200, 200), (300, 300), (400, 400)])
			.build_and_execute(|| {
				// Make sure no pools get merged into `SubPools::no_era` until era 7.
				BondingDuration::set(5);
				assert_eq!(MaxUnbonding::<Runtime>::get(), 7);

				assert_ok!(Pools::unbond(Origin::signed(10), 0));

				CurrentEra::set(1);
				assert_ok!(Pools::unbond(Origin::signed(40), 0));

				CurrentEra::set(3);
				assert_ok!(Pools::unbond(Origin::signed(100), 0));

				CurrentEra::set(5);
				assert_ok!(Pools::unbond(Origin::signed(200), 0));

				CurrentEra::set(6);
				assert_ok!(Pools::unbond(Origin::signed(300), 0));

				// Given
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 => UnbondPool { points: 10, balance: 10 },
							1 => UnbondPool { points: 40, balance: 40 },
							3 => UnbondPool { points: 100, balance: 100 },
							5 => UnbondPool { points: 200, balance: 200 },
							6 => UnbondPool { points: 300, balance: 300 },
						}
					}
				);

				// When
				let SlashPoolOut { slashed_bonded, slashed_unlocking } =
					Pools::slash_pool(SlashPoolArgs {
						pool_stash: &PRIMARY_ACCOUNT,
						slash_amount: (40 + 100 + 200 + 400) / 2,
						slash_era: 0,
						apply_era: 5,
						active_bonded: 400,
					})
					.unwrap();

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 => UnbondPool { points: 10, balance: 10 },
							1 => UnbondPool { points: 40, balance: 40 / 2 },
							3 => UnbondPool { points: 100, balance: 100 / 2},
							5 => UnbondPool { points: 200, balance: 200 / 2},
							6 => UnbondPool { points: 300, balance: 300 },
						}
					}
				);
				let expected_slashed_unlocking: BTreeMap<_, _> =
					[(1, 40 / 2), (3, 100 / 2), (5, 200 / 2)].into_iter().collect();
				assert_eq!(slashed_unlocking, expected_slashed_unlocking);
				assert_eq!(slashed_bonded, 400 / 2);
			});
	}

	// Same as above, but the slash amount is greater than the slash-able balance of the pool.
	#[test]
	fn pool_slash_works_with_slash_amount_greater_than_slashable() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (100, 100), (200, 200), (300, 300), (400, 400)])
			.build_and_execute(|| {
				// Make sure no pools get merged into `SubPools::no_era` until era 7.
				BondingDuration::set(5);
				assert_eq!(MaxUnbonding::<Runtime>::get(), 7);

				assert_ok!(Pools::unbond(Origin::signed(10), 0));

				CurrentEra::set(1);
				assert_ok!(Pools::unbond(Origin::signed(40), 0));

				CurrentEra::set(3);
				assert_ok!(Pools::unbond(Origin::signed(100), 0));

				CurrentEra::set(5);
				assert_ok!(Pools::unbond(Origin::signed(200), 0));

				CurrentEra::set(6);
				assert_ok!(Pools::unbond(Origin::signed(300), 0));

				// Given
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 => UnbondPool { points: 10, balance: 10 },
							1 => UnbondPool { points: 40, balance: 40 },
							3 => UnbondPool { points: 100, balance: 100 },
							5 => UnbondPool { points: 200, balance: 200 },
							6 => UnbondPool { points: 300, balance: 300 },
						}
					}
				);

				// When
				let SlashPoolOut { slashed_bonded, slashed_unlocking } =
					Pools::slash_pool(SlashPoolArgs {
						pool_stash: &PRIMARY_ACCOUNT,
						slash_amount: 40 + 100 + 200 + 400 + 10,
						slash_era: 0,
						apply_era: 5,
						active_bonded: 400,
					})
					.unwrap();

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(PRIMARY_ACCOUNT).unwrap(),
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! {
							0 => UnbondPool { points: 10, balance: 10 },
							1 => UnbondPool { points: 40, balance: 0 },
							3 => UnbondPool { points: 100, balance: 0 },
							5 => UnbondPool { points: 200, balance: 0 },
							6 => UnbondPool { points: 300, balance: 300 },
						}
					}
				);
				let expected_slashed_unlocking: BTreeMap<_, _> =
					[(1, 0), (3, 0), (5, 0)].into_iter().collect();
				assert_eq!(slashed_unlocking, expected_slashed_unlocking);
				assert_eq!(slashed_bonded, 0);
			});
	}
}
