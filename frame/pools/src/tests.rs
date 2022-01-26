use super::*;
use crate::mock::{
	Balance, Balances, CanBondExtra, CurrentEra, ExtBuilder, Origin, Pools, Runtime, StakingMock,
	PRIMARY_ACCOUNT, REWARDS_ACCOUNT,
};
use frame_support::{assert_noop, assert_ok};

// TODO
// - make sure any time we do a balance transfer and then some other operation
//	we either use transactional storage or have sufficient can_* functions
// - make sure that `unbond` transfers rewards prior to actually unbonding
// - implement staking impl of the delegator pools interface
// - test `do_slash`

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
		assert_eq!(BondedPoolStorage::<Runtime>::count(), 1);
		assert_eq!(RewardPoolStorage::<Runtime>::count(), 1);
		assert_eq!(SubPoolsStorage::<Runtime>::count(), 0);
		assert_eq!(DelegatorStorage::<Runtime>::count(), 1);

		assert_eq!(
			BondedPoolStorage::<Runtime>::get(0).unwrap(),
			BondedPool::<Runtime> { points: 10, account_id: PRIMARY_ACCOUNT }
		);
		assert_eq!(
			RewardPoolStorage::<Runtime>::get(0).unwrap(),
			RewardPool::<Runtime> {
				balance: 0,
				points: 0.into(),
				total_earnings: 0,
				account_id: REWARDS_ACCOUNT
			}
		);
		assert_eq!(
			DelegatorStorage::<Runtime>::get(10).unwrap(),
			Delegator::<Runtime> {
				pool: 0,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None
			}
		)
	})
}

#[test]
fn exercise_delegator_life_cycle() {
	// create pool
	// join pool
	// claim rewards
	// get more rewards
	//
}

mod points_to_issue {
	use super::*;
	#[test]
	fn points_to_issue_works() {
		ExtBuilder::default().build_and_execute(|| {
			let points_to_issue = points_to_issue::<Runtime>;
			// 1 points : 1 balance ratio
			assert_eq!(points_to_issue(100, 100, 10), 10);
			assert_eq!(points_to_issue(100, 100, 0), 0);
			// 2 points : 1 balance ratio
			assert_eq!(points_to_issue(50, 100, 10), 20);
			// 1 points: 2 balance ratio
			assert_eq!(points_to_issue(100, 50, 10), 5);
			// 100 points : 0 balance ratio
			assert_eq!(points_to_issue(0, 100, 10), 100 * 10);
			// 0 points : 100 balance ratio
			assert_eq!(points_to_issue(100, 0, 10), 10);
			// 10 points : 3 balance ratio
			assert_eq!(points_to_issue(30, 100, 10), 33);
			// 2 points : 3 balance ratio
			assert_eq!(points_to_issue(300, 200, 10), 6);
			// 4 points : 9 balance ratio
			assert_eq!(points_to_issue(900, 400, 90), 40)
		});
	}
}

mod balance_to_unbond {
	use super::*;
	#[test]
	fn balance_to_unbond_works() {
		ExtBuilder::default().build_and_execute(|| {
			let balance_to_unbond = balance_to_unbond::<Runtime>;
			// 1 balance : 1 points ratio
			assert_eq!(balance_to_unbond(100, 100, 10), 10);
			assert_eq!(balance_to_unbond(100, 100, 0), 0);
			// 1 balance : 2 points ratio
			assert_eq!(balance_to_unbond(50, 100, 10), 5);
			// 2 balance : 1 points ratio
			assert_eq!(balance_to_unbond(100, 50, 10), 20);
			// 100 balance : 0 points ratio
			assert_eq!(balance_to_unbond(100, 0, 10), 0);
			// 0 balance : 100 points ratio
			assert_eq!(balance_to_unbond(0, 100, 10), 0);
			// 10 balance : 3 points ratio
			assert_eq!(balance_to_unbond(100, 30, 10), 33);
			// 2 balance : 3 points ratio
			assert_eq!(balance_to_unbond(200, 300, 10), 6);
			// 4 balance : 9 points ratio
			assert_eq!(balance_to_unbond(400, 900, 90), 40)
		});
	}
}

mod bonded_pool {
	use super::*;
	#[test]
	fn points_to_issue_works() {}

	#[test]
	fn balance_to_unbond_works() {
		// zero case
	}

	#[test]
	fn ok_to_join_with_works() {
		ExtBuilder::default().build_and_execute(|| {
			let pool = BondedPool::<Runtime> { points: 100, account_id: 123 };

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
	// use super::*;

	// #[test]
	// fn update_total_earnings_and_balance_works() {
	// 	ExtBuilder::default().build_and_execute(|| {
	// 		let pool = RewardPool {
	// 			account_id: 123,
	// 			balance: 0,
	// 			total_earnings: 0,
	// 			points: 0
	// 		};

	// 		Balances::make_free_balance_be(100);
	// 		let pool = pool.update_total_earnings_and_balance();
	// 		assert_eq!(
	// 			pool.total_earnings, 100
	// 		);
	// 		assert_eq!(
	// 			pool.balance, 100
	// 		);

	// 		let pool = pool.update_total_earnings_and_balance();
	// 	});
	// }
}

mod unbond_pool {
	#[test]
	fn points_to_issue_works() {
		// zero case
	}

	#[test]
	fn balance_to_unbond_works() {
		// zero case
	}
}
mod sub_pools {
	use super::*;

	#[test]
	fn maybe_merge_pools_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(<Runtime as Config>::MaxUnbonding::get(), 5);

			// Given
			let mut sp0 = SubPools::<Runtime> {
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
			let sp1 = sp0.clone().maybe_merge_pools(3);

			// Then it exits early without modifications
			assert_eq!(sp1, sp0);

			// When `current_era == MaxUnbonding`,
			let mut sp1 = sp1.maybe_merge_pools(4);

			// Then it exits early without modifications
			assert_eq!(sp1, sp0);

			// Given we have entries for era 0..=5
			sp1.with_era.insert(5, UnbondPool::<Runtime>::new(50, 50));
			sp0.with_era.insert(5, UnbondPool::<Runtime>::new(50, 50));

			// When  `current_era - MaxUnbonding == 0`,
			let sp1 = sp1.maybe_merge_pools(5);

			// Then era 0 is merged into the `no_era` pool
			sp0.no_era = sp0.with_era.remove(&0).unwrap();
			assert_eq!(sp1, sp0);

			// When `current_era - MaxUnbonding == 1`
			let sp2 = sp1.maybe_merge_pools(6);
			let era_1_pool = sp0.with_era.remove(&1).unwrap();

			// Then era 1 is merged into the `no_era` pool
			sp0.no_era.points += era_1_pool.points;
			sp0.no_era.balance += era_1_pool.balance;
			assert_eq!(sp2, sp0);

			// When `current_era - MaxUnbonding == 5`, so all pools with era <= 4 are removed
			let sp3 = sp2.maybe_merge_pools(10);

			// Then all eras <= 5 are merged into the `no_era` pool
			for era in 2..=5 {
				let to_merge = sp0.with_era.remove(&era).unwrap();
				sp0.no_era.points += to_merge.points;
				sp0.no_era.balance += to_merge.balance;
			}
			assert_eq!(sp3, sp0);
		});
	}
}

mod join {
	use super::*;

	#[test]
	fn join_works() {
		ExtBuilder::default().build_and_execute(|| {
			Balances::make_free_balance_be(&11, 5 + 2);

			assert!(!DelegatorStorage::<Runtime>::contains_key(&11));

			assert_ok!(Pools::join(Origin::signed(11), 2, 0));

			// Storage is updated correctly
			assert_eq!(
				DelegatorStorage::<Runtime>::get(&11).unwrap(),
				Delegator::<Runtime> {
					pool: 0,
					points: 2,
					reward_pool_total_earnings: 0,
					unbonding_era: None
				}
			);
			assert_eq!(
				BondedPoolStorage::<Runtime>::get(&0).unwrap(),
				BondedPool::<Runtime> { points: 12, account_id: PRIMARY_ACCOUNT }
			);
		});
	}

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
			assert_noop!(Pools::join(Origin::signed(11), 420, 0), Error::<Runtime>::OverflowRisk);

			BondedPoolStorage::<Runtime>::insert(
				1,
				BondedPool::<Runtime> { points: 100, account_id: 123 },
			);
			// Force the points:balance ratio to 100/10 (so 10)
			StakingMock::set_bonded_balance(123, 10);
			assert_noop!(Pools::join(Origin::signed(11), 420, 1), Error::<Runtime>::OverflowRisk);

			// Force the points:balance ratio to be a valid 100/100
			StakingMock::set_bonded_balance(123, 100);
			// Cumulative balance is > 1/10 of Balance::MAX
			assert_noop!(
				Pools::join(Origin::signed(11), Balance::MAX / 10 - 100, 1),
				Error::<Runtime>::OverflowRisk
			);

			CanBondExtra::set(false);
			assert_noop!(Pools::join(Origin::signed(11), 420, 1), Error::<Runtime>::StakingError);
			CanBondExtra::set(true);

			assert_noop!(
				Pools::join(Origin::signed(11), 420, 1),
				Error::<Runtime>::RewardPoolNotFound
			);
			RewardPoolStorage::<Runtime>::insert(
				1,
				RewardPool::<Runtime> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account_id: 321,
				},
			);

			// Skipping Currency::transfer & StakingInterface::bond_extra errors
		});
	}
}

mod claim_payout {
	use super::*;

	fn del(points: Balance, reward_pool_total_earnings: Balance) -> Delegator<Runtime> {
		Delegator { pool: 0, points, reward_pool_total_earnings, unbonding_era: None }
	}

	fn rew(balance: Balance, points: u32, total_earnings: Balance) -> RewardPool<Runtime> {
		RewardPool { balance, points: points.into(), total_earnings, account_id: REWARDS_ACCOUNT }
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
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 90);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPoolStorage::<Runtime>::get(0).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(10)));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(45, 5_000 - 50 * 10, 150)
				);
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 45);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 398);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(40)));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 210);

				// When
				assert_ok!(Pools::claim_payout(Origin::signed(50)));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);
			});
	}

	#[test]
	fn calculate_delegator_payout_errors_if_a_delegator_is_unbonding() {
		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPoolStorage::<Runtime>::get(0).unwrap();
			let reward_pool = RewardPoolStorage::<Runtime>::get(0).unwrap();
			let mut delegator = DelegatorStorage::<Runtime>::get(10).unwrap();
			delegator.unbonding_era = Some(0);

			assert_noop!(
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator),
				Error::<Runtime>::AlreadyUnbonding
			);
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_1() {
		let del = |reward_pool_total_earnings| Delegator::<Runtime> {
			pool: 0,
			points: 10,
			reward_pool_total_earnings,
			unbonding_era: None,
		};
		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPoolStorage::<Runtime>::get(0).unwrap();
			let reward_pool = RewardPoolStorage::<Runtime>::get(0).unwrap();
			let delegator = DelegatorStorage::<Runtime>::get(10).unwrap();

			// Given no rewards have been earned
			// When
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&bonded_pool, reward_pool, delegator).unwrap();

			// Then
			assert_eq!(payout, 0);
			assert_eq!(delegator, del(0));
			assert_eq!(reward_pool, rew(0, 0, 0));

			// Given the pool has earned some rewards for the first time
			Balances::make_free_balance_be(&reward_pool.account_id, 5);

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
				let bonded_pool = BondedPoolStorage::<Runtime>::get(0).unwrap();
				let reward_pool = RewardPoolStorage::<Runtime>::get(0).unwrap();
				// Delegator with 10 points
				let del_10 = DelegatorStorage::<Runtime>::get(10).unwrap();
				// Delegator with 40 points
				let del_40 = DelegatorStorage::<Runtime>::get(40).unwrap();
				// Delegator with 50 points
				let del_50 = DelegatorStorage::<Runtime>::get(50).unwrap();

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
				let bonded_pool = BondedPoolStorage::<Runtime>::get(0).unwrap();

				// Given the bonded pool has 100 points
				assert_eq!(bonded_pool.points, 100);
				// Each delegator currently has a free balance of -
				Balances::make_free_balance_be(&10, 0);
				Balances::make_free_balance_be(&40, 0);
				Balances::make_free_balance_be(&50, 0);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 100);

				// When
				assert_ok!(Pools::do_reward_payout(
					10,
					DelegatorStorage::get(10).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect a payout of 10: (10 del virtual points / 100 pool points) * 100 pool
				// balance
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 100));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(90, 100 * 100 - 100 * 10, 100)
				);
				assert_eq!(Balances::free_balance(&10), 10);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 90);

				// When
				assert_ok!(Pools::do_reward_payout(
					40,
					DelegatorStorage::get(40).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect payout 40: (400 del virtual points / 900 pool points) * 90 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 100));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(50, 9_000 - 100 * 40, 100)
				);
				assert_eq!(Balances::free_balance(&40), 40);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 50);

				// When
				assert_ok!(Pools::do_reward_payout(
					50,
					DelegatorStorage::get(50).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect payout 50: (50 del virtual points / 50 pool points) * 50 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 100));
				assert_eq!(RewardPoolStorage::<Runtime>::get(0).unwrap(), rew(0, 0, 100));
				assert_eq!(Balances::free_balance(&50), 50);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				assert_ok!(Pools::do_reward_payout(
					10,
					DelegatorStorage::get(10).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect payout 5: (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 150));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(45, 5_000 - 50 * 10, 150)
				);
				assert_eq!(Balances::free_balance(&10), 10 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 45);

				// When
				assert_ok!(Pools::do_reward_payout(
					40,
					DelegatorStorage::get(40).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect payout 20: (2,000 del virtual points / 4,500 pool points) * 45 pool
				// balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 150));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(25, 4_500 - 50 * 40, 150)
				);
				assert_eq!(Balances::free_balance(&40), 40 + 20);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 25);

				// Given del 50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 75);

				// When
				assert_ok!(Pools::do_reward_payout(
					50,
					DelegatorStorage::get(50).unwrap(),
					&bonded_pool
				));

				// Then
				// We expect a payout of 50: (5,000 del virtual points / 7,5000 pool points) * 75
				// pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 200));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_ok!(Pools::do_reward_payout(
					10,
					DelegatorStorage::get(10).unwrap(),
					&bonded_pool
				));

				// Then
				// We expect a payout of 5
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 200));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(20, 2_500 - 10 * 50, 200)
				);
				assert_eq!(Balances::free_balance(&10), 15 + 5);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 20);

				// Given del 40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 420);

				// When
				assert_ok!(Pools::do_reward_payout(
					10,
					DelegatorStorage::get(10).unwrap(),
					&bonded_pool
				));

				// Then
				// We expect a payout of 40
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 600));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
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
				assert_ok!(Pools::do_reward_payout(
					10,
					DelegatorStorage::get(10).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect a payout of 2: (200 del virtual points / 38,000 pool points) * 400 pool
				// balance
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap(), del(10, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(398, (38_000 + 20 * 100) - 10 * 20, 620)
				);
				assert_eq!(Balances::free_balance(&10), 60 + 2);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 398);

				// When
				assert_ok!(Pools::do_reward_payout(
					40,
					DelegatorStorage::get(40).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect a payout of 188: (18,800 del virtual points /  39,800 pool points) * 399
				// pool balance
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap(), del(40, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(210, 39_800 - 40 * 470, 620)
				);
				assert_eq!(Balances::free_balance(&40), 60 + 188);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 210);

				// When
				assert_ok!(Pools::do_reward_payout(
					50,
					DelegatorStorage::get(50).unwrap(),
					&bonded_pool
				));

				// Then
				// Expect payout of 210: (21,000 / 21,000) * 210
				assert_eq!(DelegatorStorage::<Runtime>::get(50).unwrap(), del(50, 620));
				assert_eq!(
					RewardPoolStorage::<Runtime>::get(0).unwrap(),
					rew(0, 21_000 - 50 * 420, 620)
				);
				assert_eq!(Balances::free_balance(&50), 100 + 210);
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 0);
			});
	}

	#[test]
	fn do_reward_payout_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			let bonded_pool = BondedPoolStorage::<Runtime>::get(0).unwrap();
			let mut delegator = DelegatorStorage::<Runtime>::get(10).unwrap();

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
			assert_ok!(Pools::unbond(Origin::signed(10)));

			assert_eq!(
				SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
				sub_pools_with_era! { 0 => UnbondPool::<Runtime> { points: 10, balance: 10 }}
			);

			assert_eq!(
				BondedPoolStorage::<Runtime>::get(0).unwrap(),
				BondedPool { account_id: PRIMARY_ACCOUNT, points: 0 }
			);

			assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), 0);
		});
	}

	#[test]
	fn unbond_pool_of_3_works() {
		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (550, 550)])
			.build_and_execute(|| {
				// Given a slash from 600 -> 100
				StakingMock::set_bonded_balance(PRIMARY_ACCOUNT, 100);

				// When
				assert_ok!(Pools::unbond(Origin::signed(40)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 6, balance: 6 }}
				);
				assert_eq!(
					BondedPoolStorage::<Runtime>::get(0).unwrap(),
					BondedPool { account_id: PRIMARY_ACCOUNT, points: 560 }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), 94);
				assert_eq!(DelegatorStorage::<Runtime>::get(40).unwrap().unbonding_era, Some(0));

				// When
				assert_ok!(Pools::unbond(Origin::signed(10)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 7, balance: 7 }}
				);
				assert_eq!(
					BondedPoolStorage::<Runtime>::get(0).unwrap(),
					BondedPool { account_id: PRIMARY_ACCOUNT, points: 550 }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), 93);
				assert_eq!(DelegatorStorage::<Runtime>::get(10).unwrap().unbonding_era, Some(0));

				// When
				assert_ok!(Pools::unbond(Origin::signed(550)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 100, balance: 100 }}
				);
				assert_eq!(
					BondedPoolStorage::<Runtime>::get(0).unwrap(),
					BondedPool { account_id: PRIMARY_ACCOUNT, points: 0 }
				);
				assert_eq!(StakingMock::bonded_balance(&PRIMARY_ACCOUNT), 0);
				assert_eq!(DelegatorStorage::<Runtime>::get(550).unwrap().unbonding_era, Some(0));
			});
	}

	#[test]
	fn unbond_merges_older_pools() {
		todo!()
	}

	#[test]
	fn unbond_pool_of_3_works_when_there_are_rewards_to_claims() {
		todo!()
	}

	#[test]
	fn unbond_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(Pools::unbond(Origin::signed(11)), Error::<Runtime>::DelegatorNotFound);

			// Add the delegator
			let delegator = Delegator { pool: 1, points: 10, ..Default::default() };
			DelegatorStorage::<Runtime>::insert(11, delegator);

			assert_noop!(Pools::unbond(Origin::signed(11)), Error::<Runtime>::PoolNotFound);

			// Add bonded pool to go along with the delegator
			let bonded_pool = BondedPool { account_id: 101, points: 10 };
			BondedPoolStorage::<Runtime>::insert(1, bonded_pool);

			assert_noop!(Pools::unbond(Origin::signed(11)), Error::<Runtime>::RewardPoolNotFound);
		});
	}
}

mod withdraw_unbonded {
	use super::*;

	#[test]
	fn withdraw_unbonded_works_against_no_era_sub_pool() {
		ExtBuilder::default().build_and_execute(|| {

			// storage is cleaned up  - delegator is removed
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
				assert_ok!(Pools::unbond(Origin::signed(10)));
				assert_ok!(Pools::unbond(Origin::signed(40)));
				assert_ok!(Pools::unbond(Origin::signed(550)));
				SubPoolsStorage::<Runtime>::insert(
					0,
					SubPools {
						no_era: Default::default(),
						with_era: sub_pools_with_era! { 0 => UnbondPool { points: 600, balance: 100 }},
					},
				);
				CurrentEra::set(StakingMock::bonding_duration());

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(40)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 560, balance: 94 }}
				);
				assert_eq!(Balances::free_balance(&40), 40 + 6);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 94);
				assert!(!DelegatorStorage::<Runtime>::contains_key(40));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(10)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 550, balance: 93 }}
				);
				assert_eq!(Balances::free_balance(&10), 10 + 1);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 93);
				assert!(!DelegatorStorage::<Runtime>::contains_key(10));

				// When
				assert_ok!(Pools::withdraw_unbonded(Origin::signed(550)));

				// Then
				assert_eq!(
					SubPoolsStorage::<Runtime>::get(0).unwrap().with_era,
					sub_pools_with_era! { 0 => UnbondPool { points: 0, balance: 0 }}
				);
				assert_eq!(Balances::free_balance(&550), 550 + 93);
				assert_eq!(Balances::free_balance(&PRIMARY_ACCOUNT), 0);
				assert!(!DelegatorStorage::<Runtime>::contains_key(550));
			});
	}

	#[test]
	fn withdraw_unbonded_errors_correctly() {
		ExtBuilder::default().build_and_execute(|| {
			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				Error::<Runtime>::DelegatorNotFound
			);

			let mut delegator = Delegator {
				pool: 1,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None,
			};
			DelegatorStorage::<Runtime>::insert(11, delegator.clone());

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				Error::<Runtime>::NotUnbonding
			);

			delegator.unbonding_era = Some(0);
			DelegatorStorage::<Runtime>::insert(11, delegator.clone());

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				Error::<Runtime>::NotUnbondedYet
			);

			CurrentEra::set(StakingMock::bonding_duration());

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				Error::<Runtime>::SubPoolsNotFound
			);

			let sub_pools = SubPools {
				no_era: Default::default(),
				with_era: sub_pools_with_era! { 0 => UnbondPool { points: 10, balance: 10  }},
			};
			SubPoolsStorage::<Runtime>::insert(1, sub_pools.clone());

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				Error::<Runtime>::PoolNotFound
			);
			BondedPoolStorage::<Runtime>::insert(1, BondedPool { points: 0, account_id: 123 });
			assert_eq!(Balances::free_balance(&123), 0);

			assert_noop!(
				Pools::withdraw_unbonded(Origin::signed(11)),
				pallet_balances::Error::<Runtime>::InsufficientBalance
			);

			// If we error the delegator does not get removed
			assert_eq!(DelegatorStorage::<Runtime>::get(&11), Some(delegator));
			// and the subpools do not get updated.
			assert_eq!(SubPoolsStorage::<Runtime>::get(1).unwrap(), sub_pools)
		});
	}
}

mod create {}

mod pools_interface {
	#[test]
	fn slash_pool_works() {}
}
