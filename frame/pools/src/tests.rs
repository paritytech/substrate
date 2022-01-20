//! Generally for pool ids we use 0-9 and delegator ids 10-99.

use super::*;
use crate::mock::{Balances, ExtBuilder, Pools, Runtime, PRIMARY_ACCOUNT, REWARDS_ACCOUNT};
use frame_support::{assert_noop, assert_ok};

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(PrimaryPools::<Runtime>::count(), 1);
		assert_eq!(RewardPools::<Runtime>::count(), 1);
		assert_eq!(SubPools::<Runtime>::count(), 0);
		assert_eq!(Delegators::<Runtime>::count(), 1);

		assert_eq!(
			PrimaryPools::<Runtime>::get(0).unwrap(),
			PrimaryPool::<Runtime> { points: 10, account_id: PRIMARY_ACCOUNT }
		);
		assert_eq!(
			RewardPools::<Runtime>::get(0).unwrap(),
			RewardPool::<Runtime> {
				balance: 0,
				points: 0,
				total_earnings: 0,
				account_id: REWARDS_ACCOUNT
			}
		);
		assert_eq!(
			Delegators::<Runtime>::get(10).unwrap(),
			Delegator::<Runtime> {
				pool: 0,
				points: 10,
				reward_pool_total_earnings: 0,
				unbonding_era: None
			}
		)
	})
}

mod primary_pool {
	#[test]
	fn points_to_issue_works() {
		// zero case
	}

	#[test]
	fn balance_to_unbond_works() {
		// zero case
	}
}
mod reward_pool {
	use super::*;
	#[test]
	fn update_total_earnings_and_balance_works() {}
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
mod sub_pools_container {
	use super::*;

	#[test]
	fn maybe_merge_pools_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(<Runtime as Config>::MaxUnbonding::get(), 5);

			// Given
			let mut sp0 = SubPoolsContainer::<Runtime> {
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

mod join {}

mod claim_payout {
	use super::*;

	#[test]
	fn calculate_delegator_payout_errors_if_a_delegator_is_unbonding() {
		ExtBuilder::default().build_and_execute(|| {
			let primary_pool = PrimaryPools::<Runtime>::get(0).unwrap();
			let reward_pool = RewardPools::<Runtime>::get(0).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();
			delegator.unbonding_era = Some(0);

			assert_noop!(
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator),
				Error::<Runtime>::AlreadyUnbonding
			);
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_1() {
		let rew = |balance, points, total_earnings| RewardPool::<Runtime> {
			balance,
			points,
			total_earnings,
			account_id: REWARDS_ACCOUNT,
		};
		let del = |reward_pool_total_earnings| Delegator::<Runtime> {
			pool: 0,
			points: 10,
			reward_pool_total_earnings,
			unbonding_era: None,
		};
		ExtBuilder::default().build_and_execute(|| {
			let primary_pool = PrimaryPools::<Runtime>::get(0).unwrap();
			let reward_pool = RewardPools::<Runtime>::get(0).unwrap();
			let delegator = Delegators::<Runtime>::get(10).unwrap();

			// given no rewards have been earned
			// when
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator).unwrap();

			// then
			assert_eq!(payout, 0);
			assert_eq!(delegator, del(0));
			assert_eq!(reward_pool, rew(0, 0, 0));

			// given the pool has earned some rewards for the first time
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 2);

			// when
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator).unwrap();

			// then
			assert_eq!(payout, 2);
			assert_eq!(reward_pool, rew(0, 0, 2));
			assert_eq!(delegator, del(2));

			// given the pool has earned rewards again
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 4);

			// when
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator).unwrap();

			// then
			assert_eq!(payout, 4);
			assert_eq!(reward_pool, rew(0, 0, 6));
			assert_eq!(delegator, del(6));

			// given the pool has earned no new rewards
			Balances::make_free_balance_be(&REWARDS_ACCOUNT, 0);

			// when
			let (reward_pool, delegator, payout) =
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator).unwrap();

			// then
			assert_eq!(payout, 0);
			assert_eq!(reward_pool, rew(0, 0, 6));
			assert_eq!(delegator, del(6));
		});
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_3() {
		let rew = |balance, points, total_earnings| RewardPool::<Runtime> {
			balance,
			points,
			total_earnings,
			account_id: REWARDS_ACCOUNT,
		};
		let del = |points, reward_pool_total_earnings| Delegator::<Runtime> {
			pool: 0,
			points,
			reward_pool_total_earnings,
			unbonding_era: None,
		};

		ExtBuilder::default()
			.add_delegators(vec![(40, 40), (50, 50)])
			.build_and_execute(|| {
				let mut primary_pool = PrimaryPools::<Runtime>::get(0).unwrap();
				primary_pool.points = 100;

				let reward_pool = RewardPools::<Runtime>::get(0).unwrap();
				// Delegator with 10 points
				let del_10 = Delegators::<Runtime>::get(10).unwrap();
				// Delegator with 40 points
				let del_40 = Delegators::<Runtime>::get(40).unwrap();
				// Delegator with 50 points
				let del_50 = Delegators::<Runtime>::get(50).unwrap();

				// Given we have a total of 100 points split among the delegators
				assert_eq!(del_50.points + del_40.points + del_10.points, 100);
				// and the reward pool has earned 100 in rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 100);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 10); // (10 del virtual points / 100 pool points) * 100 pool balance
				assert_eq!(del_10, del(10, 100));
				assert_eq!(reward_pool, rew(90, 100 * 100 - 100 * 10, 100));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 10));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_40).unwrap();

				// Then
				// The exact math is (400/900) * 90, so ideally this should be 40. But given 400 /
				// 900 (del virtual points / pool points) = ~0.444, it gets rounded down.
				assert_eq!(payout, 39);
				assert_eq!(del_40, del(40, 100));
				assert_eq!(
					reward_pool,
					rew(
						51,
						9_000 - 100 * 40, // old pool points - delegator virtual points
						100
					)
				);
				// Mock the reward pool transferring the payout to del_40
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 39));

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_50).unwrap();

				// Then
				assert_eq!(payout, 51); // (50 del virtual points / 50 pool points) * 51 pool balance
				assert_eq!(del_50, del(50, 100));
				assert_eq!(reward_pool, rew(0, 0, 100));
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 51));

				// Given the reward pool has some new rewards
				Balances::make_free_balance_be(&REWARDS_ACCOUNT, 50);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 5); // (500  del virtual points / 5,000 pool points) * 50 pool balance
				assert_eq!(del_10, del(10, 150));
				assert_eq!(reward_pool, rew(45, 5_000 - 50 * 10, 150));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 5));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_40).unwrap();

				// Then
				assert_eq!(payout, 19); // (2,000 del virtual points / 4,500 pool points) * 45 pool balance
				assert_eq!(del_40, del(40, 150));
				assert_eq!(reward_pool, rew(26, 4_500 - 50 * 40, 150));
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 19));

				// Given del_50 hasn't claimed and the reward pools has just earned 50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 50));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 76);

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_50).unwrap();

				// Then
				assert_eq!(payout, 50); // (5,000 del virtual points / 7,5000 pool points) * 76 pool balance
				assert_eq!(del_50, del(50, 200));
				assert_eq!(
					reward_pool,
					rew(
						26,
						// old pool points + points from new earnings - del points.
						//
						// points from new earnings = new earnings(50) * primary_pool.points(100)
						// del points = delegator.points(50) * new_earnings_since_last_claim (100)
						(2_500 + 50 * 100) - 50 * 100,
						200,
					)
				);
				// Mock the reward pool transferring the payout to del_50
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 50));

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 5);
				assert_eq!(del_10, del(10, 200));
				assert_eq!(reward_pool, rew(21, 2_500 - 10 * 50, 200));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 5));

				// Given del_40 hasn't claimed and the reward pool has just earned 400
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 400));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 421);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 40);
				assert_eq!(del_10, del(10, 600));
				assert_eq!(
					reward_pool,
					rew(
						381,
						// old pool points + points from new earnings - del points
						//
						// points from new earnings = new earnings(400) * primary_pool.points(100)
						// del points = delegator.points(10) * new_earnings_since_last_claim(400)
						(2_000 + 400 * 100) - 10 * 400,
						600
					)
				);
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 40));

				// Given del_40 + del_50 haven't claimed and the reward pool has earned 20
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free += 20));
				assert_eq!(Balances::free_balance(&REWARDS_ACCOUNT), 401);

				// When
				let (reward_pool, del_10, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_10).unwrap();

				// Then
				assert_eq!(payout, 2); // (200 del virtual points / 39,800 pool points) * 401
				assert_eq!(del_10, del(10, 620));
				assert_eq!(reward_pool, rew(399, (38_000 + 20 * 100) - 10 * 20, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 2));

				// When
				let (reward_pool, del_40, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_40).unwrap();

				// Then
				assert_eq!(payout, 188); // (18,800 del virtual points /  39,800 pool points) * 399
				assert_eq!(del_40, del(40, 620));
				assert_eq!(reward_pool, rew(211, 39_800 - 40 * 470, 620));
				// Mock the reward pool transferring the payout to del_10
				assert_ok!(Balances::mutate_account(&REWARDS_ACCOUNT, |a| a.free -= 188));

				// When
				let (reward_pool, del_50, payout) =
					Pools::calculate_delegator_payout(&primary_pool, reward_pool, del_50).unwrap();

				// Then
				assert_eq!(payout, 211); // (21,000 / 21,000) * 211
				assert_eq!(del_50, del(50, 620));
				assert_eq!(reward_pool, rew(0, 21_000 - 50 * 420, 620));
			});
	}
}

mod unbond {}

mod withdraw_unbonded {}

mod create {}

mod pools_interface {
	#[test]
	fn slash_pool_works() {}
}
