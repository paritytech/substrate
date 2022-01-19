//! Generally for pool ids we use 0-9 and delegator ids 10-99.

use super::*;
use crate::mock::{Balances, ExtBuilder, Pools, Runtime};
use frame_support::{assert_err, assert_noop};

// Pool 0's primary account id (i.e. its stash and controller account).
const PRIMARY_ACCOUNT: u32 = 2536596763;
// Pool 0's reward destination.
const REWARDS_ACCOUNT: u32 = 736857005;

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
mod sub_pools_container {}

mod join {}

mod claim_payout {
	use super::*;

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_1() {
		ExtBuilder::default().build_and_execute(|| {
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

		// calculate_delegator_payout_errors_if_a_delegator_is_unbonding() {
		// 	let primary_pool = PrimaryPools::<Runtime>::get(0);
		// 	let reward_pool = RewardPools::<Runtime>::get(0);
		// 	let mut delegator = Delegators::<Runtime>::get(10);
		// 	delegator.unbonding_era = Some(0);

		// 	assert_noop!(
		// 		calculate_delegator_payout(&primary_pool, reward_pool, delegator),
		// 	);
	}

	#[test]
	fn calculate_delegator_payout_works_with_a_pool_of_3() {}

	#[test]
	fn calculate_delegator_payout_errors_when_unbonding_era_is_some() {
		ExtBuilder::default().build_and_execute(|| {
			let primary_pool = PrimaryPools::<Runtime>::get(0).unwrap();
			let reward_pool = RewardPools::<Runtime>::get(0).unwrap();
			let mut delegator = Delegators::<Runtime>::get(10).unwrap();

			delegator.unbonding_era = Some(0);

			assert_noop!(
				Pools::calculate_delegator_payout(&primary_pool, reward_pool, delegator),
				Error::<Runtime>::AlreadyUnbonding
			);
		})
	}
}

mod unbond {}

mod withdraw_unbonded {}

mod create {}

mod pools_interface {
	#[test]
	fn slash_pool_works() {}
}
