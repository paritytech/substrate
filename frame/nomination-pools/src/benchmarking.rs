use super::*;
use crate::Pallet as Pools;
use frame_benchmarking::account;
use frame_support::assert_ok;
use frame_system::RawOrigin as Origin;

const USER_SEED: u32 = 0;

frame_benchmarking::benchmarks! {
	join {}: {}
	claim_payout {
		let min_create_bond = MinCreateBond::<T>::get().max(T::StakingInterface::minimum_bond());
		let depositor = account("depositor", USER_SEED, 0);

		// Create a pool
		T::Currency::make_free_balance_be(&depositor, min_create_bond * 2u32.into());
		assert_ok!(
			Pools::<T>::create(
				Origin::Signed(depositor.clone()).into(),
				min_create_bond,
				0,
				depositor.clone(),
				depositor.clone(),
				depositor.clone()
			)
		);
		// index 0 of the tuple is the key, the pool account
		let pool_account = 	BondedPools::<T>::iter().next().unwrap().0;

		let reward_account = RewardPools::<T>::get(
			pool_account
		)
		.unwrap()
		.account;

		// Send funds to the reward account of the pool
		T::Currency::make_free_balance_be(&reward_account, min_create_bond);

		// Sanity check
		assert_eq!(
			T::Currency::free_balance(&depositor),
			min_create_bond
		);
	}:_(Origin::Signed(depositor.clone()))
	verify {
		assert_eq!(
			T::Currency::free_balance(&depositor),
			min_create_bond * 2u32.into()
		);
		assert_eq!(
			T::Currency::free_balance(&reward_account),
			Zero::zero()
		);
	}

	unbond_other {}: {}
	pool_withdraw_unbonded {}: {}
	withdraw_unbonded_other {}: {}

	create {
		let min_create_bond = MinCreateBond::<T>::get().max(T::StakingInterface::minimum_bond());
		let depositor: T::AccountId = account("depositor", USER_SEED, 0);

		// Give the depositor some balance to bond
		T::Currency::make_free_balance_be(&depositor, min_create_bond * 2u32.into());

		// Make sure no pools exist as a pre-condition for our verify checks
		assert_eq!(RewardPools::<T>::count(), 0);
		assert_eq!(BondedPools::<T>::count(), 0);
	}: _(
			Origin::Signed(depositor.clone()),
			min_create_bond,
			0,
			depositor.clone(),
			depositor.clone(),
			depositor.clone()
		)
	verify {
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(BondedPools::<T>::count(), 1);
		let (pool_account, new_pool) = BondedPools::<T>::iter().next().unwrap();
		assert_eq!(
			new_pool,
			BondedPoolStorage {
				points: min_create_bond,
				depositor: depositor.clone(),
				root: depositor.clone(),
				nominator: depositor.clone(),
				state_toggler: depositor.clone(),
				state: PoolState::Open,
			}
		);
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account),
			Some(min_create_bond)
		);
	}

	nominate {}: {}
}

frame_benchmarking::impl_benchmark_test_suite!(
	Pallet,
	crate::mock::ExtBuilder::default().build(),
	crate::mock::Runtime
);
