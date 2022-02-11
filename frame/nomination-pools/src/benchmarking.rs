use super::*;
use crate::Pallet as Pools;
use frame_benchmarking::account;
use frame_system::RawOrigin as Origin;
use frame_support::{assert_ok};

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

		let reward_account = RewardPools::<T>::get(
			BondedPools::<T>::iter().next().unwrap().0
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
	create {}: {}
	nominate {}: {}
}

frame_benchmarking::impl_benchmark_test_suite!(
	Pallet,
	crate::mock::ExtBuilder::default().build(),
	crate::mock::Runtime
);