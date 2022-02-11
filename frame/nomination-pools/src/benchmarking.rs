use super::*;
use crate::Pallet as Pools;
use frame_benchmarking::{account, whitelist_account};
use frame_support::assert_ok;
use frame_system::RawOrigin as Origin;
use crate::mock::clear_storage;

const USER_SEED: u32 = 0;

frame_benchmarking::benchmarks! {
	join {
		clear_storage::<T>();

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

		// Create the account that will join the pool
		let joiner = account("joiner", USER_SEED, 0);
		let min_join_bond = MinJoinBond::<T>::get().max(T::Currency::minimum_balance());
		// and give it some funds.
		T::Currency::make_free_balance_be(&joiner, min_join_bond * 2u32.into());

		whitelist_account!(joiner);
	}: _(Origin::Signed(joiner.clone()), min_join_bond, pool_account.clone())
	verify {
		assert_eq!(T::Currency::free_balance(&joiner), min_join_bond);
		assert_eq!(T::StakingInterface::bonded_balance(&pool_account), Some(min_join_bond + min_create_bond));
		assert_eq!(
			BondedPool::<T>::get(&pool_account).unwrap(),
			BondedPool {
				account: pool_account,
				points: min_join_bond + min_create_bond,
				depositor: depositor.clone(),
				root: depositor.clone(),
				nominator: depositor.clone(),
				state_toggler: depositor.clone(),
				state: PoolState::Open,
			}
		);
	}

	claim_payout {
		clear_storage::<T>();

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

		whitelist_account!(depositor);
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
		clear_storage::<T>();

		let min_create_bond = MinCreateBond::<T>::get().max(T::StakingInterface::minimum_bond());
		let depositor: T::AccountId = account("depositor", USER_SEED, 0);

		// Give the depositor some balance to bond
		T::Currency::make_free_balance_be(&depositor, min_create_bond * 2u32.into());

		// Make sure no pools exist as a pre-condition for our verify checks
		assert_eq!(RewardPools::<T>::count(), 0);
		assert_eq!(BondedPools::<T>::count(), 0);

		whitelist_account!(depositor);
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

	nominate {
		clear_storage::<T>();

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

		// Create some accounts to nominate. For the sake of benchmarking they don't need to be actual validators
		let validators: Vec<_> = (0..T::StakingInterface::max_nominations())
			.map(|i|
				T::Lookup::unlookup(account("stash", USER_SEED, i))
			)
			.collect();

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor.clone()), pool_account, validators)
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
}

frame_benchmarking::impl_benchmark_test_suite!(
	Pallet,
	crate::mock::ExtBuilder::default().build(),
	crate::mock::Runtime
);
