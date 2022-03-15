use super::*;

/// Sanity check all invariants
pub(crate) fn checks<T: Config>() {
	assert_eq!(RewardPools::<T>::count(), BondedPools::<T>::count());
	assert!(SubPoolsStorage::<T>::count() <= BondedPools::<T>::count());
	assert!(Delegators::<T>::count() >= BondedPools::<T>::count());
	bonding_pools_checks::<T>();
	metadata_checks::<T>()
}

pub fn pre_pool_destruction_checks<T: Config>(bonded_account: T::AccountId, reward_account: T::AccountId) {
	debug_assert_eq!(
		T::Currency::free_balance(&reward_account),
		Zero::zero()
	);
	debug_assert_eq!(
		T::Currency::free_balance(&bonded_account),
		Zero::zero()
	);
	debug_assert_eq!(
		T::StakingInterface::locked_balance(&bonded_account)
			.unwrap_or_default(),
		Zero::zero()
	);
}

fn bonding_pools_checks<T: Config>() {
	let mut delegators_seen = 0;
	for (_account, pool) in BondedPools::<T>::iter() {
		assert!(pool.delegator_counter >= 1);
		assert!(pool.delegator_counter <= MaxDelegatorsPerPool::<T>::get().unwrap());
		delegators_seen += pool.delegator_counter;
	}
	assert_eq!(delegators_seen, Delegators::<T>::count());
}

fn metadata_checks<T: Config>() {
	for (pool_id, _) in Metadata::<T>::iter() {
		assert!(BondedPools::<T>::contains_key(pool_id));
		assert!(RewardPools::<T>::contains_key(pool_id));
	}
}
