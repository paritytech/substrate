use super::*;

/// Sanity check all invariants
pub(crate) fn checks<T: Config>() {
	assert_eq!(RewardPools::<T>::count(), BondedPools::<T>::count());
	assert!(SubPoolsStorage::<T>::count() <= BondedPools::<T>::count());
	assert!(Delegators::<T>::count() >= BondedPools::<T>::count());
	bonding_pools_checks::<T>();
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
