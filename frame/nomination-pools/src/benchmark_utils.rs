//! Utilities for writing benchmarks.

use crate::{BalanceOf, BondedPools, Config};
use sp_staking::StakingInterface;

/// Find the account ID of the pool created by `depositor`.
pub fn find_pool_account_by_depositor<T: Config>(depositor: &T::AccountId) -> Option<T::AccountId> {
	BondedPools::<T>::iter()
		.find(|(_, bonded_pool)| bonded_pool.depositor == *depositor)
		.map(|(pool_account, _)| pool_account)
}

// Force the `pool_account` to unbond `amount`.
pub fn unbond_pool<T: Config>(pool_account: T::AccountId, amount: BalanceOf<T>) -> Result<(), ()> {
	T::StakingInterface::unbond(pool_account.clone(), amount).unwrap();

	// Account pool points for the unbonded balance
	BondedPools::<T>::mutate(&pool_account, |maybe_pool| {
		maybe_pool.as_mut().map(|pool| pool.points -= amount)
	})
	.map(|_| ())
	.ok_or(())
}
