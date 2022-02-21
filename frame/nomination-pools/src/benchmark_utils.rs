//! Utilities for writing benchmarks.

use crate::{BalanceOf, BondedPools, Config, RewardPools};
use sp_staking::StakingInterface;

// TODO: [now] most of these can be achieved by making the fields on some structs public

/// Find the account ID of the pool created by `depositor`.
pub fn find_pool_account_by_depositor<T: Config>(depositor: &T::AccountId) -> Option<T::AccountId> {
	BondedPools::<T>::iter()
		.find(|(_, bonded_pool)| bonded_pool.depositor == *depositor)
		.map(|(pool_account, _)| pool_account)
}

// Force the `pool_account` to unbond `amount`.
pub fn unbond_pool<T: Config>(pool_account: T::AccountId, amount: BalanceOf<T>) -> Result<(), ()> {
	T::StakingInterface::unbond(pool_account.clone(), amount).map_err(|_| ())?;

	// Account pool points for the unbonded balance
	BondedPools::<T>::mutate(&pool_account, |maybe_pool| {
		maybe_pool.as_mut().map(|pool| pool.points -= amount)
	})
	.map(|_| ())
	.ok_or(())
}

// Get the account ID of the reward pool for the given bonded `pool_account`.
pub fn get_reward_pool_account<T: Config>(pool_account: &T::AccountId) -> Result<T::
AccountId, ()> {
	RewardPools::<T>::get(
		pool_account
	)
	.map(|r| r.account.clone())
	.ok_or(())
}
