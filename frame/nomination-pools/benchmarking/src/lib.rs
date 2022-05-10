// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Benchmarks for the nomination pools coupled with the staking and bags list pallets.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

use frame_benchmarking::{account, frame_support::traits::Currency, vec, whitelist_account, Vec};
use frame_election_provider_support::SortedListProvider;
use frame_support::{ensure, traits::Get};
use frame_system::RawOrigin as Origin;
use pallet_nomination_pools::{
	BalanceOf, BondExtra, BondedPoolInner, BondedPools, ConfigOp, MaxPoolMembers,
	MaxPoolMembersPerPool, MaxPools, Metadata, MinCreateBond, MinJoinBond, Pallet as Pools,
	PoolMembers, PoolRoles, PoolState, RewardPools, SubPoolsStorage,
};
use sp_runtime::traits::{Bounded, Zero};
use sp_staking::{EraIndex, StakingInterface};
// `frame_benchmarking::benchmarks!` macro needs this
use pallet_nomination_pools::Call;

type CurrencyOf<T> = <T as pallet_nomination_pools::Config>::Currency;

const USER_SEED: u32 = 0;
const MAX_SPANS: u32 = 100;

pub trait Config:
	pallet_nomination_pools::Config + pallet_staking::Config + pallet_bags_list::Config
{
}

pub struct Pallet<T: Config>(Pools<T>);

fn create_funded_user_with_balance<T: pallet_nomination_pools::Config>(
	string: &'static str,
	n: u32,
	balance: BalanceOf<T>,
) -> T::AccountId {
	let user = account(string, n, USER_SEED);
	T::Currency::make_free_balance_be(&user, balance);
	user
}

// Create a bonded pool account, bonding `balance` and giving the account `balance * 2` free
// balance.
fn create_pool_account<T: pallet_nomination_pools::Config>(
	n: u32,
	balance: BalanceOf<T>,
) -> (T::AccountId, T::AccountId) {
	let ed = CurrencyOf::<T>::minimum_balance();
	let pool_creator: T::AccountId =
		create_funded_user_with_balance::<T>("pool_creator", n, ed + balance * 2u32.into());

	Pools::<T>::create(
		Origin::Signed(pool_creator.clone()).into(),
		balance,
		pool_creator.clone(),
		pool_creator.clone(),
		pool_creator.clone(),
	)
	.unwrap();

	let pool_account = pallet_nomination_pools::BondedPools::<T>::iter()
		.find(|(_, bonded_pool)| bonded_pool.roles.depositor == pool_creator)
		.map(|(pool_id, _)| Pools::<T>::create_bonded_account(pool_id))
		.expect("pool_creator created a pool above");

	(pool_creator, pool_account)
}

fn vote_to_balance<T: pallet_nomination_pools::Config>(
	vote: u64,
) -> Result<BalanceOf<T>, &'static str> {
	vote.try_into().map_err(|_| "could not convert u64 to Balance")
}

#[allow(unused)]
struct ListScenario<T: pallet_nomination_pools::Config> {
	/// Stash/Controller that is expected to be moved.
	origin1: T::AccountId,
	creator1: T::AccountId,
	dest_weight: BalanceOf<T>,
	origin1_member: Option<T::AccountId>,
}

impl<T: Config> ListScenario<T> {
	/// An expensive scenario for bags-list implementation:
	///
	/// - the node to be updated (r) is the head of a bag that has at least one other node. The bag
	///   itself will need to be read and written to update its head. The node pointed to by r.next
	///   will need to be read and written as it will need to have its prev pointer updated. Note
	///   that there are two other worst case scenarios for bag removal: 1) the node is a tail and
	///   2) the node is a middle node with prev and next; all scenarios end up with the same number
	///   of storage reads and writes.
	///
	/// - the destination bag has at least one node, which will need its next pointer updated.
	pub(crate) fn new(
		origin_weight: BalanceOf<T>,
		is_increase: bool,
	) -> Result<Self, &'static str> {
		ensure!(!origin_weight.is_zero(), "origin weight must be greater than 0");

		ensure!(
			pallet_nomination_pools::MaxPools::<T>::get().unwrap_or(0) >= 3,
			"must allow at least three pools for benchmarks"
		);

		// Burn the entire issuance.
		let i = CurrencyOf::<T>::burn(CurrencyOf::<T>::total_issuance());
		sp_std::mem::forget(i);

		// Create accounts with the origin weight
		let (pool_creator1, pool_origin1) = create_pool_account::<T>(USER_SEED + 1, origin_weight);
		T::StakingInterface::nominate(
			pool_origin1.clone(),
			// NOTE: these don't really need to be validators.
			vec![account("random_validator", 0, USER_SEED)],
		)?;

		let (_, pool_origin2) = create_pool_account::<T>(USER_SEED + 2, origin_weight);
		T::StakingInterface::nominate(
			pool_origin2.clone(),
			vec![account("random_validator", 0, USER_SEED)].clone(),
		)?;

		// Find a destination weight that will trigger the worst case scenario
		let dest_weight_as_vote = <T as pallet_staking::Config>::VoterList::score_update_worst_case(
			&pool_origin1,
			is_increase,
		);

		let dest_weight: BalanceOf<T> =
			dest_weight_as_vote.try_into().map_err(|_| "could not convert u64 to Balance")?;

		// Create an account with the worst case destination weight
		let (_, pool_dest1) = create_pool_account::<T>(USER_SEED + 3, dest_weight);
		T::StakingInterface::nominate(
			pool_dest1.clone(),
			vec![account("random_validator", 0, USER_SEED)],
		)?;

		let weight_of = pallet_staking::Pallet::<T>::weight_of_fn();
		assert_eq!(vote_to_balance::<T>(weight_of(&pool_origin1)).unwrap(), origin_weight);
		assert_eq!(vote_to_balance::<T>(weight_of(&pool_origin2)).unwrap(), origin_weight);
		assert_eq!(vote_to_balance::<T>(weight_of(&pool_dest1)).unwrap(), dest_weight);

		Ok(ListScenario {
			origin1: pool_origin1,
			creator1: pool_creator1,
			dest_weight,
			origin1_member: None,
		})
	}

	fn add_joiner(mut self, amount: BalanceOf<T>) -> Self {
		let amount = MinJoinBond::<T>::get()
			.max(CurrencyOf::<T>::minimum_balance())
			// Max `amount` with minimum thresholds for account balance and joining a pool
			// to ensure 1) the user can be created and 2) can join the pool
			.max(amount);

		let joiner: T::AccountId = account("joiner", USER_SEED, 0);
		self.origin1_member = Some(joiner.clone());
		CurrencyOf::<T>::make_free_balance_be(&joiner, amount * 2u32.into());

		let original_bonded = T::StakingInterface::active_stake(&self.origin1).unwrap();

		// Unbond `amount` from the underlying pool account so when the member joins
		// we will maintain `current_bonded`.
		T::StakingInterface::unbond(self.origin1.clone(), amount)
			.expect("the pool was created in `Self::new`.");

		// Account pool points for the unbonded balance.
		BondedPools::<T>::mutate(&1, |maybe_pool| {
			maybe_pool.as_mut().map(|pool| pool.points -= amount)
		});

		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), amount, 1).unwrap();

		// Sanity check that the vote weight is still the same as the original bonded
		let weight_of = pallet_staking::Pallet::<T>::weight_of_fn();
		assert_eq!(vote_to_balance::<T>(weight_of(&self.origin1)).unwrap(), original_bonded);

		// Sanity check the member was added correctly
		let member = PoolMembers::<T>::get(&joiner).unwrap();
		assert_eq!(member.points, amount);
		assert_eq!(member.pool_id, 1);

		self
	}
}

frame_benchmarking::benchmarks! {
	join {
		let origin_weight = pallet_nomination_pools::MinCreateBond::<T>::get()
			.max(CurrencyOf::<T>::minimum_balance())
			* 2u32.into();

		// setup the worst case list scenario.
		let scenario = ListScenario::<T>::new(origin_weight, true)?;
		assert_eq!(
			T::StakingInterface::active_stake(&scenario.origin1).unwrap(),
			origin_weight
		);

		let max_additional = scenario.dest_weight.clone() - origin_weight;
		let joiner_free = CurrencyOf::<T>::minimum_balance() + max_additional;

		let joiner: T::AccountId
			= create_funded_user_with_balance::<T>("joiner", 0, joiner_free);

		whitelist_account!(joiner);
	}: _(Origin::Signed(joiner.clone()), max_additional, 1)
	verify {
		assert_eq!(CurrencyOf::<T>::free_balance(&joiner), joiner_free - max_additional);
		assert_eq!(
			T::StakingInterface::active_stake(&scenario.origin1).unwrap(),
			scenario.dest_weight
		);
	}

	bond_extra_transfer {
		let origin_weight = pallet_nomination_pools::MinCreateBond::<T>::get()
			.max(CurrencyOf::<T>::minimum_balance())
			* 2u32.into();
		let scenario = ListScenario::<T>::new(origin_weight, true)?;
		let extra = scenario.dest_weight.clone() - origin_weight;

		// creator of the src pool will bond-extra, bumping itself to dest bag.

	}: bond_extra(Origin::Signed(scenario.creator1.clone()), BondExtra::FreeBalance(extra))
	verify {
		assert!(
			T::StakingInterface::active_stake(&scenario.origin1).unwrap() >=
			scenario.dest_weight
		);
	}

	bond_extra_reward {
		let origin_weight = pallet_nomination_pools::MinCreateBond::<T>::get()
			.max(CurrencyOf::<T>::minimum_balance())
			* 2u32.into();
		let scenario = ListScenario::<T>::new(origin_weight, true)?;
		let extra = (scenario.dest_weight.clone() - origin_weight).max(CurrencyOf::<T>::minimum_balance());

		// transfer exactly `extra` to the depositor of the src pool (1),
		let reward_account1 = Pools::<T>::create_reward_account(1);
		assert!(extra >= CurrencyOf::<T>::minimum_balance());
		CurrencyOf::<T>::deposit_creating(&reward_account1, extra);

	}: bond_extra(Origin::Signed(scenario.creator1.clone()), BondExtra::Rewards)
	verify {
		assert!(
			T::StakingInterface::active_stake(&scenario.origin1).unwrap() >=
			scenario.dest_weight
		);
	}

	claim_payout {
		let origin_weight = pallet_nomination_pools::MinCreateBond::<T>::get().max(CurrencyOf::<T>::minimum_balance()) * 2u32.into();
		let ed = CurrencyOf::<T>::minimum_balance();
		let (depositor, pool_account) = create_pool_account::<T>(0, origin_weight);
		let reward_account = Pools::<T>::create_reward_account(1);

		// Send funds to the reward account of the pool
		CurrencyOf::<T>::make_free_balance_be(&reward_account, ed + origin_weight);

		// Sanity check
		assert_eq!(
			CurrencyOf::<T>::free_balance(&depositor),
			origin_weight
		);

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor.clone()))
	verify {
		assert_eq!(
			CurrencyOf::<T>::free_balance(&depositor),
			origin_weight * 2u32.into()
		);
		assert_eq!(
			CurrencyOf::<T>::free_balance(&reward_account),
			ed + Zero::zero()
		);
	}

	unbond {
		// The weight the nominator will start at. The value used here is expected to be
		// significantly higher than the first position in a list (e.g. the first bag threshold).
		let origin_weight = BalanceOf::<T>::try_from(952_994_955_240_703u128)
			.map_err(|_| "balance expected to be a u128")
			.unwrap();
		let scenario = ListScenario::<T>::new(origin_weight, false)?;
		let amount = origin_weight - scenario.dest_weight.clone();

		let scenario = scenario.add_joiner(amount);
		let member_id = scenario.origin1_member.unwrap().clone();
		let all_points = PoolMembers::<T>::get(&member_id).unwrap().points;
		whitelist_account!(member_id);
	}: _(Origin::Signed(member_id.clone()), member_id.clone(), all_points)
	verify {
		let bonded_after = T::StakingInterface::active_stake(&scenario.origin1).unwrap();
		// We at least went down to the destination bag
		assert!(bonded_after <= scenario.dest_weight.clone());
		let member = PoolMembers::<T>::get(
			&member_id
		)
		.unwrap();
		assert_eq!(
			member.unbonding_eras.keys().cloned().collect::<Vec<_>>(),
			vec![0 + T::StakingInterface::bonding_duration()]
		);
		assert_eq!(
			member.unbonding_eras.values().cloned().collect::<Vec<_>>(),
			vec![all_points]
		);
	}

	pool_withdraw_unbonded {
		let s in 0 .. MAX_SPANS;

		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Add a new member
		let min_join_bond = MinJoinBond::<T>::get().max(CurrencyOf::<T>::minimum_balance());
		let joiner = create_funded_user_with_balance::<T>("joiner", 0, min_join_bond * 2u32.into());
		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), min_join_bond, 1)
			.unwrap();

		// Sanity check join worked
		assert_eq!(
			T::StakingInterface::active_stake(&pool_account).unwrap(),
			min_create_bond + min_join_bond
		);
		assert_eq!(CurrencyOf::<T>::free_balance(&joiner), min_join_bond);

		// Unbond the new member
		Pools::<T>::fully_unbond(Origin::Signed(joiner.clone()).into(), joiner.clone()).unwrap();

		// Sanity check that unbond worked
		assert_eq!(
			T::StakingInterface::active_stake(&pool_account).unwrap(),
			min_create_bond
		);
		assert_eq!(pallet_staking::Ledger::<T>::get(&pool_account).unwrap().unlocking.len(), 1);
		// Set the current era
		pallet_staking::CurrentEra::<T>::put(EraIndex::max_value());

		// Add `s` count of slashing spans to storage.
		pallet_staking::benchmarking::add_slashing_spans::<T>(&pool_account, s);
		whitelist_account!(pool_account);
	}: _(Origin::Signed(pool_account.clone()), 1, s)
	verify {
		// The joiners funds didn't change
		assert_eq!(CurrencyOf::<T>::free_balance(&joiner), min_join_bond);
		// The unlocking chunk was removed
		assert_eq!(pallet_staking::Ledger::<T>::get(pool_account).unwrap().unlocking.len(), 0);
	}

	withdraw_unbonded_update {
		let s in 0 .. MAX_SPANS;

		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Add a new member
		let min_join_bond = MinJoinBond::<T>::get().max(CurrencyOf::<T>::minimum_balance());
		let joiner = create_funded_user_with_balance::<T>("joiner", 0, min_join_bond * 2u32.into());
		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), min_join_bond, 1)
			.unwrap();

		// Sanity check join worked
		assert_eq!(
			T::StakingInterface::active_stake(&pool_account).unwrap(),
			min_create_bond + min_join_bond
		);
		assert_eq!(CurrencyOf::<T>::free_balance(&joiner), min_join_bond);

		// Unbond the new member
		pallet_staking::CurrentEra::<T>::put(0);
		Pools::<T>::fully_unbond(Origin::Signed(joiner.clone()).into(), joiner.clone()).unwrap();

		// Sanity check that unbond worked
		assert_eq!(
			T::StakingInterface::active_stake(&pool_account).unwrap(),
			min_create_bond
		);
		assert_eq!(pallet_staking::Ledger::<T>::get(&pool_account).unwrap().unlocking.len(), 1);

		// Set the current era to ensure we can withdraw unbonded funds
		pallet_staking::CurrentEra::<T>::put(EraIndex::max_value());

		pallet_staking::benchmarking::add_slashing_spans::<T>(&pool_account, s);
		whitelist_account!(joiner);
	}: withdraw_unbonded(Origin::Signed(joiner.clone()), joiner.clone(), s)
	verify {
		assert_eq!(
			CurrencyOf::<T>::free_balance(&joiner),
			min_join_bond * 2u32.into()
		);
		// The unlocking chunk was removed
		assert_eq!(pallet_staking::Ledger::<T>::get(&pool_account).unwrap().unlocking.len(), 0);
	}

	withdraw_unbonded_kill {
		let s in 0 .. MAX_SPANS;

		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());

		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// We set the pool to the destroying state so the depositor can leave
		BondedPools::<T>::try_mutate(&1, |maybe_bonded_pool| {
			maybe_bonded_pool.as_mut().ok_or(()).map(|bonded_pool| {
				bonded_pool.state = PoolState::Destroying;
			})
		})
		.unwrap();

		// Unbond the creator
		pallet_staking::CurrentEra::<T>::put(0);
		// Simulate some rewards so we can check if the rewards storage is cleaned up. We check this
		// here to ensure the complete flow for destroying a pool works - the reward pool account
		// should never exist by time the depositor withdraws so we test that it gets cleaned
		// up when unbonding.
		let reward_account = Pools::<T>::create_reward_account(1);
		assert!(frame_system::Account::<T>::contains_key(&reward_account));
		Pools::<T>::fully_unbond(Origin::Signed(depositor.clone()).into(), depositor.clone()).unwrap();

		// Sanity check that unbond worked
		assert_eq!(
			T::StakingInterface::active_stake(&pool_account).unwrap(),
			Zero::zero()
		);
		assert_eq!(
			CurrencyOf::<T>::free_balance(&pool_account),
			min_create_bond
		);
		assert_eq!(pallet_staking::Ledger::<T>::get(&pool_account).unwrap().unlocking.len(), 1);

		// Set the current era to ensure we can withdraw unbonded funds
		pallet_staking::CurrentEra::<T>::put(EraIndex::max_value());

		// Some last checks that storage items we expect to get cleaned up are present
		assert!(pallet_staking::Ledger::<T>::contains_key(&pool_account));
		assert!(BondedPools::<T>::contains_key(&1));
		assert!(SubPoolsStorage::<T>::contains_key(&1));
		assert!(RewardPools::<T>::contains_key(&1));
		assert!(PoolMembers::<T>::contains_key(&depositor));
		assert!(frame_system::Account::<T>::contains_key(&reward_account));

		whitelist_account!(depositor);
	}: withdraw_unbonded(Origin::Signed(depositor.clone()), depositor.clone(), s)
	verify {
		// Pool removal worked
		assert!(!pallet_staking::Ledger::<T>::contains_key(&pool_account));
		assert!(!BondedPools::<T>::contains_key(&1));
		assert!(!SubPoolsStorage::<T>::contains_key(&1));
		assert!(!RewardPools::<T>::contains_key(&1));
		assert!(!PoolMembers::<T>::contains_key(&depositor));
		assert!(!frame_system::Account::<T>::contains_key(&pool_account));
		assert!(!frame_system::Account::<T>::contains_key(&reward_account));

		// Funds where transferred back correctly
		assert_eq!(
			CurrencyOf::<T>::free_balance(&depositor),
			// gets bond back + rewards collecting when unbonding
			min_create_bond * 2u32.into() + CurrencyOf::<T>::minimum_balance()
		);
	}

	create {
		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let depositor: T::AccountId = account("depositor", USER_SEED, 0);

		// Give the depositor some balance to bond
		CurrencyOf::<T>::make_free_balance_be(&depositor, min_create_bond * 2u32.into());

		// Make sure no pools exist as a pre-condition for our verify checks
		assert_eq!(RewardPools::<T>::count(), 0);
		assert_eq!(BondedPools::<T>::count(), 0);

		whitelist_account!(depositor);
	}: _(
			Origin::Signed(depositor.clone()),
			min_create_bond,
			depositor.clone(),
			depositor.clone(),
			depositor.clone()
		)
	verify {
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(BondedPools::<T>::count(), 1);
		let (_, new_pool) = BondedPools::<T>::iter().next().unwrap();
		assert_eq!(
			new_pool,
			BondedPoolInner {
				points: min_create_bond,
				state: PoolState::Open,
				member_counter: 1,
				roles: PoolRoles {
					depositor: depositor.clone(),
					root: depositor.clone(),
					nominator: depositor.clone(),
					state_toggler: depositor.clone(),
				},
			}
		);
		assert_eq!(
			T::StakingInterface::active_stake(&Pools::<T>::create_bonded_account(1)),
			Some(min_create_bond)
		);
	}

	nominate {
		let n in 1 .. T::MaxNominations::get();

		// Create a pool
		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Create some accounts to nominate. For the sake of benchmarking they don't need to be
		// actual validators
		 let validators: Vec<_> = (0..n)
			.map(|i| account("stash", USER_SEED, i))
			.collect();

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor.clone()), 1, validators)
	verify {
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(BondedPools::<T>::count(), 1);
		let (_, new_pool) = BondedPools::<T>::iter().next().unwrap();
		assert_eq!(
			new_pool,
			BondedPoolInner {
				points: min_create_bond,
				state: PoolState::Open,
				member_counter: 1,
				roles: PoolRoles {
					depositor: depositor.clone(),
					root: depositor.clone(),
					nominator: depositor.clone(),
					state_toggler: depositor.clone(),
				}
			}
		);
		assert_eq!(
			T::StakingInterface::active_stake(&Pools::<T>::create_bonded_account(1)),
			Some(min_create_bond)
		);
	}

	set_state {
		// Create a pool
		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);
		BondedPools::<T>::mutate(&1, |maybe_pool| {
			// Force the pool into an invalid state
			maybe_pool.as_mut().map(|mut pool| pool.points = min_create_bond * 10u32.into());
		});

		let caller = account("caller", 0, USER_SEED);
		whitelist_account!(caller);
	}:_(Origin::Signed(caller), 1, PoolState::Destroying)
	verify {
		assert_eq!(BondedPools::<T>::get(1).unwrap().state, PoolState::Destroying);
	}

	set_metadata {
		let n in 1 .. <T as pallet_nomination_pools::Config>::MaxMetadataLen::get();

		// Create a pool
		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(CurrencyOf::<T>::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Create metadata of the max possible size
		let metadata: Vec<u8> = (0..n).map(|_| 42).collect();

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor), 1, metadata.clone())
	verify {
		assert_eq!(Metadata::<T>::get(&1), metadata);
	}

	set_configs {
	}:_(
		Origin::Root,
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(u32::MAX),
		ConfigOp::Set(u32::MAX),
		ConfigOp::Set(u32::MAX)
	) verify {
		assert_eq!(MinJoinBond::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(MinCreateBond::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(MaxPools::<T>::get(), Some(u32::MAX));
		assert_eq!(MaxPoolMembers::<T>::get(), Some(u32::MAX));
		assert_eq!(MaxPoolMembersPerPool::<T>::get(), Some(u32::MAX));
	}

	update_roles {
		let first_id = pallet_nomination_pools::LastPoolId::<T>::get() + 1;
		let (root, _) = create_pool_account::<T>(0, CurrencyOf::<T>::minimum_balance() * 2u32.into());
		let random: T::AccountId = account("but is anything really random in computers..?", 0, USER_SEED);
	}:_(
		Origin::Signed(root.clone()),
		first_id,
		Some(random.clone()),
		Some(random.clone()),
		Some(random.clone())
	) verify {
		assert_eq!(
			pallet_nomination_pools::BondedPools::<T>::get(first_id).unwrap().roles,
			pallet_nomination_pools::PoolRoles {
				depositor: root,
				nominator: random.clone(),
				state_toggler: random.clone(),
				root: random,
			},
		)
	}

	impl_benchmark_test_suite!(
		Pallet,
		crate::mock::new_test_ext(),
		crate::mock::Runtime
	);
}
