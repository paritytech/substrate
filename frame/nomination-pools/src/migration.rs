// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::log;
use codec::Decode;
use frame_support::{traits::{OnRuntimeUpgrade, GetStorageVersion}, weights::Weight};
use sp_runtime::traits::{Zero, Saturating};
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};
// import items from crate with care, prefer not bringing in definitions of storage items as they
// might change multiple times.
use crate::{BalanceOf, Config, Pallet, PoolId, PoolState, Event};

pub mod v1 {
	use super::*;

	#[derive(Decode)]
	pub struct PoolRolesV0<AccountId> {
		pub depositor: AccountId,
		pub root: AccountId,
		pub nominator: AccountId,
		pub state_toggler: AccountId,
	}

	#[derive(Decode)]
	pub struct PoolRolesV1<AccountId> {
		pub depositor: AccountId,
		pub root: Option<AccountId>,
		pub nominator: Option<AccountId>,
		pub state_toggler: Option<AccountId>,
	}

	impl<AccountId> PoolRolesV0<AccountId> {
		fn migrate_to_v1(self) -> PoolRolesV1<AccountId> {
			PoolRolesV1 {
				depositor: self.depositor,
				root: Some(self.root),
				nominator: Some(self.nominator),
				state_toggler: Some(self.state_toggler),
			}
		}
	}

	#[derive(Decode)]
	pub struct BondedPoolInnerV0<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: PoolRolesV0<T::AccountId>,
	}

	#[derive(Decode)]
	pub struct BondedPoolInnerV1<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: PoolRolesV1<T::AccountId>,
	}

	impl<T: Config> BondedPoolInnerV0<T> {
		fn migrate_to_v1(self) -> BondedPoolInnerV1<T> {
			// Note: `commission` field not introduced to `BondedPoolInner` until
			// migration 4.
			BondedPoolInnerV1 {
				points: self.points,
				member_counter: self.member_counter,
				state: self.state,
				roles: self.roles.migrate_to_v1(),
			}
		}
	}

	/// Trivial migration which makes the roles of each pool optional.
	///
	/// Note: The depositor is not optional since he can never change.
	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 1 && onchain == 0 {
				// this is safe to execute on any runtime that has a bounded number of pools.
				let mut translated = 0u64;
				crate::BondedPools::<T>::translate::<BondedPoolInnerV0<T>, _>(|_key, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v1())
				});

				current.put::<Pallet<T>>();

				log!(info, "Upgraded {} pools, storage to version {:?}", translated, current);

				T::DbWeight::get().reads_writes(translated + 1, translated + 1)
			} else {
				log!(info, "Migration did not executed. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), &'static str> {
			// new version must be set.
			assert_eq!(Pallet::<T>::on_chain_storage_version(), 1);
			Pallet::<T>::try_state(frame_system::Pallet::<T>::block_number())?;
			Ok(())
		}
	}
}

pub mod v2 {
	use super::*;
	use frame_support::{BoundedBTreeMap, traits::{StorageVersion, ExistenceRequirement}};
	use sp_core::U256;
	use sp_runtime::Perbill;
	use sp_staking::EraIndex;

	#[derive(Decode)]
	pub struct RewardPoolV0<B> {
		pub balance: B,
		pub total_earnings: B,
		pub points: U256,
	}

	#[derive(Decode)]
	pub struct RewardPoolV1<T: Config> {
		last_recorded_reward_counter: T::RewardCounter,
		last_recorded_total_payouts: BalanceOf<T>,
		total_rewards_claimed: BalanceOf<T>,
	}

	#[derive(Decode)]
	pub struct PoolMembersV0<T: Config> {
		pub pool_id: PoolId,
		pub points: BalanceOf<T>,
		pub reward_pool_total_earnings: BalanceOf<T>,
		pub unbonding_eras: BoundedBTreeMap<EraIndex, BalanceOf<T>, T::MaxUnbonding>,
	}

	#[derive(Decode)]
	pub struct PoolMembersV1<T: Config> {
		pub pool_id: PoolId,
		pub points: BalanceOf<T>,
		pub last_recorded_reward_counter: T::RewardCounter,
		pub unbonding_eras: BoundedBTreeMap<EraIndex, BalanceOf<T>, T::MaxUnbonding>,
	}

	/// Migrate the pool reward scheme to the new version, as per
	/// <https://github.com/paritytech/substrate/pull/11669.>.
	pub struct MigrateToV2<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> MigrateToV2<T> {
		fn run(current: StorageVersion) -> Weight {
			let mut reward_pools_translated = 0u64;
			let mut members_translated = 0u64;
			// just for logging.
			let mut total_value_locked = BalanceOf::<T>::zero();
			let mut total_points_locked = BalanceOf::<T>::zero();

			// store each member of the pool, with their active points. In the process, migrate
			// their data as well.
			let mut temp_members = BTreeMap::<PoolId, Vec<(T::AccountId, BalanceOf<T>)>>::new();
			crate::PoolMembers::<T>::translate::<PoolMembersV0<T>, _>(|key, old_member| {
				let id = old_member.pool_id;
				temp_members.entry(id).or_default().push((key, old_member.points));

				total_points_locked += old_member.points;
				members_translated += 1;
				Some(PoolMembersV1::<T> {
					last_recorded_reward_counter: Zero::zero(),
					pool_id: old_member.pool_id,
					points: old_member.points,
					unbonding_eras: old_member.unbonding_eras,
				})
			});

			// translate all reward pools. In the process, do the last payout as well.
			crate::RewardPools::<T>::translate::<RewardPoolV0<BalanceOf<T>>, _>(
				|id, _old_reward_pool| {
					// each pool should have at least one member.
					let members = match temp_members.get(&id) {
						Some(x) => x,
						None => {
							log!(error, "pool {} has no member! deleting it..", id);
							return None
						},
					};
					let bonded_pool = match crate::BondedPools::<T>::get(id) {
						Some(x) => x,
						None => {
							log!(error, "pool {} has no bonded pool! deleting it..", id);
							return None
						},
					};

					let accumulated_reward = crate::RewardPool::<T>::current_balance(id);
					let reward_account = Pallet::<T>::create_reward_account(id);
					let mut sum_paid_out = BalanceOf::<T>::zero();

					members
						.into_iter()
						.filter_map(|(who, points)| {
							let bonded_pool = match crate::BondedPool::<T>::get(id) {
								Some(x) => x,
								None => {
									log!(error, "pool {} for member {:?} does not exist!", id, who);
									return None
								},
							};

							total_value_locked += bonded_pool.points_to_balance(*points);
							let portion = Perbill::from_rational(*points, bonded_pool.points);
							let last_claim = portion * accumulated_reward;

							log!(
								debug,
								"{:?} has {:?} ({:?}) of pool {} with total reward of {:?}",
								who,
								portion,
								last_claim,
								id,
								accumulated_reward
							);

							if last_claim.is_zero() {
								None
							} else {
								Some((who, last_claim))
							}
						})
						.for_each(|(who, last_claim)| {
							let outcome = T::Currency::transfer(
								&reward_account,
								&who,
								last_claim,
								ExistenceRequirement::KeepAlive,
							);

							if let Err(reason) = outcome {
								log!(warn, "last reward claim failed due to {:?}", reason,);
							} else {
								sum_paid_out = sum_paid_out.saturating_add(last_claim);
							}

							Pallet::<T>::deposit_event(Event::<T>::PaidOut {
								member: who.clone(),
								pool_id: id,
								payout: last_claim,
								commission: Zero::zero(),
							});
						});

					// this can only be because of rounding down, or because the person we
					// wanted to pay their reward to could not accept it (dust).
					let leftover = accumulated_reward.saturating_sub(sum_paid_out);
					if !leftover.is_zero() {
						// pay it all to depositor.
						let o = T::Currency::transfer(
							&reward_account,
							&bonded_pool.roles.depositor,
							leftover,
							ExistenceRequirement::KeepAlive,
						);
						log!(warn, "paying {:?} leftover to the depositor: {:?}", leftover, o);
					}

					// finally, migrate the reward pool.
					reward_pools_translated += 1;

					Some(RewardPoolV1 {
						last_recorded_reward_counter: Zero::zero(),
						last_recorded_total_payouts: Zero::zero(),
						total_rewards_claimed: Zero::zero(),
					})
				},
			);

			log!(
				info,
				"Upgraded {} members, {} reward pools, TVL {:?} TPL {:?}, storage to version {:?}",
				members_translated,
				reward_pools_translated,
				total_value_locked,
				total_points_locked,
				current
			);
			current.put::<Pallet<T>>();

			T::DbWeight::get().reads_writes(members_translated + 1, reward_pools_translated + 1)
		}
	}

	impl<T: Config> OnRuntimeUpgrade for MigrateToV2<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 2 && onchain == 1 {
				Self::run(current)
			} else {
				log!(info, "MigrateToV2 did not executed. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			// all reward accounts must have more than ED.
			RewardPools::<T>::iter().for_each(|(id, _)| {
				assert!(
					T::Currency::free_balance(&Pallet::<T>::create_reward_account(id)) >=
						T::Currency::minimum_balance()
				)
			});

			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), &'static str> {
			// new version must be set.
			assert_eq!(Pallet::<T>::on_chain_storage_version(), 2);

			// no reward or bonded pool has been skipped.
			assert_eq!(RewardPools::<T>::iter().count() as u32, RewardPools::<T>::count());
			assert_eq!(BondedPools::<T>::iter().count() as u32, BondedPools::<T>::count());

			// all reward pools must have exactly ED in them. This means no reward can be claimed,
			// and that setting reward counters all over the board to zero will work henceforth.
			RewardPools::<T>::iter().for_each(|(id, _)| {
				assert_eq!(
					RewardPool::<T>::current_balance(id),
					Zero::zero(),
					"reward pool({}) balance is {:?}",
					id,
					RewardPool::<T>::current_balance(id)
				);
			});

			log!(info, "post upgrade hook for MigrateToV2 executed.");
			Ok(())
		}
	}
}

pub mod v3 {
	use super::*;
	use crate::{Metadata, BondedPools};

	/// This migration removes stale bonded-pool metadata, if any.
	pub struct MigrateToV3<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV3<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current > onchain {
				let mut metadata_iterated = 0u64;
				let mut metadata_removed = 0u64;
				Metadata::<T>::iter_keys()
					.filter(|id| {
						metadata_iterated += 1;
						!BondedPools::<T>::contains_key(&id)
					})
					.collect::<Vec<_>>()
					.into_iter()
					.for_each(|id| {
						metadata_removed += 1;
						Metadata::<T>::remove(&id);
					});
				current.put::<Pallet<T>>();
				// metadata iterated + bonded pools read + a storage version read
				let total_reads = metadata_iterated * 2 + 1;
				// metadata removed + a storage version write
				let total_writes = metadata_removed + 1;
				T::DbWeight::get().reads_writes(total_reads, total_writes)
			} else {
				log!(info, "MigrateToV3 should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			ensure!(
				Pallet::<T>::current_storage_version() > Pallet::<T>::on_chain_storage_version(),
				"the on_chain version is equal or more than the current one"
			);
			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), &'static str> {
			ensure!(
				Metadata::<T>::iter_keys().all(|id| BondedPools::<T>::contains_key(&id)),
				"not all of the stale metadata has been removed"
			);
			ensure!(Pallet::<T>::on_chain_storage_version() == 3, "wrong storage version");
			Ok(())
		}
	}
}

pub mod v4 {
	use sp_runtime::Perbill;

use super::*;
	use crate::{PoolRoles, Commission, GlobalMaxCommission};

	#[derive(Decode)]
	pub struct OldBondedPoolInner<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: PoolRoles<T::AccountId>,
	}

	#[derive(Decode)]
	pub struct NewBondedPoolInner<T: Config> {
		pub commission: Commission<T>,
		pub member_counter: u32,
		pub points: BalanceOf<T>,
		pub roles: PoolRoles<T::AccountId>,
		pub state: PoolState,
	}

	impl<T: Config> OldBondedPoolInner<T> {
		fn migrate_to_v4(self) -> NewBondedPoolInner<T> {
			NewBondedPoolInner {
				commission: Commission::default(),
				member_counter: self.member_counter,
				points: self.points,
				state: self.state,
				roles: self.roles,
			}
		}
	}

	/// This migration adds a `commission` field to every `BondedPoolInner`, if
	/// any.
	pub struct MigrateToV4<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV4<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 4 && onchain == 3 {
				GlobalMaxCommission::<T>::set(Some(Perbill::zero()));
				log!(info, "Set initial global max commission to 0%");

				let mut translated = 0u64;
				crate::BondedPools::<T>::translate::<OldBondedPoolInner<T>, _>(|_key, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v4())
				});

				current.put::<Pallet<T>>();
				log!(info, "Upgraded {} pools, storage to version {:?}", translated, current);
				T::DbWeight::get().reads_writes(translated + 1, translated + 1)
			} else {
				log!(info, "Migration did not executed. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			ensure!(
				Pallet::<T>::current_storage_version() > Pallet::<T>::on_chain_storage_version(),
				"the on_chain version is equal or more than the current one"
			);
			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), &'static str> {
			ensure!(
				BondedPools::<T>::iter().all(|(_, inner)| inner.commission.current.is_none() &&
					inner.commission.max.is_none() &&
					inner.commission.throttle.is_none()),
				"a commission value has been incorrectly set"
			);
			ensure!(Pallet::<T>::on_chain_storage_version() == 4, "wrong storage version");
			Ok(())
		}
	}
}
