// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::*;
use crate::log;
use frame_support::traits::OnRuntimeUpgrade;
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

pub mod v1 {
	use super::*;

	#[derive(Decode)]
	pub struct OldPoolRoles<AccountId> {
		pub depositor: AccountId,
		pub root: AccountId,
		pub nominator: AccountId,
		pub bouncer: AccountId,
	}

	impl<AccountId> OldPoolRoles<AccountId> {
		fn migrate_to_v1(self) -> PoolRoles<AccountId> {
			PoolRoles {
				depositor: self.depositor,
				root: Some(self.root),
				nominator: Some(self.nominator),
				bouncer: Some(self.bouncer),
			}
		}
	}

	#[derive(Decode)]
	pub struct OldBondedPoolInner<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: OldPoolRoles<T::AccountId>,
	}

	impl<T: Config> OldBondedPoolInner<T> {
		fn migrate_to_v1(self) -> BondedPoolInner<T> {
			// Note: `commission` field not introduced to `BondedPoolInner` until
			// migration 4.
			BondedPoolInner {
				points: self.points,
				commission: Commission::default(),
				member_counter: self.member_counter,
				state: self.state,
				roles: self.roles.migrate_to_v1(),
			}
		}
	}

	/// Trivial migration which makes the roles of each pool optional.
	///
	/// Note: The depositor is not optional since they can never change.
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
				BondedPools::<T>::translate::<OldBondedPoolInner<T>, _>(|_key, old_value| {
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
		fn post_upgrade(_: Vec<u8>) -> Result<(), TryRuntimeError> {
			// new version must be set.
			ensure!(
				Pallet::<T>::on_chain_storage_version() == 1,
				"The onchain version must be updated after the migration."
			);
			Pallet::<T>::try_state(frame_system::Pallet::<T>::block_number())?;
			Ok(())
		}
	}
}

pub mod v2 {
	use super::*;
	use sp_runtime::Perbill;

	#[test]
	fn migration_assumption_is_correct() {
		// this migrations cleans all the reward accounts to contain exactly ed, and all members
		// having no claimable rewards. In this state, all fields of the `RewardPool` and
		// `member.last_recorded_reward_counter` are all zero.
		use crate::mock::*;
		ExtBuilder::default().build_and_execute(|| {
			let join = |x| {
				Balances::make_free_balance_be(&x, Balances::minimum_balance() + 10);
				frame_support::assert_ok!(Pools::join(RuntimeOrigin::signed(x), 10, 1));
			};

			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 10);
			assert_eq!(
				RewardPools::<Runtime>::get(1).unwrap(),
				RewardPool { ..Default::default() }
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);

			join(20);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 20);
			assert_eq!(
				RewardPools::<Runtime>::get(1).unwrap(),
				RewardPool { ..Default::default() }
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(20).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);

			join(30);
			assert_eq!(BondedPool::<Runtime>::get(1).unwrap().points, 30);
			assert_eq!(
				RewardPools::<Runtime>::get(1).unwrap(),
				RewardPool { ..Default::default() }
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(10).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(20).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);
			assert_eq!(
				PoolMembers::<Runtime>::get(30).unwrap().last_recorded_reward_counter,
				Zero::zero()
			);
		});
	}

	#[derive(Decode)]
	pub struct OldRewardPool<B> {
		pub balance: B,
		pub total_earnings: B,
		pub points: U256,
	}

	#[derive(Decode)]
	pub struct OldPoolMember<T: Config> {
		pub pool_id: PoolId,
		pub points: BalanceOf<T>,
		pub reward_pool_total_earnings: BalanceOf<T>,
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
			PoolMembers::<T>::translate::<OldPoolMember<T>, _>(|key, old_member| {
				let id = old_member.pool_id;
				temp_members.entry(id).or_default().push((key, old_member.points));

				total_points_locked += old_member.points;
				members_translated += 1;
				Some(PoolMember::<T> {
					last_recorded_reward_counter: Zero::zero(),
					pool_id: old_member.pool_id,
					points: old_member.points,
					unbonding_eras: old_member.unbonding_eras,
				})
			});

			// translate all reward pools. In the process, do the last payout as well.
			RewardPools::<T>::translate::<OldRewardPool<BalanceOf<T>>, _>(
				|id, _old_reward_pool| {
					// each pool should have at least one member.
					let members = match temp_members.get(&id) {
						Some(x) => x,
						None => {
							log!(error, "pool {} has no member! deleting it..", id);
							return None
						},
					};
					let bonded_pool = match BondedPools::<T>::get(id) {
						Some(x) => x,
						None => {
							log!(error, "pool {} has no bonded pool! deleting it..", id);
							return None
						},
					};

					let accumulated_reward = RewardPool::<T>::current_balance(id);
					let reward_account = Pallet::<T>::create_reward_account(id);
					let mut sum_paid_out = BalanceOf::<T>::zero();

					members
						.into_iter()
						.filter_map(|(who, points)| {
							let bonded_pool = match BondedPool::<T>::get(id) {
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

					Some(RewardPool {
						last_recorded_reward_counter: Zero::zero(),
						last_recorded_total_payouts: Zero::zero(),
						total_rewards_claimed: Zero::zero(),
						total_commission_claimed: Zero::zero(),
						total_commission_pending: Zero::zero(),
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
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			// all reward accounts must have more than ED.
			RewardPools::<T>::iter().try_for_each(|(id, _)| -> Result<(), TryRuntimeError> {
				ensure!(
					T::Currency::free_balance(&Pallet::<T>::create_reward_account(id)) >=
						T::Currency::minimum_balance(),
					"Reward accounts must have greater balance than ED."
				);
				Ok(())
			})?;

			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), TryRuntimeError> {
			// new version must be set.
			ensure!(
				Pallet::<T>::on_chain_storage_version() == 2,
				"The onchain version must be updated after the migration."
			);

			// no reward or bonded pool has been skipped.
			ensure!(
				RewardPools::<T>::iter().count() as u32 == RewardPools::<T>::count(),
				"The count of reward pools must remain the same after the migration."
			);
			ensure!(
				BondedPools::<T>::iter().count() as u32 == BondedPools::<T>::count(),
				"The count of reward pools must remain the same after the migration."
			);

			// all reward pools must have exactly ED in them. This means no reward can be claimed,
			// and that setting reward counters all over the board to zero will work henceforth.
			RewardPools::<T>::iter().try_for_each(|(id, _)| -> Result<(), TryRuntimeError> {
				ensure!(
					RewardPool::<T>::current_balance(id) == Zero::zero(),
					"Reward pool balance must be zero.",
				);
				Ok(())
			})?;

			log!(info, "post upgrade hook for MigrateToV2 executed.");
			Ok(())
		}
	}
}

pub mod v3 {
	use super::*;

	/// This migration removes stale bonded-pool metadata, if any.
	pub struct MigrateToV3<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV3<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			if onchain == 2 {
				log!(
					info,
					"Running migration with current storage version {:?} / onchain {:?}",
					current,
					onchain
				);

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
				StorageVersion::new(3).put::<Pallet<T>>();
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
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), TryRuntimeError> {
			ensure!(
				Metadata::<T>::iter_keys().all(|id| BondedPools::<T>::contains_key(&id)),
				"not all of the stale metadata has been removed"
			);
			ensure!(
				Pallet::<T>::on_chain_storage_version() >= 3,
				"nomination-pools::migration::v3: wrong storage version"
			);
			Ok(())
		}
	}
}

pub mod v4 {
	use super::*;

	#[derive(Decode)]
	pub struct OldBondedPoolInner<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: PoolRoles<T::AccountId>,
	}

	impl<T: Config> OldBondedPoolInner<T> {
		fn migrate_to_v4(self) -> BondedPoolInner<T> {
			BondedPoolInner {
				commission: Commission::default(),
				member_counter: self.member_counter,
				points: self.points,
				state: self.state,
				roles: self.roles,
			}
		}
	}

	/// Migrates from `v3` directly to `v5` to avoid the broken `v4` migration.
	#[allow(deprecated)]
	pub type MigrateV3ToV5<T, U> = (v4::MigrateToV4<T, U>, v5::MigrateToV5<T>);

	/// # Warning
	///
	/// To avoid mangled storage please use `MigrateV3ToV5` instead.
	/// See: github.com/paritytech/substrate/pull/13715
	///
	/// This migration adds a `commission` field to every `BondedPoolInner`, if
	/// any.
	#[deprecated(
		note = "To avoid mangled storage please use `MigrateV3ToV5` instead. See: github.com/paritytech/substrate/pull/13715"
	)]
	pub struct MigrateToV4<T, U>(sp_std::marker::PhantomData<(T, U)>);
	#[allow(deprecated)]
	impl<T: Config, U: Get<Perbill>> OnRuntimeUpgrade for MigrateToV4<T, U> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if onchain == 3 {
				log!(warn, "Please run MigrateToV5 immediately after this migration. See github.com/paritytech/substrate/pull/13715");
				let initial_global_max_commission = U::get();
				GlobalMaxCommission::<T>::set(Some(initial_global_max_commission));
				log!(
					info,
					"Set initial global max commission to {:?}.",
					initial_global_max_commission
				);

				let mut translated = 0u64;
				BondedPools::<T>::translate::<OldBondedPoolInner<T>, _>(|_key, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v4())
				});

				StorageVersion::new(4).put::<Pallet<T>>();
				log!(info, "Upgraded {} pools, storage to version {:?}", translated, current);

				// reads: translated + onchain version.
				// writes: translated + current.put + initial global commission.
				T::DbWeight::get().reads_writes(translated + 1, translated + 2)
			} else {
				log!(info, "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), TryRuntimeError> {
			// ensure all BondedPools items now contain an `inner.commission: Commission` field.
			ensure!(
				BondedPools::<T>::iter().all(|(_, inner)|
					// Check current
					(inner.commission.current.is_none() ||
					inner.commission.current.is_some()) &&
					// Check max
					(inner.commission.max.is_none() || inner.commission.max.is_some()) &&
					// Check change_rate
					(inner.commission.change_rate.is_none() ||
					inner.commission.change_rate.is_some()) &&
					// Check throttle_from
					(inner.commission.throttle_from.is_none() ||
					inner.commission.throttle_from.is_some())),
				"a commission value has not been set correctly"
			);
			ensure!(
				GlobalMaxCommission::<T>::get() == Some(U::get()),
				"global maximum commission error"
			);
			ensure!(
				Pallet::<T>::on_chain_storage_version() >= 4,
				"nomination-pools::migration::v4: wrong storage version"
			);
			Ok(())
		}
	}
}

pub mod v5 {
	use super::*;

	#[derive(Decode)]
	pub struct OldRewardPool<T: Config> {
		last_recorded_reward_counter: T::RewardCounter,
		last_recorded_total_payouts: BalanceOf<T>,
		total_rewards_claimed: BalanceOf<T>,
	}

	impl<T: Config> OldRewardPool<T> {
		fn migrate_to_v5(self) -> RewardPool<T> {
			RewardPool {
				last_recorded_reward_counter: self.last_recorded_reward_counter,
				last_recorded_total_payouts: self.last_recorded_total_payouts,
				total_rewards_claimed: self.total_rewards_claimed,
				total_commission_pending: Zero::zero(),
				total_commission_claimed: Zero::zero(),
			}
		}
	}

	/// This migration adds `total_commission_pending` and `total_commission_claimed` field to every
	/// `RewardPool`, if any.
	pub struct MigrateToV5<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV5<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 5 && onchain == 4 {
				let mut translated = 0u64;
				RewardPools::<T>::translate::<OldRewardPool<T>, _>(|_id, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v5())
				});

				current.put::<Pallet<T>>();
				log!(info, "Upgraded {} pools, storage to version {:?}", translated, current);

				// reads: translated + onchain version.
				// writes: translated + current.put.
				T::DbWeight::get().reads_writes(translated + 1, translated + 1)
			} else {
				log!(info, "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			let rpool_keys = RewardPools::<T>::iter_keys().count();
			let rpool_values = RewardPools::<T>::iter_values().count();
			if rpool_keys != rpool_values {
				log!(info, "🔥 There are {} undecodable RewardPools in storage. This migration will try to correct them. keys: {}, values: {}", rpool_keys.saturating_sub(rpool_values), rpool_keys, rpool_values);
			}

			ensure!(
				PoolMembers::<T>::iter_keys().count() == PoolMembers::<T>::iter_values().count(),
				"There are undecodable PoolMembers in storage. This migration will not fix that."
			);
			ensure!(
				BondedPools::<T>::iter_keys().count() == BondedPools::<T>::iter_values().count(),
				"There are undecodable BondedPools in storage. This migration will not fix that."
			);
			ensure!(
				SubPoolsStorage::<T>::iter_keys().count() ==
					SubPoolsStorage::<T>::iter_values().count(),
				"There are undecodable SubPools in storage. This migration will not fix that."
			);
			ensure!(
				Metadata::<T>::iter_keys().count() == Metadata::<T>::iter_values().count(),
				"There are undecodable Metadata in storage. This migration will not fix that."
			);

			Ok((rpool_values as u64).encode())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(data: Vec<u8>) -> Result<(), TryRuntimeError> {
			let old_rpool_values: u64 = Decode::decode(&mut &data[..]).unwrap();
			let rpool_keys = RewardPools::<T>::iter_keys().count() as u64;
			let rpool_values = RewardPools::<T>::iter_values().count() as u64;
			ensure!(
				rpool_keys == rpool_values,
				"There are STILL undecodable RewardPools - migration failed"
			);

			if old_rpool_values != rpool_values {
				log!(
					info,
					"🎉 Fixed {} undecodable RewardPools.",
					rpool_values.saturating_sub(old_rpool_values)
				);
			}

			// ensure all RewardPools items now contain `total_commission_pending` and
			// `total_commission_claimed` field.
			ensure!(
				RewardPools::<T>::iter().all(|(_, reward_pool)| reward_pool
					.total_commission_pending >=
					Zero::zero() && reward_pool
					.total_commission_claimed >=
					Zero::zero()),
				"a commission value has been incorrectly set"
			);
			ensure!(
				Pallet::<T>::on_chain_storage_version() >= 5,
				"nomination-pools::migration::v5: wrong storage version"
			);

			// These should not have been touched - just in case.
			ensure!(
				PoolMembers::<T>::iter_keys().count() == PoolMembers::<T>::iter_values().count(),
				"There are undecodable PoolMembers in storage."
			);
			ensure!(
				BondedPools::<T>::iter_keys().count() == BondedPools::<T>::iter_values().count(),
				"There are undecodable BondedPools in storage."
			);
			ensure!(
				SubPoolsStorage::<T>::iter_keys().count() ==
					SubPoolsStorage::<T>::iter_values().count(),
				"There are undecodable SubPools in storage."
			);
			ensure!(
				Metadata::<T>::iter_keys().count() == Metadata::<T>::iter_values().count(),
				"There are undecodable Metadata in storage."
			);

			Ok(())
		}
	}
}
