// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! A pallet that's designed to ONLY do:
//!
//! If a nominator is not exposed at all in any `ErasStakers` (i.e. "has not backed any validators in the last 28 days"), then they can register themselves in this pallet, and move quickly into a nomination pool.

#![cfg_attr(not(feature = "std"), no_std)]

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_std::prelude::*;

	use frame_support::traits::Currency;
	use pallet_nomination_pools::PoolId;
	use sp_staking::EraIndex;
	use sp_runtime::traits::Saturating;

	type BalanceOf<T> = <<T as pallet_staking::Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ pallet_staking::Config<
			CurrencyBalance = <Self as pallet_nomination_pools::Config>::CurrencyBalance,
		> + pallet_nomination_pools::Config
	{
		type SlashPerEra: Get<BalanceOf<Self>>;
	}

	/// One who wishes to be unstaked.
	#[derive(Encode, Decode, Eq, PartialEq, Clone, scale_info::TypeInfo)]
	pub struct Unstake<AccountId> {
		/// Their stash account.
		stash: AccountId,
		/// The list of eras for which they have been checked.
		checked: Vec<EraIndex>,
		/// The pool they wish to join.
		pool_id: PoolId,
	}

	/// The current "head of the queue" being unstaked.
	#[pallet::storage]
	#[pallet::unbounded]
	pub type Head<T: Config> = StorageValue<_, Unstake<T::AccountId>, OptionQuery>;

	/// The map of all accounts wishing to be unstaked.
	#[pallet::storage]
	pub type Queue<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, PoolId>;

	/// Number of eras to check per block.
	///
	/// If set to 0, this pallet does absolutely nothing.
	///
	/// Based on the amount of weight available ot `on_idle`, up to this many eras of a single nominator might be checked.
	#[pallet::storage]
	pub type ErasToCheckPerBlock<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_idle(_block: T::BlockNumber, remaining_weight: Weight) -> Weight {
			0
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// enqueue oneself to be migrated from
		#[pallet::weight(0)]
		pub fn enqueue(origin: OriginFor<T>, pool_id: PoolId) -> DispatchResult {
			// TODO: they must not already have any unbonding funds, i.e. ledger.unlocking
			// TODO: they should not be able to perform any actions in staking anymore once they are enqueued.. this might be a bit nasty. Should use a custom signed extension.
			let who = ensure_signed(origin)?;
			todo!();
		}
	}

	impl<T: Config> Pallet<T> {
		fn get_unstake_head() -> Option<Unstake<T::AccountId>> {
			Head::<T>::take().or_else(|| {
				Queue::<T>::drain()
					.take(1)
					.map(|(stash, pool_id)| Unstake { stash, pool_id, checked: Default::default() })
					.next()
			})
		}
		/// process up to `remaining_weight`.
		///
		/// Returns the actual weight consumed.
		fn process_head(remaining_weight: Weight) -> Weight {
			let get_unstake_head_weight = T::DbWeight::get().reads(2);
			if remaining_weight < get_unstake_head_weight {
				// nothing can be done.
				return 0;
			}


			let Unstake { stash, mut checked, pool_id } = match Self::get_unstake_head() {
				None => {
					// There's no `Head` and nothing in the `Queue`, nothing to do here.
					return get_unstake_head_weight;
				},
				Some(x) => x,
			};

			let weight_per_era_check = todo!("should come from our benchmarks");
			let max_eras_to_check = remaining_weight.div(weight_per_era_check);
			let final_eras_to_check = ErasToCheckPerBlock::<T>::get().min(max_eras_to_check);

			if final_eras_to_check.is_zero() {
				return get_unstake_head_weight + T::DbWeight::get().reads(1)
			}

			let slash_stash = |eras_checked: EraIndex| {
				let slash_amount = T::SlashPerEra::get().saturating_mul(eras_checked.into());
				let (_, imbalance) = <T as pallet_staking::Config>::Currency::slash(&stash, slash_amount);
			};

			let current_era = pallet_staking::CurrentEra::<T>::get().unwrap_or_default();
			let bonding_duration = <T as pallet_staking::Config>::BondingDuration::get();

			let total_check_range = (current_era.saturating_sub(bonding_duration)..current_era)
				.rev()
				.collect::<Vec<_>>();
			let now_check_range = total_check_range
				.iter()
				.filter(|e| !checked.contains(e))
				.take(final_eras_to_check as usize)
				.collect::<Vec<_>>();

			if now_check_range.is_empty() && final_eras_to_check > 0 {
				// `stash` is not exposed in any era -- we can let go of them now.
				let num_slashing_spans = 0; // TODO
				let ctrl = pallet_staking::Bonded::<T>::get(&stash).unwrap();
				let ledger = pallet_staking::Ledger::<T>::get(ctrl).unwrap();
				pallet_staking::Pallet::<T>::force_unstake(
					frame_system::RawOrigin::Root.into(),
					stash.clone(),
					num_slashing_spans,
				)
				.unwrap();
				pallet_nomination_pools::Pallet::<T>::join(
					frame_system::RawOrigin::Signed(stash.clone()).into(),
					ledger.total,
					pool_id,
				).unwrap();
				0 // TODO return weight, should be the weight of the code in this `if`
			} else {
				let is_exposed = now_check_range.iter().any(|e| Self::is_exposed_in_era(&stash, *e));
				if is_exposed {
					// this account was actually exposed in some era within the range -- slash them and
					// remove them from the queue.
					// TODO: slash
					0 // TODO: return weight, should be 'now_check_range.count() * weight_per_era_check + slash_weight'
				} else {
					// Not exposed in these two eras.
					checked.extend(now_check_range);
					Head::<T>::put(Unstake { stash, checked, pool_id });
					0 // TODO: return weight, should be 'now_check_range.count() * weight_per_era_check'
				}
			}
		}

		fn is_exposed_in_era(who: &T::AccountId, era: &EraIndex) -> bool {
			pallet_staking::ErasStakers::<T>::iter_prefix(era)
				.any(|(_, exposures)| exposures.others.iter().any(|i| i.who == *who))
		}
	}
}
