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

	#[derive(Encode, Decode, Eq, PartialEq, Clone, scale_info::TypeInfo)]
	pub struct Unstake<AccountId> {
		stash: AccountId,
		checked: Vec<EraIndex>,
		pool_id: PoolId,
	}

	#[pallet::storage]
	#[pallet::unbounded]
	pub type Head<T: Config> = StorageValue<_, Unstake<T::AccountId>, OptionQuery>;

	#[pallet::storage]
	pub type Queue<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, PoolId>;

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
		#[pallet::weight(0)]
		pub fn enqueue(origin: OriginFor<T>, pool_id: PoolId) -> DispatchResult {
			// TODO: they must not already have any unbonding funds.
			let who = ensure_signed(origin)?;
			todo!();
		}
	}

	impl<T: Config> Pallet<T> {
		fn process_head() {
			let eras_to_check = ErasToCheckPerBlock::<T>::get();
			let maybe_next = Head::<T>::take().or_else(|| {
				Queue::<T>::drain()
					.take(1)
					.map(|(stash, pool_id)| Unstake { stash, pool_id, checked: Default::default() })
					.next()
			});

			let Unstake { stash, mut checked, pool_id } = match maybe_next {
				None => return,
				Some(x) => x,
			};

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
				.take(eras_to_check as usize)
				.collect::<Vec<_>>();

			if now_check_range.is_empty() && eras_to_check > 0 {
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
			} else {
				let is_exposed = now_check_range.iter().any(|e| Self::is_exposed_in_era(&stash, *e));
				if is_exposed {
					// this account was actually exposed in some era within the range -- slash them and
					// remove them from the queue.
					// TODO: slash
				} else {
					// Not exposed in these two eras.
					checked.extend(now_check_range);
					Head::<T>::put(Unstake { stash, checked, pool_id });
				}
			}

		}

		fn is_exposed_in_era(who: &T::AccountId, era: &EraIndex) -> bool {
			pallet_staking::ErasStakers::<T>::iter_prefix(era)
				.any(|(_, exposures)| exposures.others.iter().any(|i| i.who == *who))
		}
	}
}
