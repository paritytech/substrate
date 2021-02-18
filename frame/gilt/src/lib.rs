// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Gilt Pallet
//! A pallet allowing accounts to auction for being frozen and receive open-ended
//! inflation-protection in return.

use sp_std::prelude::*;

use sp_std::{cmp, result, mem, fmt::Debug, ops::BitOr};
use sp_arithmetic::Perquintill;
use sp_runtime::{
	RuntimeDebug, DispatchResult, DispatchError,
	traits::{
		Zero, AtLeast32BitUnsigned, StaticLookup, CheckedAdd, CheckedSub,
		MaybeSerializeDeserialize, Saturating, Bounded, StoredMapError, SaturatedConversion
	},
};
use codec::{Codec, Encode, Decode};
use frame_support::{
	ensure,
	traits::{
		Currency, OnUnbalanced, TryDrop, StoredMap, EnsureOrigin, IsType,
		WithdrawReasons, LockIdentifier, LockableCurrency, ExistenceRequirement,
		Imbalance, SignedImbalance, ReservableCurrency, Get, ExistenceRequirement::KeepAlive,
		ExistenceRequirement::AllowDeath, BalanceStatus as Status
	}
};
#[cfg(feature = "std")]
use frame_support::traits::GenesisBuild;

pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::PositiveImbalance;
	type NegativeImbalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId>;

		type EnlargeOrigin: EnsureOrigin<Self::Origin>;

		type Deficit: OnUnbalanced<PositiveImbalanceOf<Self>>;
		type Surplus: OnUnbalanced<NegativeImbalanceOf<Self>>;

		#[pallet::constant]
		type QueueCount: Get<u32>;

		#[pallet::constant]
		type MaxQueueLen: Get<u32>;

		#[pallet::constant]
		type Period: Get<Self::BlockNumber>;

		#[pallet::constant]
		type MinFreeze: Get<BalanceOf<Self>>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct GiltBid<Balance, AccountId> {
		amount: Balance,
		who: AccountId,
	}

	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct ActiveGilt<Balance, AccountId, BlockNumber> {
		proportion: Perquintill,
		amount: Balance,
		who: AccountId,
		expiry: BlockNumber,
	}

	pub type ActiveIndex = u32;

	/// The way of determining the net issuance (i.e. after factoring in all maturing frozen funds)
	/// is:
	///
	/// `total_issuance - frozen + proportion * total_issuance`
	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct ActiveGiltsTotal<Balance> {
		/// The total amount of funds held in reserve for all active gilts.
		frozen: Balance,
		/// The proportion of funds that the `frozen` balance represents to total issuance.
		proportion: Perquintill,
		/// The total number of gilts issued so far.
		index: ActiveIndex,
	}

	#[pallet::storage]
	pub type Queues<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		u32,
		Vec<GiltBid<BalanceOf<T>, T::AccountId>>,
		ValueQuery,
	>;

	#[pallet::storage]
	pub type QueueTotals<T> = StorageValue<_, Vec<(u32, BalanceOf<T>)>, ValueQuery>;

	#[pallet::storage]
	pub type ActiveTotal<T> = StorageValue<_, ActiveGiltsTotal<BalanceOf<T>>, ValueQuery>;

	#[pallet::storage]
	pub type Active<T> = StorageMap<
		_,
		Blake2_128Concat,
		ActiveIndex,
		ActiveGilt<BalanceOf<T>, <T as frame_system::Config>::AccountId, <T as frame_system::Config>::BlockNumber>,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::metadata(T::AccountId = "AccountId")]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A bid was successfully placed.
		/// \[ who, amount, duration \]
		BidPlaced(T::AccountId, BalanceOf<T>, u32),
		/// A bid was successfully removed (before being accepted as a gilt).
		/// \[ who, amount, duration \]
		BidRetracted(T::AccountId, BalanceOf<T>, u32),
		/// A bid was accepted as a gilt. The balance may not be released until expiry.
		/// \[ index, expiry, who, amount \]
		GiltIssued(ActiveIndex, T::BlockNumber, T::AccountId, BalanceOf<T>),
		/// An expired gilt has been thawed.
		/// \[ index, who, original_amount, additional_amount \]
		GiltThawed(ActiveIndex, T::AccountId, BalanceOf<T>, BalanceOf<T>),
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		DurationTooSmall,
		DurationTooBig,
		AmountTooSmall,
		QueueFull,
		/// Gilt index is known.
		Unknown,
		/// Not the owner of the gilt.
		NotOwner,
		/// Gilt not yet at expiry date.
		NotExpired,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T:Config> Pallet<T> {
		/// Place a bid.
		#[pallet::weight(10_000 + T::DbWeight::get().writes(1))]
		pub fn place_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let queue_count = T::QueueCount::get() as usize;
			ensure!(duration > 0, Error::<T>::DurationTooSmall);
			ensure!(duration <= queue_count as u32, Error::<T>::DurationTooBig);
			ensure!(amount >= T::MinFreeze::get(), Error::<T>::AmountTooSmall);

			QueueTotals::<T>::try_mutate(|qs| -> Result<(), DispatchError> {
				qs.resize(queue_count as usize, (0, Zero::zero()));
				ensure!(qs[queue_count - 1].0 < T::MaxQueueLen::get(), Error::<T>::QueueFull);
				qs[queue_count - 1].0 += 1;
				T::Currency::reserve(&who, amount)?;
				qs[queue_count - 1].1 += amount;
				Ok(())
			})?;
			Self::deposit_event(Event::BidPlaced(who.clone(), amount, duration));
			Queues::<T>::mutate(duration, |q| q.insert(0, GiltBid { amount, who }));

			Ok(().into())
		}

		/// Retract a previously placed bid.
		#[pallet::weight(10_000 + T::DbWeight::get().writes(1))]
		pub fn retract_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// TODO

			Ok(().into())
		}

		/// Allow more freezing up to `amount`.
		#[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1))]
		pub fn enlarge(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::EnlargeOrigin::ensure_origin(origin)?;

			let total_issuance = T::Currency::total_issuance();
			let mut remaining = amount;
			let now = frame_system::Module::<T>::block_number();

			ActiveTotal::<T>::mutate(|totals| {
				QueueTotals::<T>::mutate(|qs| {
					for periods in (1..=T::QueueCount::get()).rev() {
						if qs[periods as usize - 1].0 == 0 {
							continue
						}
						let index = periods as usize - 1;
						let expiry = now + T::Period::get() * periods.into();
						Queues::<T>::mutate(periods, |q| {
							while let Some(mut bid) = q.pop() {
								if remaining < bid.amount {
									let overflow = bid.amount - remaining;
									bid.amount = remaining;
									q.push(GiltBid { amount: overflow, who: bid.who.clone() });
								}
								let amount = bid.amount;
								// Can never overflow due to block above.
								remaining -= amount;
								// Should never underflow since it should track the total of the bids
								// exactly, but we'll be defensive.
								qs[index].1 = qs[index].1.saturating_sub(bid.amount);

								// Now to activate the bid...
								let liquid_issuance: u128 = total_issuance.saturating_sub(totals.frozen)
									.saturated_into();
								let frozen_issuance = totals.proportion * liquid_issuance;
								let actual_issued = frozen_issuance.saturating_add(liquid_issuance);
								let n: u128 = amount.saturated_into();
								let d = actual_issued;
								let proportion = Perquintill::from_rational_approximation(n, d);
								let who = bid.who;
								let index = totals.index;
								totals.frozen += bid.amount;
								totals.proportion = totals.proportion.saturating_add(proportion);
								totals.index += 1;
								let e = Event::GiltIssued(index, expiry, who.clone(), amount);
								Self::deposit_event(e);
								let gilt = ActiveGilt { amount, proportion, who, expiry };
								Active::<T>::insert(index, gilt);

								if remaining.is_zero() {
									break;
								}
							}
							qs[index].0 = q.len() as u32;
						});
						if remaining.is_zero() {
							break
						}
					}
				});
			});
			Ok(().into())
		}

		/// Remove an active ongoing
		#[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1))]
		pub fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact] index: ActiveIndex,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let gilt = Active::<T>::get(index).ok_or(Error::<T>::Unknown)?;
			// If found, check the owner is `who`.
			ensure!(gilt.who == who, Error::<T>::NotOwner);
			let now = frame_system::Module::<T>::block_number();
			ensure!(now >= gilt.expiry, Error::<T>::NotExpired);
			// Remove it
			Active::<T>::remove(index);

			// Multiply the proportion it is by the total issued.
			let total_issuance = T::Currency::total_issuance();
			ActiveTotal::<T>::mutate(|totals| {
				let liquid_issuance: u128 = total_issuance.saturating_sub(totals.frozen)
					.saturated_into();
				let frozen_issuance = totals.proportion * liquid_issuance;
				let actual_issued = frozen_issuance.saturating_add(liquid_issuance);
				let gilt_value: BalanceOf<T> = (gilt.proportion * actual_issued).saturated_into();

				totals.frozen = totals.frozen.saturating_sub(gilt.amount);
				totals.proportion = totals.proportion.saturating_sub(gilt.proportion);

				// Remove or mint the additional to the amount using `Deficit`/`Surplus`.
				if gilt_value > gilt.amount {
					// Unreserve full amount.
					T::Currency::unreserve(&gilt.who, gilt.amount);
					let amount = gilt_value - gilt.amount;
					let deficit = T::Currency::deposit_creating(&gilt.who, amount);
					T::Deficit::on_unbalanced(deficit);
				} else if gilt_value < gilt.amount {
					// We take anything reserved beyond the gilt's final value.
					let rest = gilt.amount - gilt_value;
					// `slash` might seem a little aggressive, but it's the only way to do it
					// in case it's locked into the staking system.
					let surplus = T::Currency::slash_reserved(&gilt.who, rest).0;
					T::Surplus::on_unbalanced(surplus);
					// Unreserve only its new value (less than the amount reserved). Everything
					// should add up, but (defensive) in case it doesn't, unreserve takes lower
					// priority over the funds.
					T::Currency::unreserve(&gilt.who, gilt_value);
				}

				let e = Event::GiltThawed(index, gilt.who, gilt.amount, gilt_value);
				Self::deposit_event(e);
			});

			Ok(().into())
		}
	}
}
