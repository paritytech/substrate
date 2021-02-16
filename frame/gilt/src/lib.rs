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
		MaybeSerializeDeserialize, Saturating, Bounded, StoredMapError,
	},
};
use codec::{Codec, Encode, Decode};
use frame_support::{
	ensure,
	traits::{
		Currency, OnUnbalanced, TryDrop, StoredMap, EnsureOrigin, IsType,
		WithdrawReasons, LockIdentifier, LockableCurrency, ExistenceRequirement,
		Imbalance, SignedImbalance, ReservableCurrency, Get, ExistenceRequirement::KeepAlive,
		ExistenceRequirement::AllowDeath, BalanceStatus as Status,
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

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId>;

		type EnlargeOrigin: EnsureOrigin<Self::Origin>;

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
	pub struct ActiveGilt<AccountId, BlockNumber> {
		proportion: Perquintill,
		who: AccountId,
		expiry: BlockNumber,
	}

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
	}

	#[pallet::storage]
	pub type Queues<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		u32,
		Vec<GiltBid<BalanceOf<T>, T::AccountId>>,
		ValueQuery
	>;

	pub type ActiveIndex = u32;

	#[pallet::storage]
	pub type ActiveCounter<T> = StorageValue<_, ActiveIndex, ValueQuery>;

	#[pallet::storage]
	pub type QueueTotals<T> = StorageValue<_, Vec<(u32, BalanceOf<T>)>, ValueQuery>;

	#[pallet::storage]
	pub type ActiveTotal<T> = StorageValue<_, ActiveGiltsTotal<BalanceOf<T>>, ValueQuery>;

	#[pallet::storage]
	pub type Active<T> = StorageMap<
		_,
		Blake2_128Concat,
		ActiveIndex,
		ActiveGilt<<T as frame_system::Config>::AccountId, <T as frame_system::Config>::BlockNumber>,
		ValueQuery
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
		GiltMinted(ActiveIndex, T::BlockNumber, T::AccountId, BalanceOf<T>),
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

			let total_issuance = T::Currency::total_issuance();

			QueueTotals::<T>::try_mutate(|qs| -> Result<(), DispatchError> {
				qs.resize(queue_count as usize, (0, Zero::zero()));
				ensure!(qs[queue_count - 1].0 < T::MaxQueueLen::get(), Error::<T>::QueueFull);
				qs[queue_count - 1].0 += 1;
				T::Currency::reserve(&who, amount)?;
				qs[queue_count - 1].1 += amount;
				Ok(())
			})?;
			Self::deposit_event(Event::BidPlaced(who.clone(), amount, duration));
			Queues::<T>::mutate(duration, |q| q.push(GiltBid { amount, who }));

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

		#[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1))]
		pub fn enlarge(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::EnlargeOrigin::ensure_origin(origin)?;

			// TODO


			Ok(().into())
		}

		/// Remove an active ongoing
		#[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1))]
		pub fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::EnlargeOrigin::ensure_origin(origin)?;

			// TODO
			Ok(().into())
		}
	}
}
