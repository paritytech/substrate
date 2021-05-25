// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd. SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

//! # Gift Pallet
//! A pallet allowing existing users to onboard new users by sending them tokens before they have
//! created an account.
//!
//! ## Overview
//!
//! Alice wants to send DOT to Bob as a gift for this birthday, but Bob is not really familiar with
//! Polkadot and does not have a Polkadot account.
//!
//! Alice uses the Gift pallet to reserve some funds in her account, and allows access to a "shared
//! account" to transfer those funds away from Alice. (similar to transfer approvals)
//!
//! Alice then shares the private key of the shared account with Bob, who can then generate a brand
//! new account that Alice has no idea about, and then use the shared account to finally transfer
//! balance to Bob's final account.
//!
//! ## Design
//!
//! This pallet is designed to solve the following problems:
//! * Allow Alice to send gift to a user who does not have an account (yet)
//! * Allow a new user to safely claim those funds without exposing or involving anyone else for
//!   account creation
//! * Allow the new user to make that claim without needing to have any initial funds (a free
//!   transaction)
//!

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{
		pallet_prelude::*,
		traits::{Currency, ExistenceRequirement, ReservableCurrency},
		sp_runtime::traits::{CheckedAdd, Saturating, Zero},
	};
	use frame_system::pallet_prelude::*;

	type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Because this pallet emits events, it depends on the runtime's definition of an event.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// The Balances of your system.
		type Currency: ReservableCurrency<Self::AccountId>;
		/// The additional deposit needed to place a gift. Should be greater than the existential
		/// deposit to avoid killing the gifter account.
		type GiftDeposit: Get<BalanceOf<Self>>;
		/// The minimum gift amount. Should be greater than the existential deposit.
		type MinimumGift: Get<BalanceOf<Self>>;

	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[derive(Encode, Decode)]
	pub struct GiftInfo<AccountId, Balance> {
		gifter: AccountId,
		deposit: Balance,
		amount: Balance,
	}

	#[pallet::storage]
	#[pallet::getter(fn gifts)]
	pub type Gifts<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		GiftInfo<T::AccountId, BalanceOf<T>>,
	>;

	#[pallet::event]
	#[pallet::metadata(T::AccountId = "AccountId", BalanceOf<T> = "Balance")]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A gift has been created! [amount, claimer]
		GiftCreated(BalanceOf<T>, T::AccountId),
		/// A gift has been claimed! [claimer, amount, to]
		GiftClaimed(T::AccountId, BalanceOf<T>, T::AccountId),
		/// A gift has been removed :( [to]
		GiftRemoved(T::AccountId),
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// User already has a pending gift.
		PendingGift,
		/// Don't be cheap... Get your friend a good gift!
		GiftTooSmall,
		/// An overflow has occurred.
		Overflow,
		/// A gift does not exist for this user.
		NoGift,
		/// You are not the owner of this gift.
		NotGifter,
	}

	// Dispatchable functions allows users to interact with the pallet and invoke state changes.
	// These functions materialize as "extrinsics", which are often compared to transactions.
	// Dispatchable functions must be annotated with a weight and must return a DispatchResult.
	#[pallet::call]
	impl<T:Config> Pallet<T> {
		/// Create a gift.
		///
		/// A gift is some balance which is reserved from the calling account, and placed under
		/// control of the `controller` account.
		///
		/// The credentials of this controller account can be shared with anyone, allow them to then
		/// transfer the balance to a final account, without needing to expose the final accounts
		/// credentials. This is done via the `claim` extrinsic.
		///
		/// NOTE: The fee of this extrinsic should take into account the full cost of `claim`, which
		/// is allowed for free as a result of this extrinsic.
		#[pallet::weight(0)]
		fn gift(origin: OriginFor<T>, amount: BalanceOf<T>, controller: T::AccountId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(!Gifts::<T>::contains_key(&controller), Error::<T>::PendingGift);
			ensure!(amount >= T::MinimumGift::get(), Error::<T>::GiftTooSmall);

			let deposit = T::GiftDeposit::get();
			let total_reserve = amount.checked_add(&deposit).ok_or(Error::<T>::Overflow)?;
			T::Currency::reserve(&who, total_reserve)?;

			// All checks have passed, so let's create the gift.
			let gift = GiftInfo {
				gifter: who,
				deposit,
				amount,
			};

			Gifts::<T>::insert(&controller, gift);
			Self::deposit_event(Event::<T>::GiftCreated(amount, controller));
			Ok(())
		}

		/// Claim a gift.
		///
		/// This extrinsic allows a controller of a gift to transfer the reserved balance to a final
		/// `to` account.
		///
		/// The intention of this extrinsic is to allow a brand new user to claim a gift without
		/// needing to pay transaction fees.
		#[pallet::weight((0, Pays::No))] // Does not pay fee, so we MUST prevalidate this function
		fn claim(origin: OriginFor<T>, to: T::AccountId) -> DispatchResult {
			// In the pre-validation function we confirmed that this user has a gift, and this
			// signed transaction is enough for them to claim it to whomever.
			let who = ensure_signed(origin)?;

			// They should 100% have a gift, but no reason not to handle the error anyway.
			let gift = Gifts::<T>::take(&who).ok_or(Error::<T>::NoGift)?;

			let err_amount = T::Currency::unreserve(&gift.gifter, gift.deposit.saturating_add(gift.amount));
			// Should always have enough reserved unless there is a bug somewhere.
			debug_assert!(err_amount.is_zero());
			let res = T::Currency::transfer(&gift.gifter, &to, gift.amount, ExistenceRequirement::AllowDeath);
			// Should never fail because we unreserve more than this above.
			debug_assert!(res.is_ok());

			Self::deposit_event(Event::<T>::GiftClaimed(who, gift.amount, to));
			Ok(())
		}

		/// Remove a gift.
		///
		/// The original gifter can revoke a gift assuming that it has not been claimed.
		#[pallet::weight(0)]
		fn remove(origin: OriginFor<T>, to: T::AccountId) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let gift = Gifts::<T>::get(&to).ok_or(Error::<T>::NoGift)?;
			ensure!(gift.gifter == who, Error::<T>::NotGifter);

			let err_amount = T::Currency::unreserve(&gift.gifter, gift.deposit.saturating_add(gift.amount));
			// Should always have enough reserved unless there is a bug somewhere.
			debug_assert!(err_amount.is_zero());

			Gifts::<T>::remove(&to);

			Self::deposit_event(Event::<T>::GiftRemoved(to));
			Ok(())
		}
	}
}

use codec::{Encode, Decode};
use frame_support::{
	pallet_prelude::*,
	traits::IsSubType,
	sp_runtime::traits::{DispatchInfoOf, SignedExtension},
};

#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct PrevalidateGiftClaim<T: Config + Send + Sync>(core::marker::PhantomData<T>) where
	<T as frame_system::Config>::Call: IsSubType<Call<T>>;

impl<T: Config + Send + Sync> core::fmt::Debug for PrevalidateGiftClaim<T> where
	<T as frame_system::Config>::Call: IsSubType<Call<T>>
{
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		write!(f, "PrevalidateGiftClaim")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut core::fmt::Formatter) -> core::fmt::Result {
		Ok(())
	}
}

impl<T: Config + Send + Sync> PrevalidateGiftClaim<T> where
	<T as frame_system::Config>::Call: IsSubType<Call<T>>
{
	pub fn new() -> Self {
		Self(core::marker::PhantomData)
	}
}

impl<T: Config + Send + Sync> SignedExtension for PrevalidateGiftClaim<T> where
	<T as frame_system::Config>::Call: IsSubType<Call<T>>
{
	type AccountId = T::AccountId;
	type Call = <T as frame_system::Config>::Call;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "PrevalidateGiftClaim";

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		if let Some(local_call) = call.is_sub_type() {
			if let Call::claim(_to) = local_call {
				// All we need to check is that the caller has a gift they own.
				Gifts::<T>::get(who).ok_or(InvalidTransaction::BadProof)?;
			}
		}
		Ok(ValidTransaction::default())
	}
}
