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

//! Proof-of-Personhood system.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "128"]

use codec::Codec;
use scale_info::TypeInfo;
use sp_arithmetic::traits::Saturating;
use sp_core::bounded::BoundedVec;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Convert, StaticLookup},
	ArithmeticError::Overflow,
	Perbill, RuntimeDebug,
};
use sp_std::{marker::PhantomData, prelude::*};

use frame_support::{
	codec::{Decode, Encode, MaxEncodedLen},
	dispatch::{DispatchError, DispatchResultWithPostInfo, PostDispatchInfo},
	ensure,
	traits::{EnsureOrigin, PollStatus, Polling, RankedMembers, Time, VoteTally},
	CloneNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// Payroll cycle.
pub type Cycle = u32;

// Can be implemented by Pot pallet with a fixed Currency impl, but can also be implemented with
// XCM/MultiAsset and made generic over assets.
pub trait Pay {
	/// The type by which we measure units of the currency in which we make payments.
	type Balance: AtLeast32BitUnsigned + Codec + MaxEncodedLen;
	/// The type by which we identify the individuals to whom a payment may be made.
	type AccountId;
	/// An identifier given to an individual payment.
	type Id;
	/// The amount of currency with which we have to make payments in this period. It may be a fixed
	/// value or reduce as calls to `pay` are made. It should be called once prior to the series of
	/// payments to determine the overall budget and then not again until the next series of
	/// payments are to be made.
	fn budget() -> Self::Balance;
	/// Make a payment and return an identifier for later evaluation of success in some off-chain
	/// mechanism (likely an event, but possibly not on this chain).
	fn pay(who: &Self::AccountId, amount: Self::Balance) -> Result<Self::Id, ()>;
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, storage::KeyLenOf, weights::PaysFee};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The runtime event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Means by which we can make payments to accounts. This also defines the currency and the
		/// balance which we use to denote that currency.
		type Paymaster: Pay<AccountId = <Self as frame_system::Config>::AccountId>;

		/// The current membership of payees.
		type Members: RankedMembers<AccountId = <Self as frame_system::Config>::AccountId>;

		/// The maximum payout to be made for a single period to an active member of the given rank.
		type ActiveSalaryForRank: Convert<Self::Members::Rank, Self::Paymaster::Balance>;

		/// The number of blocks between sequential payout cycles.
		#[pallet::constant]
		type CyclePeriod: Get<Self::BlockNumber>;
	}

	/// The next payout cycle to pay, and the block nunber at which it should be paid.
	#[pallet::storage]
	pub(super) type LastPayout<T: Config<I>, I: 'static = ()> =
		StorageValue<_, T::BlockNumber, OptionQuery>;

	/// The most recent cycle which was paid to a member. None implies that a member has not yet
	/// been paid.
	#[pallet::storage]
	pub(super) type LastClaim<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, T::BlockNumber, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A member is inducted into the payroll.
		Inducted { who: T::AccountId },
		/// A payment happened.
		Paid { who: T::AccountId },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The account is not a ranked member.
		NotMember,
		// The account is not yet inducted into the system.
		NotInducted,
		/// The member does not have a current valid claim.
		NoClaim,
		/// Cycle is not yet over.
		NotYet,
		/// The payout cycles have not yet started.
		NotStarted,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		#[pallet::weight(T::WeightInfo::add_member())]
		pub fn induct(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let _ = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			let last_payout = LastPayout::<T, I>::get().unwrap_or_else(Zero::zero);
			LastClaim::<T, I>::put(who, last_payout);
			Self::deposit_event(Event::<T, I>::Inducted { who });
			Ok(Pays::No.into())
		}

		// TODO: preregistration of activity for the next cycle.

		/// Request a payout.
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members`.
		#[pallet::weight(T::WeightInfo::add_member())]
		pub fn payout(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let _rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			let last_claim = LastClaim::<T, I>::get(who).ok_or(Error::<T, I>::NotInducted)?;
			let last_payout = LastPayout::<T, I>::get().or_or(Error::<T, I>::NotStarted)?;
			ensure!(last_claim < last_payout, Error::<T, I>::NoClaim);
			LastClaim::<T, I>::put(who, last_payout);

			// TODO: make payout according to rank and activity.
			let amount = Self::deposit_event(Event::<T, I>::Paid { who });
			Ok(Pays::No.into())
		}

		/// Move to next payout cycle, assuming that the present block
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members`.
		#[pallet::weight(T::WeightInfo::add_member())]
		pub fn next_cycle(origin: OriginFor<T>) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			let now = frame_system::Pallet::<T>::block_number();
			let last_payout = LastPayout::<T, I>::get().or_or(Error::<T, I>::NoClaim)?;
			let next_payout = last_payout.saturating_add(T::CyclePeriod::get());
			ensure!(now >= next_payout, Error::<T, I>::NotYet);
			LastPayout::<T, I>::put(next_payout);
			Ok(Pays::No.into())
		}
	}

	impl<T: Config<I>, I: 'static> Pallet<T, I> {}
}
