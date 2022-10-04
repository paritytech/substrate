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

use scale_info::TypeInfo;
use sp_arithmetic::traits::Saturating;
use sp_core::bounded::BoundedVec;
use sp_runtime::{
	traits::{Convert, StaticLookup},
	ArithmeticError::Overflow,
	Perbill, RuntimeDebug,
};
use sp_std::{marker::PhantomData, prelude::*};

use frame_support::{
	codec::{Decode, Encode, MaxEncodedLen},
	dispatch::{DispatchError, DispatchResultWithPostInfo, PostDispatchInfo},
	ensure,
	traits::{EnsureOrigin, PollStatus, Polling, Time, VoteTally},
	CloneNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// The index of a globally synced meet---starts at zero and increments once per month.
pub type MeetsIndex = u32;

/// The ID of a specific party ("bubble").
pub type BubbleId = u32;

/// Record needed for every member.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Person {
	/// The personhood score, valid as of `valid_until` sync.
	score: u32,
	/// The attendence counter, valid as of `valid_until` sync.
	attendance_counter: u32,
	/// The party at which `attendence_counter` is valid.
	valid_until: MeetIndex,
}

impl Person {
	/// Increments `valid_until` to `until`, reducing `score` and `attendence_counter` accordingly.
	pub fn skip_to(&mut self, until: SyncIndex) {
		todo!()
	}

	/// Skips to `at - 1`, then increments `attendence_counter` and adjusts score accorindgly.
	/// `Err` if `valid_until` is greater than `at`.
	pub fn see(&mut self, at: SyncIndex) -> Result<(), ()> {
		todo!()
	}
}

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Sync<Moment> {
	begin: Moment,
}

// TODO: introduce Time::Moment::seconds_later() and Time::Moment::seconds_earlier()

/// The offset of the meetup in half-hour intervals from the initial meetup.
///
/// Valid values are `0..=30`.
pub type Phase = u8;

/// A standard geolocation, in billionths.
pub type GeoLocation = (u64, u64);

/// Record needed for every bubble.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Bubbke<AccountId> {
	meets: MeetIndex,
	phase: Phase,
	location: GeoLocation,
	capacity: u32,
	description: [u8; 32],
	//	organiser: T::AccountId,
	//	deposit: BalanceOf<T>,
	/// determined immediately prior to the party start randomly from the RSVPs list.
	super_nodes: BoundedVec<AccountId, 8>,
	earlier_bubbles: BoundedVec<BubbleId, 4>,
	later_bubbles: BoundedVec<BubbleId, 4>,
	contemp_bubbles: BoundedVec<BubbleId, 4>,
}

pub type SyncOf<T> = Sync<<<T as Config>::Time as Time>::Moment>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, storage::KeyLenOf};
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

		type Time: Time;
	}

	/// The current individuals we recognise.
	#[pallet::storage]
	pub type People<T: Config<I>> = StorageMap<_, Twox64Concat, T::AccountId, Person>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>> {
		/// A member `who` has been added.
		MemberAdded { who: T::AccountId },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Dummy.
		Dummy,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Introduce a new member.
		///
		/// - `origin`: Must be the `AdminOrigin`.
		/// - `who`: Account of non-member which will become a member.
		/// - `rank`: The rank to give the new member.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::add_member())]
		pub fn add_member(origin: OriginFor<T>) -> DispatchResult {
			let _who = ensure_signed(origin)?;
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {}
}
