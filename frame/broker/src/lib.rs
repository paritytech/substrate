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

#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]

pub use pallet::*;

mod mock;
mod tests;
mod benchmarking;

pub mod weights;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use bitvec::BitArr;
	use frame_support::{pallet_prelude::*, traits::fungible::{self, Inspect, Mutate, MutateHold}};
	use frame_system::pallet_prelude::*;
	use sp_runtime::AccountId32;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Currency: Inspect<Self::AccountId>;//Mutate<Self::AccountId> + MutateHold<Self::AccountId>;

		/// Weight information for all calls of this pallet.
		type WeightInfo: WeightInfo;
	}

	pub type BalanceOf<T> = <<T as Config>::Currency as Inspect<<T as frame_system::Config>::AccountId>>::Balance;

	pub type Timeslice = u32;
	pub type CoreIndex = u16;
	// TODO: Use BitArr instead; for this, we'll need to ensure Codec is impl'ed for `BitArr`.
	pub type CorePart = [u8; 10];
	pub type RelayAccountId = AccountId32;
	pub type Balance = u128;
	pub type ParaId = u32;
	/// Counter for the total CoreParts which could be dedicated to a pool. `u32` so we don't ever
	/// get an overflow.
	pub type PartCount = u32;
	pub type SignedPartCount = i32;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionId {
		begin: Timeslice,
		core: CoreIndex,
		part: CorePart,
	}

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionRecord<AccountId> {
		end: Timeslice,
		owner: AccountId,
	}
	pub type RegionRecordOf<T> = RegionRecord<<T as frame_system::Config>::AccountId>;

	// TODO: Use a more specialised 32-bit type which puts Off and InstaPool into unused 32-bit values.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum CoreTask {
		Off,
		Assigned { target: ParaId },
		InstaPool,
	}

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ScheduleItem {
		part: CorePart,
		task: CoreTask,
	}
	pub type Schedule = BoundedVec<ScheduleItem, ConstU32<80>>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum Contributor<AccountId> {
		System,
		Private(AccountId),
	}
	pub type ContributorOf<T> = Contributor<<T as frame_system::Config>::AccountId>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ContributionRecord<AccountId> {
		begin: Timeslice,
		end: Timeslice,
		core: CoreIndex,
		parts: CorePart,
		payee: Contributor<AccountId>,
	}
	pub type ContributionRecordOf<T> = ContributionRecord<<T as frame_system::Config>::AccountId>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct InstaPoolHistoryRecord<Balance> {
		total_contributions: PartCount,
		maybe_payout: Option<Balance>,
	}
	pub type InstaPoolHistoryRecordOf<T> = InstaPoolHistoryRecord<BalanceOf<T>>;

	#[pallet::storage]
	pub type Regions<T> = StorageMap<_, Blake2_128Concat, RegionId, RegionRecordOf<T>, OptionQuery>;

	/// The work we plan on having each core do at a particular time in the future.
	#[pallet::storage]
	pub type Workplan<T> = StorageMap<_, Twox64Concat, (Timeslice, CoreIndex), Schedule, OptionQuery>;

	/// The current workload of each core. This gets updated with workplan as timeslices pass.
	#[pallet::storage]
	pub type Workload<T> = StorageMap<_, Twox64Concat, CoreIndex, Schedule, OptionQuery>;

	#[pallet::storage]
	pub type InstaPoolSize<T> = StorageValue<_, PartCount, ValueQuery>;

	#[pallet::storage]
	pub type InstaPoolContribution<T> = StorageMap<_, Blake2_128Concat, ContributionRecordOf<T>, (), OptionQuery>;

	#[pallet::storage]
	pub type InstaPoolIo<T> = StorageMap<_, Blake2_128Concat, Timeslice, SignedPartCount, ValueQuery>;

	/// Total InstaPool rewards for each Timeslice and the number of core parts which contributed.
	#[pallet::storage]
	pub type InstaPoolHistory<T> = StorageMap<_, Blake2_128Concat, Timeslice, InstaPoolHistoryRecordOf<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Transferred {
			region_id: RegionId,
			old_owner: T::AccountId,
			owner: T::AccountId,
		}
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		UnknownRegion,
		NotOwner,
	}

	#[pallet::call(weight(<T as Config>::WeightInfo))]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn transfer(origin: OriginFor<T>, region_id: RegionId, new_owner: T::AccountId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_transfer(region_id, Some(who), new_owner)?;
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Logic for call `Self::change_value`.
		pub(crate) fn do_transfer(region_id: RegionId, maybe_check_owner: Option<T::AccountId>, new_owner: T::AccountId) -> Result<(), Error<T>> {
			let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

			if let Some(check_owner) = maybe_check_owner {
				ensure!(check_owner == region.owner, Error::<T>::NotOwner);
			}

			let old_owner = region.owner;
			region.owner = new_owner;
			Regions::<T>::insert(&region_id, &region);
			Self::deposit_event(Event::Transferred { region_id, old_owner, owner: region.owner });

			Ok(())
		}
	}
}
