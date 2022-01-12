// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! The signed phase.

use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::PageIndex;
use frame_support::{traits::Currency, BoundedVec};
use scale_info::TypeInfo;
use sp_npos_elections::ElectionScore;

/// Exports of this pallet
pub use pallet::*;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Default)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct SubmissionMetadata<T: Config> {
	deposit: BalanceOf<T>,
	fee: BalanceOf<T>,
	reward: BalanceOf<T>,
	claimed_score: ElectionScore,
	pages: BoundedVec<PageIndex, T::Pages>,
}

#[frame_support::pallet]
mod pallet {
	use super::*;
	use frame_support::pallet_prelude::{StorageDoubleMap, *};
	use frame_system::pallet_prelude::*;

	pub trait WeightInfo {}
	impl WeightInfo for () {}

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: crate::Config {
		type Currency: Currency<Self::AccountId>;
		type WeightInfo: WeightInfo;
	}

	/// Double map from (account, page) to a solution page.
	#[pallet::storage]
	type Submissions<T: Config> =
		StorageDoubleMap<_, Twox64Concat, T::AccountId, Twox64Concat, PageIndex, T::Solution>;
	/// Map from account to the metadata of their submission.
	///
	/// invariant: for any Key1 of type `AccountId` in [`Submissions`], this storage map also has a
	/// value.
	#[pallet::storage]
	type SubmissionMetadataStorage<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, SubmissionMetadata<T>>;

	#[pallet::pallet]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}
}

impl<T: Config> Pallet<T> {}
