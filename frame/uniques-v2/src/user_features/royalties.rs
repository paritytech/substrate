// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::*;
use enumflags2::BitFlags;
use frame_support::pallet_prelude::*;
use sp_runtime::Perbill;

impl<T: Config> Pallet<T> {
	pub fn do_change_creator_royalties(
		caller: T::AccountId,
		id: T::CollectionId,
		royalties: Perbill,
	) -> DispatchResult {
		Collections::<T>::try_mutate(id, |maybe_collection| {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(collection.creator == caller, Error::<T>::NotAuthorized);

			// royalties can only be decreased
			ensure!(
				royalties < collection.creator_royalties,
				Error::<T>::RoyaltiesBiggerToPreviousValue
			);

			collection.creator_royalties = royalties;

			// TODO: update collection config

			Self::deposit_event(Event::CreatorRoyaltiesChanged {
				id,
				royalties,
				creator: collection.creator.clone(),
			});

			Ok(())
		})
	}

	pub fn do_change_owner_royalties(
		caller: T::AccountId,
		id: T::CollectionId,
		config: CollectionConfig,
		royalties: Perbill,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();
		let is_locked = user_features.contains(UserFeatures::IsLocked);

		Collections::<T>::try_mutate(id, |maybe_collection| {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

			ensure!(
				collection.owner_royalties + collection.creator_royalties < Perbill::one(),
				Error::<T>::TotalRoyaltiesExceedHundredPercent
			);

			// if collection is locked then royalties can only be decreased
			ensure!(
				!is_locked || royalties < collection.owner_royalties,
				Error::<T>::RoyaltiesBiggerToPreviousValue
			);

			collection.owner_royalties = royalties;

			// TODO: update collection config

			Self::deposit_event(Event::OwnerRoyaltiesChanged {
				id,
				royalties,
				owner: collection.owner.clone(),
			});

			Ok(())
		})
	}
}
