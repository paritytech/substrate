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

impl<T: Config> Pallet<T> {
	pub fn do_set_collection_metadata(
		id: T::CollectionId,
		config: CollectionConfig,
		sender: T::AccountId,
		data: MetadataOf<T>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();

		if user_features.contains(UserFeatures::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into());
		}

		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;

		ensure!(collection.owner == sender, Error::<T>::NotAuthorized);

		// do the logic

		let mut metadata = CollectionMetadataOf::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;

		metadata.data = data.clone();

		CollectionMetadataOf::<T>::insert(id, metadata);
		Self::deposit_event(Event::<T>::CollectionMetadataSet { id, data });

		Ok(())
	}
}
