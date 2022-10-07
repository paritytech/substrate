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
use frame_support::pallet_prelude::*;

/// Freeze functions allow to make particular items non-transferable.
/// It's also possible to revert the setting back.
/// An origin must have a `Freezer` role in order to call those methods.
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_freeze_item(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(collection_details.freezer == origin, Error::<T, I>::NoPermission);

		let mut settings = Self::get_item_settings(&collection, &item)?;
		if !settings.contains(ItemSetting::NonTransferable) {
			settings.insert(ItemSetting::NonTransferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, ItemConfig(settings));

		Self::deposit_event(Event::<T, I>::Frozen { collection, item });
		Ok(())
	}

	pub fn do_thaw_item(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(collection_details.freezer == origin, Error::<T, I>::NoPermission);

		let mut settings = Self::get_item_settings(&collection, &item)?;
		if settings.contains(ItemSetting::NonTransferable) {
			settings.remove(ItemSetting::NonTransferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, ItemConfig(settings));

		Self::deposit_event(Event::<T, I>::Thawed { collection, item });
		Ok(())
	}
}
