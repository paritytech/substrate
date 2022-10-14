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

/// The helper methods bellow allow to read and validate different
/// collection/item/pallet settings.
/// For example, those settings allow to disable NFTs trading on a pallet level, or for a particular
/// collection, or for a specific item.
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn get_collection_settings(
		collection_id: &T::CollectionId,
	) -> Result<CollectionSettings, DispatchError> {
		let config = CollectionConfigOf::<T, I>::get(&collection_id)
			.ok_or(Error::<T, I>::UnknownCollection)?;
		Ok(config.values())
	}

	pub fn get_item_settings(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
	) -> Result<ItemSettings, DispatchError> {
		let config = ItemConfigOf::<T, I>::get(&collection_id, &item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		Ok(config.values())
	}

	pub fn is_collection_setting_disabled(
		collection_id: &T::CollectionId,
		setting: CollectionSetting,
	) -> Result<(bool, CollectionSettings), DispatchError> {
		let settings = Self::get_collection_settings(&collection_id)?;
		Ok((!settings.contains(setting), settings))
	}

	pub fn is_item_setting_disabled(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
		setting: ItemSetting,
	) -> Result<(bool, ItemSettings), DispatchError> {
		let settings = Self::get_item_settings(&collection_id, &item_id)?;
		Ok((!settings.contains(setting), settings))
	}

	pub fn is_pallet_feature_enabled(feature: PalletFeature) -> bool {
		let features = T::Features::get();
		return !features.0.contains(feature)
	}
}
