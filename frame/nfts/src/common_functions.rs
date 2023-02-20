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

//! Various pieces of common functionality.

use crate::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Get the owner of the item, if the item exists.
	pub fn owner(collection: T::CollectionId, item: T::ItemId) -> Option<T::AccountId> {
		Item::<T, I>::get(collection, item).map(|i| i.owner)
	}

	/// Get the owner of the collection, if the collection exists.
	pub fn collection_owner(collection: T::CollectionId) -> Option<T::AccountId> {
		Collection::<T, I>::get(collection).map(|i| i.owner)
	}

	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn set_next_id(id: T::CollectionId) {
		NextCollectionId::<T, I>::set(Some(id));
	}

	#[cfg(test)]
	pub fn get_next_id() -> T::CollectionId {
		NextCollectionId::<T, I>::get().unwrap_or(T::CollectionId::initial_value())
	}
}
