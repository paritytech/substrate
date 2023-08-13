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

//! Various pieces of common functionality.

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Get the owner of the item, if the item exists.
	pub fn owner(collection: T::CollectionId, item: T::ItemId) -> Option<T::AccountId> {
		Item::<T, I>::get(collection, item).map(|i| i.owner)
	}

	/// Get the owner of the collection, if the collection exists.
	pub fn collection_owner(collection: T::CollectionId) -> Option<T::AccountId> {
		Collection::<T, I>::get(collection).map(|i| i.owner)
	}

	/// Validate the `data` was signed by `signer` and the `signature` is correct.
	pub fn validate_signature(
		data: &Vec<u8>,
		signature: &T::OffchainSignature,
		signer: &T::AccountId,
	) -> DispatchResult {
		if signature.verify(&**data, &signer) {
			return Ok(())
		}

		// NOTE: for security reasons modern UIs implicitly wrap the data requested to sign into
		// <Bytes></Bytes>, that's why we support both wrapped and raw versions.
		let prefix = b"<Bytes>";
		let suffix = b"</Bytes>";
		let mut wrapped: Vec<u8> = Vec::with_capacity(data.len() + prefix.len() + suffix.len());
		wrapped.extend(prefix);
		wrapped.extend(data);
		wrapped.extend(suffix);

		ensure!(signature.verify(&*wrapped, &signer), Error::<T, I>::WrongSignature);

		Ok(())
	}

	pub(crate) fn set_next_collection_id(collection: T::CollectionId) {
		let next_id = collection.increment();
		NextCollectionId::<T, I>::set(next_id);
		Self::deposit_event(Event::NextCollectionIdIncremented { next_id });
	}

	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn set_next_id(id: T::CollectionId) {
		NextCollectionId::<T, I>::set(Some(id));
	}

	#[cfg(test)]
	pub fn get_next_id() -> T::CollectionId {
		NextCollectionId::<T, I>::get()
			.or(T::CollectionId::initial_value())
			.expect("Failed to get next collection ID")
	}
}
