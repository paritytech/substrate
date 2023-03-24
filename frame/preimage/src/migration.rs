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

//! Storage migrations for the preimage pallet.

use super::*;
use frame_support::{
	storage_alias,
	traits::{ConstU32, OnRuntimeUpgrade},
};
use sp_std::collections::btree_map::BTreeMap;

/// The log target.
const TARGET: &'static str = "runtime::preimage::migration::v1";

/// The original data layout of the preimage pallet without a specific version number.
mod v0 {
	use super::*;

	#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo, MaxEncodedLen, RuntimeDebug)]
	pub enum RequestStatus<AccountId, Balance> {
		Unrequested(Option<(AccountId, Balance)>),
		Requested(u32),
	}

	#[storage_alias]
	pub type PreimageFor<T: Config> = StorageMap<
		Pallet<T>,
		Identity,
		<T as frame_system::Config>::Hash,
		BoundedVec<u8, ConstU32<MAX_SIZE>>,
	>;

	#[storage_alias]
	pub type StatusFor<T: Config> = StorageMap<
		Pallet<T>,
		Identity,
		<T as frame_system::Config>::Hash,
		RequestStatus<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
	>;

	/// Returns the number of images or `None` if the storage is corrupted.
	#[cfg(feature = "try-runtime")]
	pub fn image_count<T: Config>() -> Option<u32> {
		let images = v0::PreimageFor::<T>::iter_values().count() as u32;
		let status = v0::StatusFor::<T>::iter_values().count() as u32;

		if images == status {
			Some(images)
		} else {
			None
		}
	}
}

pub mod v1 {
	use super::*;

	/// Migration for moving preimage from V0 to V1 storage.
	///
	/// Note: This needs to be run with the same hashing algorithm as before
	/// since it is not re-hashing the preimages.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0, "can only upgrade from version 0");

			let images = v0::image_count::<T>().expect("v0 storage corrupted");
			log::info!(target: TARGET, "Migrating {} images", &images);
			Ok((images as u32).encode())
		}

		fn on_runtime_upgrade() -> Weight {
			let mut weight = T::DbWeight::get().reads(1);
			if StorageVersion::get::<Pallet<T>>() != 0 {
				log::warn!(
					target: TARGET,
					"skipping MovePreimagesIntoBuckets: executed on wrong storage version.\
				Expected version 0"
				);
				return weight
			}

			let status = v0::StatusFor::<T>::drain().collect::<Vec<_>>();
			weight.saturating_accrue(T::DbWeight::get().reads(status.len() as u64));

			let preimages = v0::PreimageFor::<T>::drain().collect::<BTreeMap<_, _>>();
			weight.saturating_accrue(T::DbWeight::get().reads(preimages.len() as u64));

			for (hash, status) in status.into_iter() {
				let preimage = if let Some(preimage) = preimages.get(&hash) {
					preimage
				} else {
					log::error!(target: TARGET, "preimage not found for hash {:?}", &hash);
					continue
				};
				let len = preimage.len() as u32;
				if len > MAX_SIZE {
					log::error!(
						target: TARGET,
						"preimage too large for hash {:?}, len: {}",
						&hash,
						len
					);
					continue
				}

				let status = match status {
					v0::RequestStatus::Unrequested(deposit) => match deposit {
						Some(deposit) => RequestStatus::Unrequested { deposit, len },
						// `None` depositor becomes system-requested.
						None =>
							RequestStatus::Requested { deposit: None, count: 1, len: Some(len) },
					},
					v0::RequestStatus::Requested(count) if count == 0 => {
						log::error!(target: TARGET, "preimage has counter of zero: {:?}", hash);
						continue
					},
					v0::RequestStatus::Requested(count) =>
						RequestStatus::Requested { deposit: None, count, len: Some(len) },
				};
				log::trace!(target: TARGET, "Moving preimage {:?} with len {}", hash, len);

				crate::StatusFor::<T>::insert(hash, status);
				crate::PreimageFor::<T>::insert(&(hash, len), preimage);

				weight.saturating_accrue(T::DbWeight::get().writes(2));
			}
			StorageVersion::new(1).put::<Pallet<T>>();

			weight.saturating_add(T::DbWeight::get().writes(1))
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(state: Vec<u8>) -> Result<(), &'static str> {
			let old_images: u32 =
				Decode::decode(&mut &state[..]).expect("pre_upgrade provides a valid state; qed");
			let new_images = image_count::<T>().expect("V1 storage corrupted");

			if new_images != old_images {
				log::error!(
					target: TARGET,
					"migrated {} images, expected {}",
					new_images,
					old_images
				);
			}
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1, "must upgrade");
			Ok(())
		}
	}

	/// Returns the number of images or `None` if the storage is corrupted.
	#[cfg(feature = "try-runtime")]
	pub fn image_count<T: Config>() -> Option<u32> {
		// Use iter_values() to ensure that the values are decodable.
		let images = crate::PreimageFor::<T>::iter_values().count() as u32;
		let status = crate::StatusFor::<T>::iter_values().count() as u32;

		if images == status {
			Some(images)
		} else {
			None
		}
	}
}

#[cfg(test)]
#[cfg(feature = "try-runtime")]
mod test {
	use super::*;
	use crate::mock::{Test as T, *};

	use frame_support::bounded_vec;

	#[test]
	fn migration_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0);
			// Insert some preimages into the v0 storage:

			// Case 1: Unrequested without deposit
			let (p, h) = preimage::<T>(128);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Unrequested(None));
			// Case 2: Unrequested with deposit
			let (p, h) = preimage::<T>(1024);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Unrequested(Some((1, 1))));
			// Case 3: Requested by 0 (invalid)
			let (p, h) = preimage::<T>(8192);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Requested(0));
			// Case 4: Requested by 10
			let (p, h) = preimage::<T>(65536);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Requested(10));

			assert_eq!(v0::image_count::<T>(), Some(4));
			assert_eq!(v1::image_count::<T>(), None, "V1 storage should be corrupted");

			let state = v1::Migration::<T>::pre_upgrade().unwrap();
			let _w = v1::Migration::<T>::on_runtime_upgrade();
			v1::Migration::<T>::post_upgrade(state).unwrap();

			// V0 and V1 share the same prefix, so `iter_values` still counts the same.
			assert_eq!(v0::image_count::<T>(), Some(3));
			assert_eq!(v1::image_count::<T>(), Some(3)); // One gets skipped therefore 3.
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1);

			// Case 1: Unrequested without deposit becomes system-requested
			let (p, h) = preimage::<T>(128);
			assert_eq!(crate::PreimageFor::<T>::get(&(h, 128)), Some(p));
			assert_eq!(
				crate::StatusFor::<T>::get(h),
				Some(RequestStatus::Requested { deposit: None, count: 1, len: Some(128) })
			);
			// Case 2: Unrequested with deposit becomes unrequested
			let (p, h) = preimage::<T>(1024);
			assert_eq!(crate::PreimageFor::<T>::get(&(h, 1024)), Some(p));
			assert_eq!(
				crate::StatusFor::<T>::get(h),
				Some(RequestStatus::Unrequested { deposit: (1, 1), len: 1024 })
			);
			// Case 3: Requested by 0 should be skipped
			let (_, h) = preimage::<T>(8192);
			assert_eq!(crate::PreimageFor::<T>::get(&(h, 8192)), None);
			assert_eq!(crate::StatusFor::<T>::get(h), None);
			// Case 4: Requested by 10 becomes requested by 10
			let (p, h) = preimage::<T>(65536);
			assert_eq!(crate::PreimageFor::<T>::get(&(h, 65536)), Some(p));
			assert_eq!(
				crate::StatusFor::<T>::get(h),
				Some(RequestStatus::Requested { deposit: None, count: 10, len: Some(65536) })
			);
		});
	}

	/// Returns a preimage with a given size and its hash.
	fn preimage<T: Config>(
		len: usize,
	) -> (BoundedVec<u8, ConstU32<MAX_SIZE>>, <T as frame_system::Config>::Hash) {
		let p = bounded_vec![1; len];
		let h = <T as frame_system::Config>::Hashing::hash_of(&p);
		(p, h)
	}
}
