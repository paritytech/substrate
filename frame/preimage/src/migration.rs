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

//! Storage migrations for the preimage pallet.

use super::*;
#[cfg(feature = "try-runtime")]
use frame_support::traits::OnRuntimeUpgradeHelpersExt;
use frame_support::{
	storage_alias,
	traits::{ConstU32, OnRuntimeUpgrade},
};

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

	#[cfg(feature = "try-runtime")]
	pub fn image_count<T: Config>() -> Option<u32> {
		// Use iter_values since otherwise it would indicate that a value cannot be decoded,
		// possibly due to `MAX_SIZE` being too small.
		let images = v0::PreimageFor::<T>::iter_values().count() as u32;
		let status = v0::StatusFor::<T>::iter().count() as u32;

		if images == status && images > 0 {
			Some(images)
		} else {
			None
		}
	}
}

pub mod v1 {
	use super::*;

	/// Migration for moving preimages from a single map into into specific buckets.
	///
	/// Note: This needs to be run with the same hashing algorithm as before
	/// since it is not re-hashing the preimages.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0, "can only upgrade from version 0");

			let images = v0::image_count::<T>().expect("v0 storage corrupted");
			log::info!(target: TARGET, "Migrating {} images", &images);
			Self::set_temp_storage(images, "old_images");
			Ok(())
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
			for (hash, status) in status.into_iter() {
				let preimage =
					v0::PreimageFor::<T>::take(hash).expect("storage corrupt: no image for status");
				let len = preimage.len() as u32;
				assert!(len <= MAX_SIZE, "Preimage larger than MAX_SIZE");

				let status = match status {
					v0::RequestStatus::Unrequested(deposit) => match deposit {
						Some(deposit) => RequestStatus::Unrequested { deposit, len },
						// `None` depositor becomes system-requested.
						None =>
							RequestStatus::Requested { deposit: None, count: 1, len: Some(len) },
					},
					v0::RequestStatus::Requested(count) =>
						RequestStatus::Requested { deposit: None, count, len: Some(len) },
				};
				log::trace!(target: TARGET, "Moving preimage {:?} with len {}", hash, len);

				Pallet::<T>::insert(&hash, preimage.into_inner().into())
					.expect("Must insert preimage");
				StatusFor::<T>::insert(hash, status);

				weight = weight.saturating_add(T::DbWeight::get().reads_writes(3, 2));
			}
			// Note: No `v0::StatusFor::<T>::clear(…)` hereu32::MAX, None
			// since v0 and v1 use the same key-space.
			let rem = v0::PreimageFor::<T>::clear(u32::MAX, None);
			assert!(rem.maybe_cursor.is_none());

			StorageVersion::new(1).put::<Pallet<T>>();

			weight = weight.saturating_add(T::DbWeight::get().reads_writes(0, 2));
			weight
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			let old_images = Self::get_temp_storage::<u32>("old_images").unwrap();
			let new_images = image_count::<T>();

			assert!(new_images == old_images);
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1, "must upgrade");
			Ok(())
		}
	}

	#[cfg(feature = "try-runtime")]
	pub fn image_count<T: Config>() -> u32 {
		// Use iter_values() to ensure that the values are decodable.
		let images = crate::PreimageFor::<T>::iter_values().count() as u32;
		let status = crate::StatusFor::<T>::iter_values().count() as u32;
		assert_eq!(images, status, "V1 storage corrupt: {} images vs {} status", images, status);
		images
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

			// Case 3: Requested by 0
			let (p, h) = preimage::<T>(8192);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Requested(0));
			// Case 4: Requested by 10
			let (p, h) = preimage::<T>(65536);
			v0::PreimageFor::<T>::insert(h, p);
			v0::StatusFor::<T>::insert(h, v0::RequestStatus::Requested(10));

			assert_eq!(v0::image_count::<T>(), Some(4));
			assert_eq!(v1::image_count::<T>(), 0);

			v1::Migration::<T>::pre_upgrade().unwrap();
			let _w = v1::Migration::<T>::on_runtime_upgrade();
			v1::Migration::<T>::post_upgrade().unwrap();

			assert_eq!(v0::image_count::<T>(), None, "v0 storage should be corrupted now");
			assert_eq!(v1::image_count::<T>(), 4);
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1);
		});
	}

	fn preimage<T: Config>(
		len: usize,
	) -> (BoundedVec<u8, ConstU32<MAX_SIZE>>, <T as frame_system::Config>::Hash) {
		let p = bounded_vec![1; len];
		let h = <T as frame_system::Config>::Hashing::hash_of(&p);
		(p, h)
	}
}
