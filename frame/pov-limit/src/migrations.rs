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

// Migrations for Pov-Limit Pallet

use super::*;
use frame_support::{pallet_prelude::StorageVersion, traits::OnRuntimeUpgrade};
use sp_std::vec::Vec;

pub mod v1 {
	use super::*;

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let mut weight = T::DbWeight::get().reads(1);

			let storage_version = StorageVersion::get::<Pallet<T>>();

			if storage_version > 0 {
				log::info!("The pallet is alredy migrated to V1.");
				return weight
			}

			for i in 0..5000 {
				TrashData::<T>::insert(&i, i);
				weight = weight.saturating_add(T::DbWeight::get().writes(1))
			}

			StorageVersion::new(1).put::<Pallet<T>>();

			weight
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();
			ensure!(onchain == 1, "new version must be set.");
			ensure!(
				TrashData::<T>::iter().count() == 5000,
				"not enogh data was inserted into `TrashData`."
			);
			Ok(())
		}
	}
}
