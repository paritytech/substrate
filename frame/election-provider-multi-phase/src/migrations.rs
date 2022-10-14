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

pub mod v1 {
	use frame_support::{
		storage::unhashed,
		traits::{Defensive, GetStorageVersion, OnRuntimeUpgrade},
		BoundedVec,
	};
	use sp_std::collections::btree_map::BTreeMap;

	use crate::*;
	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 1 && onchain == 0 {
				if SignedSubmissionIndices::<T>::exists() {
					// This needs to be tested at a both a block height where this value exists, and
					// when it doesn't.
					let now = frame_system::Pallet::<T>::block_number();
					let map = unhashed::get::<BTreeMap<ElectionScore, u32>>(
						&SignedSubmissionIndices::<T>::hashed_key(),
					)
					.defensive_unwrap_or_default();
					let vector = map
						.into_iter()
						.map(|(score, index)| (score, now, index))
						.collect::<Vec<_>>();

					log!(
						debug,
						"{:?} SignedSubmissionIndices read from storage (max: {:?})",
						vector.len(),
						T::SignedMaxSubmissions::get()
					);

					// defensive-only, assuming a constant `SignedMaxSubmissions`.
					let bounded = BoundedVec::<_, _>::truncate_from(vector);
					SignedSubmissionIndices::<T>::put(bounded);

					log!(info, "SignedSubmissionIndices existed and got migrated");
				} else {
					log!(info, "SignedSubmissionIndices did NOT exist.");
				}

				current.put::<Pallet<T>>();
				T::DbWeight::get().reads_writes(2, 1)
			} else {
				log!(info, "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}
	}
}
