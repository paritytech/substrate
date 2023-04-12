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

pub mod v1 {
	use crate::{types::BalanceOf, *};
	use frame_support::{
		storage::unhashed,
		traits::{Defensive, Get, GetStorageVersion, OnRuntimeUpgrade},
		weights::Weight,
	};
	use sp_staking::EraIndex;
	use sp_std::prelude::*;

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
				// update the version nonetheless.
				current.put::<Pallet<T>>();

				// if a head exists, then we put them back into the queue.
				if Head::<T>::exists() {
					if let Some((stash, _, deposit)) =
						unhashed::take::<(T::AccountId, Vec<EraIndex>, BalanceOf<T>)>(
							&Head::<T>::hashed_key(),
						)
						.defensive()
					{
						Queue::<T>::insert(stash, deposit);
					} else {
						// not much we can do here -- head is already deleted.
					}
					T::DbWeight::get().reads_writes(2, 3)
				} else {
					T::DbWeight::get().reads(2)
				}
			} else {
				log!(info, "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			assert_eq!(Pallet::<T>::on_chain_storage_version(), 0);
			Ok(Default::default())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_: Vec<u8>) -> Result<(), &'static str> {
			assert_eq!(Pallet::<T>::on_chain_storage_version(), 1);
			Ok(())
		}
	}
}
