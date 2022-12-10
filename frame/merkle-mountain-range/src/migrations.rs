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
		pallet_prelude::*,
		traits::{GetStorageVersion, OnRuntimeUpgrade},
	};

	use crate::*;
	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log::info!(
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 1 && onchain == 0 {

				current.put::<Pallet<T>>();
				// TODO: adjust DbWeight
				T::DbWeight::get().reads_writes(2, 1)
			} else {
				log::info!("Migration did not execute. This probably should be removed");
				// TODO: adjust DbWeight (but reads -> 1 should remain correct)
				T::DbWeight::get().reads(1)
			}
		}
	}
}
