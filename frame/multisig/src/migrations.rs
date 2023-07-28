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

// Migrations for Multisig Pallet

use super::*;
use frame_support::{
	dispatch::GetStorageVersion,
	traits::{OnRuntimeUpgrade, WrapperKeepOpaque},
	Identity,
};

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

pub mod v1 {
	use super::*;

	type OpaqueCall<T> = WrapperKeepOpaque<<T as Config>::RuntimeCall>;

	#[frame_support::storage_alias]
	type Calls<T: Config> = StorageMap<
		Pallet<T>,
		Identity,
		[u8; 32],
		(OpaqueCall<T>, <T as frame_system::Config>::AccountId, BalanceOf<T>),
	>;

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain < 1, "this migration can be deleted");

			log!(info, "Number of calls to refund and delete: {}", Calls::<T>::iter().count());

			Ok(Vec::new())
		}

		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			if onchain > 0 {
				log!(info, "MigrateToV1 should be removed");
				return T::DbWeight::get().reads(1)
			}

			Calls::<T>::drain().for_each(|(_call_hash, (_data, caller, deposit))| {
				T::Currency::unreserve(&caller, deposit);
			});

			current.put::<Pallet<T>>();

			<T as frame_system::Config>::BlockWeights::get().max_block
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_state: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
			let onchain = Pallet::<T>::on_chain_storage_version();
			ensure!(onchain < 2, "this migration needs to be removed");
			ensure!(onchain == 1, "this migration needs to be run");
			ensure!(
				Calls::<T>::iter().count() == 0,
				"there are some dangling calls that need to be destroyed and refunded"
			);
			Ok(())
		}
	}
}
