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

//! Storage migrations for the im-online pallet.

use super::*;
use frame_support::{storage_alias, traits::OnRuntimeUpgrade};

#[cfg(feature = "try-runtime")]
use frame_support::ensure;
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

/// The log target.
const TARGET: &str = "runtime::im-online::migration::v1";

/// The original data layout of the im-online pallet (`ReceivedHeartbeats` storage item).
mod v0 {
	use super::*;
	use frame_support::traits::WrapperOpaque;

	#[derive(Encode, Decode, Default)]
	pub(super) struct BoundedOpaqueNetworkState {
		/// PeerId of the local node in SCALE encoded.
		pub peer_id: Vec<u8>,
		/// List of addresses the node knows it can be reached as.
		pub external_addresses: Vec<Vec<u8>>,
	}

	#[storage_alias]
	pub(super) type ReceivedHeartbeats<T: Config> = StorageDoubleMap<
		Pallet<T>,
		Twox64Concat,
		SessionIndex,
		Twox64Concat,
		AuthIndex,
		WrapperOpaque<BoundedOpaqueNetworkState>,
	>;
}

pub mod v1 {
	use super::*;

	/// Simple migration that replaces `ReceivedHeartbeats` values with `true`.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			let count = v0::ReceivedHeartbeats::<T>::iter().count();
			log::info!(target: TARGET, "Migrating {} received heartbeats", count);

			Ok((count as u32).encode())
		}

		fn on_runtime_upgrade() -> Weight {
			let mut weight = T::DbWeight::get().reads(1);
			if StorageVersion::get::<Pallet<T>>() != 0 {
				log::warn!(
					target: TARGET,
					"Skipping migration because current storage version is not 0"
				);
				return weight
			}

			let heartbeats = v0::ReceivedHeartbeats::<T>::drain().collect::<Vec<_>>();

			weight.saturating_accrue(T::DbWeight::get().reads(heartbeats.len() as u64));
			weight.saturating_accrue(T::DbWeight::get().writes(heartbeats.len() as u64));

			for (session_index, auth_index, _) in heartbeats {
				log::trace!(
					target: TARGET,
					"Migrated received heartbeat for {:?}...",
					(session_index, auth_index)
				);
				crate::ReceivedHeartbeats::<T>::insert(session_index, auth_index, true);
			}

			StorageVersion::new(1).put::<Pallet<T>>();
			weight.saturating_add(T::DbWeight::get().writes(1))
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(state: Vec<u8>) -> DispatchResult {
			let old_received_heartbeats: u32 =
				Decode::decode(&mut &state[..]).expect("pre_upgrade provides a valid state; qed");
			let new_received_heartbeats = crate::ReceivedHeartbeats::<T>::iter().count();

			if new_received_heartbeats != old_received_heartbeats as usize {
				log::error!(
					target: TARGET,
					"migrated {} received heartbeats, expected {}",
					new_received_heartbeats,
					old_received_heartbeats
				);
			}
			ensure!(StorageVersion::get::<Pallet<T>>() >= 1, "must upgrade");

			Ok(())
		}
	}
}

#[cfg(all(feature = "try-runtime", test))]
mod test {
	use super::*;
	use crate::mock::{new_test_ext, Runtime as T};
	use frame_support::traits::WrapperOpaque;

	#[test]
	fn migration_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0);

			// Insert some received heartbeats into the v0 storage:
			let current_session = <T as pallet::Config>::ValidatorSet::session_index();
			v0::ReceivedHeartbeats::<T>::insert(
				&current_session,
				0,
				WrapperOpaque(v0::BoundedOpaqueNetworkState::default()),
			);
			v0::ReceivedHeartbeats::<T>::insert(
				&current_session,
				1,
				WrapperOpaque(v0::BoundedOpaqueNetworkState::default()),
			);

			// Check that the v0 storage is populated
			assert_eq!(v0::ReceivedHeartbeats::<T>::iter().count(), 2);
			assert_eq!(crate::ReceivedHeartbeats::<T>::iter().count(), 0, "V1 storage corrupted");

			// Perform the migration
			let state = v1::Migration::<T>::pre_upgrade().unwrap();
			let _w = v1::Migration::<T>::on_runtime_upgrade();
			v1::Migration::<T>::post_upgrade(state).unwrap();

			// Check that the v1 storage is populated and v0 storage is empty
			assert_eq!(v0::ReceivedHeartbeats::<T>::iter().count(), 0);
			assert_eq!(crate::ReceivedHeartbeats::<T>::iter().count(), 2);
			assert!(crate::ReceivedHeartbeats::<T>::contains_key(&current_session, 0));
			assert_eq!(Some(true), crate::ReceivedHeartbeats::<T>::get(&current_session, 1));

			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1);
		});
	}
}
