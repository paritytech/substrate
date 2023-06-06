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
const TARGET: &'static str = "runtime::im-online::migration::v1";

/// The original data layout of the im-online pallet without a specific version number.
mod v0 {
	use super::*;
	use frame_support::traits::WrapperOpaque;

	/// A type that is the same as `OpaqueNetworkState` but with [`Vec`] replaced with
	/// [`WeakBoundedVec<Limit>`] where Limit is the respective size limit
	/// `PeerIdEncodingLimit` represents the size limit of the encoding of `PeerId`
	/// `MultiAddrEncodingLimit` represents the size limit of the encoding of `MultiAddr`
	/// `AddressesLimit` represents the size limit of the vector of peers connected
	#[derive(Clone, Eq, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo)]
	pub struct BoundedOpaqueNetworkState<
		PeerIdEncodingLimit,
		MultiAddrEncodingLimit,
		AddressesLimit,
	> where
		PeerIdEncodingLimit: Get<u32>,
		MultiAddrEncodingLimit: Get<u32>,
		AddressesLimit: Get<u32>,
	{
		/// PeerId of the local node in SCALE encoded.
		pub peer_id: WeakBoundedVec<u8, PeerIdEncodingLimit>,
		/// List of addresses the node knows it can be reached as.
		pub external_addresses:
			WeakBoundedVec<WeakBoundedVec<u8, MultiAddrEncodingLimit>, AddressesLimit>,
	}

	#[storage_alias]
	pub(crate) type HeartbeatAfter<T: Config> = StorageValue<Pallet<T>, T::BlockNumber, ValueQuery>;

	#[storage_alias]
	pub(crate) type Keys<T: Config> =
		StorageValue<Pallet<T>, WeakBoundedVec<T::AuthorityId, T::MaxKeys>, ValueQuery>;

	#[storage_alias]
	pub(crate) type ReceivedHeartbeats<T: Config> = StorageDoubleMap<
		Pallet<T>,
		Twox64Concat,
		SessionIndex,
		Twox64Concat,
		AuthIndex,
		WrapperOpaque<BoundedOpaqueNetworkState<u32, u32, T::MaxPeerInHeartbeats>>,
	>;

	#[storage_alias]
	pub(crate) type AuthoredBlocks<T: pallet::Config> = StorageDoubleMap<
		Pallet<T>,
		Twox64Concat,
		SessionIndex,
		Twox64Concat,
		ValidatorId<T>,
		u32,
		ValueQuery,
	>;
}

pub mod v1 {
	use super::*;

	/// Migration for moving im-online from V0 to V1 storage.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 0, "can only upgrade from version 0");

			log::info!(
				target: TARGET,
				"Migrating {} received heartbeats",
				v0::ReceivedHeartbeats::<T>::iter().count()
			);

			Ok(())
		}

		fn on_runtime_upgrade() -> Weight {
			ReceivedHeartbeats::<T>::translate::<_, _>(
				|k: T::SessionIndex, T::AccountId, state: _| {
					log::info!(target: TARGET, "Migrated received heartbeat for {:?}...", k);
					Some(())
				},
			);

			StorageVersion::new(1).put::<Pallet<T>>();

			let count = ReceivedHeartbeats::<T>::iter().count();
			T::DbWeight::get().reads_writes(count as Weight + 1, count as Weight + 1)
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(state: Vec<u8>) -> DispatchResult {
			ensure!(StorageVersion::get::<Pallet<T>>() == 1, "must upgrade");

			log::info!(
				target: TARGET,
				"Migrated {} received heartbeats",
				crate::ReceivedHeartbeats::<T>::iter().count()
			);

			Ok(())
		}
	}
}
