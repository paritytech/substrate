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
	pallet_prelude::StorageVersion, storage_alias, traits::OnRuntimeUpgrade, BoundedVec,
};
use sp_core::H256;

/// The log target.
const TARGET: &'static str = "runtime::democracy::migration::v1";

/// The original data layout of the democracy pallet without a specific version number.
mod v0 {
	use super::*;

	#[storage_alias]
	pub type PublicProps<T: Config> = StorageValue<
		Pallet<T>,
		Vec<(PropIndex, <T as frame_system::Config>::Hash, <T as frame_system::Config>::AccountId)>,
	>;

	#[storage_alias]
	pub type NextExternal<T: Config> =
		StorageValue<Pallet<T>, (<T as frame_system::Config>::Hash, VoteThreshold)>;
}

pub mod v1 {
	use super::*;

	/// Migration for translating bare `Hash`es into `Bounded<Call>`s.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config + frame_system::Config<Hash = H256>> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0, "can only upgrade from version 0");
		}

		#[allow(deprecated)]
		fn on_runtime_upgrade() -> Weight {
			let mut weight = T::DbWeight::get().reads(1);
			if StorageVersion::get::<Pallet<T>>() != 0 {
				log::warn!(
					target: TARGET,
					"skipping on_runtime_upgrade: executed on wrong storage version.\
				Expected version 0"
				);
				return weight
			}

			ReferendumInfoOf::<T>::translate(
				|_key, old: ReferendumInfo<T::BlockNumber, T::Hash, BalanceOf<T>>| {
					Some(match old {
						ReferendumInfo::Ongoing(status) =>
							ReferendumInfo::Ongoing(ReferendumStatus {
								end: status.end,
								proposal: Bounded::from_legacy_hash(status.proposal),
								threshold: status.threshold,
								delay: status.delay,
								tally: status.tally,
							}),
						ReferendumInfo::Finished { approved, end } =>
							ReferendumInfo::Finished { approved, end },
					})
				},
			);

			let props = v0::PublicProps::<T>::take()
				.unwrap_or_default()
				.into_iter()
				.map(|(i, hash, a)| (i, Bounded::from_legacy_hash(hash), a))
				.take(T::MaxProposals::get() as usize)
				.collect::<Vec<_>>();
			let bounded = BoundedVec::<_, T::MaxProposals>::truncate_from(props);
			PublicProps::<T>::put(bounded);

			if let Some((hash, threshold)) = v0::NextExternal::<T>::take() {
				NextExternal::<T>::put((Bounded::from_legacy_hash(hash), threshold));
			}

			StorageVersion::new(1).put::<Pallet<T>>();

			weight = weight.saturating_add(T::DbWeight::get().reads_writes(0, 2));
			weight
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 1, "must upgrade");
			Ok(())
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
		new_test_ext().execute_with(|| {});
	}
}
