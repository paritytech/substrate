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
use frame_support::{pallet_prelude::*, storage_alias, traits::OnRuntimeUpgrade, BoundedVec};
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
		ValueQuery,
	>;

	#[storage_alias]
	pub type NextExternal<T: Config> =
		StorageValue<Pallet<T>, (<T as frame_system::Config>::Hash, VoteThreshold)>;

	#[cfg(feature = "try-runtime")]
	#[storage_alias]
	pub type ReferendumInfoOf<T: Config> = StorageMap<
		Pallet<T>,
		frame_support::Twox64Concat,
		ReferendumIndex,
		ReferendumInfo<
			<T as frame_system::Config>::BlockNumber,
			<T as frame_system::Config>::Hash,
			BalanceOf<T>,
		>,
	>;
}

pub mod v1 {
	use super::*;

	/// Migration for translating bare `Hash`es into `Bounded<Call>`s.
	pub struct Migration<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config + frame_system::Config<Hash = H256>> OnRuntimeUpgrade for Migration<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 0, "can only upgrade from version 0");

			let props_count = v0::PublicProps::<T>::get().len();
			log::info!(target: TARGET, "{} public proposals will be migrated.", props_count,);
			ensure!(props_count <= T::MaxProposals::get() as usize, Error::<T>::TooMany);

			let referenda_count = v0::ReferendumInfoOf::<T>::iter().count();
			log::info!(target: TARGET, "{} referenda will be migrated.", referenda_count);

			Ok((props_count as u32, referenda_count as u32).encode())
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
				|index, old: ReferendumInfo<T::BlockNumber, T::Hash, BalanceOf<T>>| {
					weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
					log::info!(target: TARGET, "migrating referendum #{:?}", &index);
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
				.into_iter()
				.map(|(i, hash, a)| (i, Bounded::from_legacy_hash(hash), a))
				.collect::<Vec<_>>();
			let bounded = BoundedVec::<_, T::MaxProposals>::truncate_from(props.clone());
			PublicProps::<T>::put(bounded);
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));

			if props.len() as u32 > T::MaxProposals::get() {
				log::error!(
					target: TARGET,
					"truncated {} public proposals to {}; continuing",
					props.len(),
					T::MaxProposals::get()
				);
			}

			if let Some((hash, threshold)) = v0::NextExternal::<T>::take() {
				log::info!(target: TARGET, "migrating next external proposal");
				NextExternal::<T>::put((Bounded::from_legacy_hash(hash), threshold));
			}

			StorageVersion::new(1).put::<Pallet<T>>();

			weight.saturating_add(T::DbWeight::get().reads_writes(1, 2))
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(state: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 1, "must upgrade");

			let (old_props_count, old_ref_count): (u32, u32) =
				Decode::decode(&mut &state[..]).expect("pre_upgrade provides a valid state; qed");
			let new_props_count = crate::PublicProps::<T>::get().len() as u32;
			ensure!(new_props_count == old_props_count, "must migrate all public proposals");
			let new_ref_count = crate::ReferendumInfoOf::<T>::iter().count() as u32;
			ensure!(new_ref_count == old_ref_count, "must migrate all referenda");

			log::info!(
				target: TARGET,
				"{} public proposals migrated, {} referenda migrated",
				new_props_count,
				new_ref_count,
			);
			Ok(())
		}
	}
}

#[cfg(test)]
#[cfg(feature = "try-runtime")]
mod test {
	use super::*;
	use crate::{
		tests::{Test as T, *},
		types::*,
	};
	use frame_support::bounded_vec;

	#[allow(deprecated)]
	#[test]
	fn migration_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 0);
			// Insert some values into the v0 storage:

			// Case 1: Ongoing referendum
			let hash = H256::repeat_byte(1);
			let status = ReferendumStatus {
				end: 1u32.into(),
				proposal: hash.clone(),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 1u32.into(),
				tally: Tally { ayes: 1u32.into(), nays: 1u32.into(), turnout: 1u32.into() },
			};
			v0::ReferendumInfoOf::<T>::insert(1u32, ReferendumInfo::Ongoing(status));

			// Case 2: Finished referendum
			v0::ReferendumInfoOf::<T>::insert(
				2u32,
				ReferendumInfo::Finished { approved: true, end: 123u32.into() },
			);

			// Case 3: Public proposals
			let hash2 = H256::repeat_byte(2);
			v0::PublicProps::<T>::put(vec![
				(3u32, hash.clone(), 123u64),
				(4u32, hash2.clone(), 123u64),
			]);

			// Case 4: Next external
			v0::NextExternal::<T>::put((hash.clone(), VoteThreshold::SuperMajorityApprove));

			// Migrate.
			let state = v1::Migration::<T>::pre_upgrade().unwrap();
			let _weight = v1::Migration::<T>::on_runtime_upgrade();
			v1::Migration::<T>::post_upgrade(state).unwrap();
			// Check that all values got migrated.

			// Case 1: Ongoing referendum
			assert_eq!(
				ReferendumInfoOf::<T>::get(1u32),
				Some(ReferendumInfo::Ongoing(ReferendumStatus {
					end: 1u32.into(),
					proposal: Bounded::from_legacy_hash(hash),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 1u32.into(),
					tally: Tally { ayes: 1u32.into(), nays: 1u32.into(), turnout: 1u32.into() },
				}))
			);
			// Case 2: Finished referendum
			assert_eq!(
				ReferendumInfoOf::<T>::get(2u32),
				Some(ReferendumInfo::Finished { approved: true, end: 123u32.into() })
			);
			// Case 3: Public proposals
			let props: BoundedVec<_, <Test as Config>::MaxProposals> = bounded_vec![
				(3u32, Bounded::from_legacy_hash(hash), 123u64),
				(4u32, Bounded::from_legacy_hash(hash2), 123u64)
			];
			assert_eq!(PublicProps::<T>::get(), props);
			// Case 4: Next external
			assert_eq!(
				NextExternal::<T>::get(),
				Some((Bounded::from_legacy_hash(hash), VoteThreshold::SuperMajorityApprove))
			);
		});
	}
}
