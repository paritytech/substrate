// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Migrations for the scheduler pallet.

use super::*;
use frame_support::traits::OnRuntimeUpgrade;
#[cfg(feature = "try-runtime")]
use frame_support::traits::OnRuntimeUpgradeHelpersExt;

/// The log target.
const TARGET: &'static str = "runtime::scheduler::migration";

pub mod v3 {
	use super::*;

	/// Migrate the scheduler pallet from V3 to V4.
	pub struct MigrateToV4<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config<Hash = PreimageHash>> OnRuntimeUpgrade for MigrateToV4<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 3, "Can only upgrade from version 3");

			let agenda_count = Agenda::<T>::iter_keys().count() as u32;
			log::info!(target: TARGET, "Will migrate {} agendas...", agenda_count);
			Self::set_temp_storage(agenda_count, "old_agenda_count");

			// Check that no agenda overflows `MaxScheduledPerBlock`.
			let max_scheduled_per_block = T::MaxScheduledPerBlock::get();
			for (block_number, agenda) in Agenda::<T>::iter() {
				if agenda.len() > max_scheduled_per_block as usize {
					log::error!(
						target: TARGET,
						"Would truncate agenda of block {:?} from {} items to {} items - abort.",
						block_number,
						agenda.len(),
						max_scheduled_per_block,
					);
					return Err("Agenda overflow")
				}
			}

			Ok(())
		}

		fn on_runtime_upgrade() -> Weight {
			let version = StorageVersion::get::<Pallet<T>>();
			if version != 3 {
				log::warn!(
					target: TARGET,
					"skipping v3 to v4 migration: executed on wrong storage version.\
				Expected version 3, found {:?}",
					version,
				);
				return T::DbWeight::get().reads(1)
			}

			crate::Pallet::<T>::migrate_v3_to_v4()
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			assert_eq!(StorageVersion::get::<Pallet<T>>(), 4, "Must upgrade");

			let new_agenda_count = Agenda::<T>::iter_keys().count() as u32;
			let old_agenda_count: u32 = Self::get_temp_storage("old_agenda_count").unwrap();
			assert_eq!(new_agenda_count, old_agenda_count, "Must migrate all agendas");

			// Check that all values decode correctly.
			for k in Agenda::<T>::iter_keys() {
				assert!(Agenda::<T>::try_get(k).is_ok(), "Cannot decode Agenda");
			}
			Ok(())
		}
	}
}

#[cfg(test)]
#[cfg(feature = "try-runtime")]
mod test {
	use super::*;
	use crate::mock::*;
	use frame_support::Hashable;
	use substrate_test_utils::assert_eq_uvec;

	#[test]
	#[allow(deprecated)]
	fn migration_v3_to_v4_works() {
		new_test_ext().execute_with(|| {
			// Assume that we are at V3.
			StorageVersion::new(3).put::<Scheduler>();

			// Call that will be bounded to a `Lookup`.
			let large_call =
				RuntimeCall::System(frame_system::Call::remark { remark: vec![0; 1024] });
			// Call that can be inlined.
			let small_call =
				RuntimeCall::System(frame_system::Call::remark { remark: vec![0; 10] });
			// Call that is already hashed adn can will be converted to `Legacy`.
			let hashed_call =
				RuntimeCall::System(frame_system::Call::remark { remark: vec![0; 2048] });
			let bound_hashed_call = Preimage::bound(hashed_call.clone()).unwrap();
			assert!(bound_hashed_call.lookup_needed());

			for i in 0..2u64 {
				let k = i.twox_64_concat();
				let old = vec![
					Some(ScheduledV3Of::<Test> {
						maybe_id: None,
						priority: i as u8 + 10,
						call: small_call.clone().into(),
						maybe_periodic: None, // 1
						origin: root(),
						_phantom: PhantomData::<u64>::default(),
					}),
					None,
					Some(ScheduledV3Of::<Test> {
						maybe_id: Some([i as u8; 32]),
						priority: 123,
						call: large_call.clone().into(),
						maybe_periodic: Some((4u64, 20)),
						origin: signed(i),
						_phantom: PhantomData::<u64>::default(),
					}),
					Some(ScheduledV3Of::<Test> {
						maybe_id: Some([(255 - i as u8); 32]),
						priority: 123,
						call: MaybeHashed::Hash(bound_hashed_call.hash()),
						maybe_periodic: Some((8u64, 10)),
						origin: signed(i),
						_phantom: PhantomData::<u64>::default(),
					}),
				];
				frame_support::migration::put_storage_value(b"Scheduler", b"Agenda", &k, old);
			}

			v3::MigrateToV4::<Test>::pre_upgrade().unwrap();
			let _w = v3::MigrateToV4::<Test>::on_runtime_upgrade();
			v3::MigrateToV4::<Test>::post_upgrade().unwrap();

			let mut x = Agenda::<Test>::iter().map(|x| (x.0, x.1.into_inner())).collect::<Vec<_>>();
			x.sort_by_key(|x| x.0);

			let bound_large_call = Preimage::bound(large_call).unwrap();
			assert!(bound_large_call.lookup_needed());
			let bound_small_call = Preimage::bound(small_call).unwrap();
			assert!(!bound_small_call.lookup_needed());

			let expected = vec![
				(
					0,
					vec![
						Some(ScheduledOf::<Test> {
							maybe_id: None,
							priority: 10,
							call: bound_small_call.clone(),
							maybe_periodic: None,
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
						Some(ScheduledOf::<Test> {
							maybe_id: Some(blake2_256(&[0u8; 32])),
							priority: 123,
							call: bound_large_call.clone(),
							maybe_periodic: Some((4u64, 20)),
							origin: signed(0),
							_phantom: PhantomData::<u64>::default(),
						}),
						Some(ScheduledOf::<Test> {
							maybe_id: Some(blake2_256(&[255u8; 32])),
							priority: 123,
							call: Bounded::from_legacy_hash(bound_hashed_call.hash()),
							maybe_periodic: Some((8u64, 10)),
							origin: signed(0),
							_phantom: PhantomData::<u64>::default(),
						}),
					],
				),
				(
					1,
					vec![
						Some(ScheduledOf::<Test> {
							maybe_id: None,
							priority: 11,
							call: bound_small_call.clone(),
							maybe_periodic: None,
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
						Some(ScheduledOf::<Test> {
							maybe_id: Some(blake2_256(&[1u8; 32])),
							priority: 123,
							call: bound_large_call.clone(),
							maybe_periodic: Some((4u64, 20)),
							origin: signed(1),
							_phantom: PhantomData::<u64>::default(),
						}),
						Some(ScheduledOf::<Test> {
							maybe_id: Some(blake2_256(&[254u8; 32])),
							priority: 123,
							call: Bounded::from_legacy_hash(bound_hashed_call.hash()),
							maybe_periodic: Some((8u64, 10)),
							origin: signed(1),
							_phantom: PhantomData::<u64>::default(),
						}),
					],
				),
			];
			for (outer, (i, j)) in x.iter().zip(expected.iter()).enumerate() {
				assert_eq!(i.0, j.0);
				for (inner, (x, y)) in i.1.iter().zip(j.1.iter()).enumerate() {
					assert_eq!(x, y, "at index: outer {} inner {}", outer, inner);
				}
			}
			assert_eq_uvec!(x, expected);

			assert_eq!(StorageVersion::get::<Scheduler>(), 4);
		});
	}

	fn signed(i: u64) -> OriginCaller {
		system::RawOrigin::Signed(i).into()
	}
}
