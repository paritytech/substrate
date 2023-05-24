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

//! Migrations for the scheduler pallet.

use super::*;
use frame_support::traits::OnRuntimeUpgrade;

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

/// The log target.
const TARGET: &'static str = "runtime::scheduler::migration";

pub mod v1 {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[frame_support::storage_alias]
	pub(crate) type Agenda<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::BlockNumber,
		Vec<
			Option<
				ScheduledV1<<T as Config>::RuntimeCall, <T as frame_system::Config>::BlockNumber>,
			>,
		>,
		ValueQuery,
	>;

	#[frame_support::storage_alias]
	pub(crate) type Lookup<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		Vec<u8>,
		TaskAddress<<T as frame_system::Config>::BlockNumber>,
	>;
}

pub mod v2 {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[frame_support::storage_alias]
	pub(crate) type Agenda<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::BlockNumber,
		Vec<Option<ScheduledV2Of<T>>>,
		ValueQuery,
	>;

	#[frame_support::storage_alias]
	pub(crate) type Lookup<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		Vec<u8>,
		TaskAddress<<T as frame_system::Config>::BlockNumber>,
	>;
}

pub mod v3 {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[frame_support::storage_alias]
	pub(crate) type Agenda<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::BlockNumber,
		Vec<Option<ScheduledV3Of<T>>>,
		ValueQuery,
	>;

	#[frame_support::storage_alias]
	pub(crate) type Lookup<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		Vec<u8>,
		TaskAddress<<T as frame_system::Config>::BlockNumber>,
	>;

	/// Migrate the scheduler pallet from V3 to V4.
	pub struct MigrateToV4<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config<Hash = PreimageHash>> OnRuntimeUpgrade for MigrateToV4<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 3, "Can only upgrade from version 3");

			let agendas = Agenda::<T>::iter_keys().count() as u32;
			let decodable_agendas = Agenda::<T>::iter_values().count() as u32;
			if agendas != decodable_agendas {
				// This is not necessarily an error, but can happen when there are Calls
				// in an Agenda that are not valid anymore with the new runtime.
				log::error!(
					target: TARGET,
					"Can only decode {} of {} agendas - others will be dropped",
					decodable_agendas,
					agendas
				);
			}
			log::info!(target: TARGET, "Trying to migrate {} agendas...", decodable_agendas);

			// Check that no agenda overflows `MaxScheduledPerBlock`.
			let max_scheduled_per_block = T::MaxScheduledPerBlock::get() as usize;
			for (block_number, agenda) in Agenda::<T>::iter() {
				if agenda.iter().cloned().filter_map(|s| s).count() > max_scheduled_per_block {
					log::error!(
						target: TARGET,
						"Would truncate agenda of block {:?} from {} items to {} items.",
						block_number,
						agenda.len(),
						max_scheduled_per_block,
					);
					return Err("Agenda would overflow `MaxScheduledPerBlock`.".into())
				}
			}
			// Check that bounding the calls will not overflow `MAX_LENGTH`.
			let max_length = T::Preimages::MAX_LENGTH as usize;
			for (block_number, agenda) in Agenda::<T>::iter() {
				for schedule in agenda.iter().cloned().filter_map(|s| s) {
					match schedule.call {
						frame_support::traits::schedule::MaybeHashed::Value(call) => {
							let l = call.using_encoded(|c| c.len());
							if l > max_length {
								log::error!(
									target: TARGET,
									"Call in agenda of block {:?} is too large: {} byte",
									block_number,
									l,
								);
								return Err("Call is too large.".into())
							}
						},
						_ => (),
					}
				}
			}

			Ok((decodable_agendas as u32).encode())
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
		fn post_upgrade(state: Vec<u8>) -> Result<(), TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 4, "Must upgrade");

			// Check that everything decoded fine.
			for k in crate::Agenda::<T>::iter_keys() {
				ensure!(crate::Agenda::<T>::try_get(k).is_ok(), "Cannot decode V4 Agenda");
			}

			let old_agendas: u32 =
				Decode::decode(&mut &state[..]).expect("pre_upgrade provides a valid state; qed");
			let new_agendas = crate::Agenda::<T>::iter_keys().count() as u32;
			if old_agendas != new_agendas {
				// This is not necessarily an error, but can happen when there are Calls
				// in an Agenda that are not valid anymore in the new runtime.
				log::error!(
					target: TARGET,
					"Did not migrate all Agendas. Previous {}, Now {}",
					old_agendas,
					new_agendas,
				);
			} else {
				log::info!(target: TARGET, "Migrated {} agendas.", new_agendas);
			}

			Ok(())
		}
	}
}

pub mod v4 {
	use super::*;
	use frame_support::pallet_prelude::*;

	/// This migration cleans up empty agendas of the V4 scheduler.
	///
	/// This should be run on a scheduler that does not have
	/// <https://github.com/paritytech/substrate/pull/12989> since it piles up `None`-only agendas. This does not modify the pallet version.
	pub struct CleanupAgendas<T>(sp_std::marker::PhantomData<T>);

	impl<T: Config> OnRuntimeUpgrade for CleanupAgendas<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			assert_eq!(
				StorageVersion::get::<Pallet<T>>(),
				4,
				"Can only cleanup agendas of the V4 scheduler"
			);

			let agendas = Agenda::<T>::iter_keys().count();
			let non_empty_agendas =
				Agenda::<T>::iter_values().filter(|a| a.iter().any(|s| s.is_some())).count();
			log::info!(
				target: TARGET,
				"There are {} total and {} non-empty agendas",
				agendas,
				non_empty_agendas
			);

			Ok((agendas as u32, non_empty_agendas as u32).encode())
		}

		fn on_runtime_upgrade() -> Weight {
			let version = StorageVersion::get::<Pallet<T>>();
			if version != 4 {
				log::warn!(target: TARGET, "Skipping CleanupAgendas migration since it was run on the wrong version: {:?} != 4", version);
				return T::DbWeight::get().reads(1)
			}

			let keys = Agenda::<T>::iter_keys().collect::<Vec<_>>();
			let mut writes = 0;
			for k in &keys {
				let mut schedules = Agenda::<T>::get(k);
				let all_schedules = schedules.len();
				let suffix_none_schedules =
					schedules.iter().rev().take_while(|s| s.is_none()).count();

				match all_schedules.checked_sub(suffix_none_schedules) {
					Some(0) => {
						log::info!(
							"Deleting None-only agenda {:?} with {} entries",
							k,
							all_schedules
						);
						Agenda::<T>::remove(k);
						writes.saturating_inc();
					},
					Some(ne) if ne > 0 => {
						log::info!(
							"Removing {} schedules of {} from agenda {:?}, now {:?}",
							suffix_none_schedules,
							all_schedules,
							ne,
							k
						);
						schedules.truncate(ne);
						Agenda::<T>::insert(k, schedules);
						writes.saturating_inc();
					},
					Some(_) => {
						frame_support::defensive!(
							// Bad but let's not panic.
							"Cannot have more None suffix schedules that schedules in total"
						);
					},
					None => {
						log::info!("Agenda {:?} does not have any None suffix schedules", k);
					},
				}
			}

			// We don't modify the pallet version.

			T::DbWeight::get().reads_writes(1 + keys.len().saturating_mul(2) as u64, writes)
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(state: Vec<u8>) -> Result<(), TryRuntimeError> {
			ensure!(StorageVersion::get::<Pallet<T>>() == 4, "Version must not change");

			let (old_agendas, non_empty_agendas): (u32, u32) =
				Decode::decode(&mut state.as_ref()).expect("Must decode pre_upgrade state");
			let new_agendas = Agenda::<T>::iter_keys().count() as u32;

			match old_agendas.checked_sub(new_agendas) {
				Some(0) => log::warn!(
					target: TARGET,
					"Did not clean up any agendas. v4::CleanupAgendas can be removed."
				),
				Some(n) => {
					log::info!(target: TARGET, "Cleaned up {} agendas, now {}", n, new_agendas)
				},
				None => unreachable!(
					"Number of agendas cannot increase, old {} new {}",
					old_agendas, new_agendas
				),
			}
			ensure!(new_agendas == non_empty_agendas, "Expected to keep all non-empty agendas");

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
	use sp_std::borrow::Cow;
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
			// Call that is already hashed and can will be converted to `Legacy`.
			let hashed_call =
				RuntimeCall::System(frame_system::Call::remark { remark: vec![0; 2048] });
			let bound_hashed_call = Preimage::bound(hashed_call.clone()).unwrap();
			assert!(bound_hashed_call.lookup_needed());
			// A Call by hash that will fail to decode becomes `None`.
			let trash_data = vec![255u8; 1024];
			let undecodable_hash = Preimage::note(Cow::Borrowed(&trash_data)).unwrap();

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
						maybe_id: Some(vec![i as u8; 32]),
						priority: 123,
						call: large_call.clone().into(),
						maybe_periodic: Some((4u64, 20)),
						origin: signed(i),
						_phantom: PhantomData::<u64>::default(),
					}),
					Some(ScheduledV3Of::<Test> {
						maybe_id: Some(vec![255 - i as u8; 320]),
						priority: 123,
						call: MaybeHashed::Hash(bound_hashed_call.hash()),
						maybe_periodic: Some((8u64, 10)),
						origin: signed(i),
						_phantom: PhantomData::<u64>::default(),
					}),
					Some(ScheduledV3Of::<Test> {
						maybe_id: Some(vec![i as u8; 320]),
						priority: 123,
						call: MaybeHashed::Hash(undecodable_hash.clone()),
						maybe_periodic: Some((4u64, 20)),
						origin: root(),
						_phantom: PhantomData::<u64>::default(),
					}),
				];
				frame_support::migration::put_storage_value(b"Scheduler", b"Agenda", &k, old);
			}

			let state = v3::MigrateToV4::<Test>::pre_upgrade().unwrap();
			let _w = v3::MigrateToV4::<Test>::on_runtime_upgrade();
			v3::MigrateToV4::<Test>::post_upgrade(state).unwrap();

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
							maybe_id: Some(blake2_256(&[255u8; 320])),
							priority: 123,
							call: Bounded::from_legacy_hash(bound_hashed_call.hash()),
							maybe_periodic: Some((8u64, 10)),
							origin: signed(0),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
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
							maybe_id: Some(blake2_256(&[254u8; 320])),
							priority: 123,
							call: Bounded::from_legacy_hash(bound_hashed_call.hash()),
							maybe_periodic: Some((8u64, 10)),
							origin: signed(1),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
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

	#[test]
	#[allow(deprecated)]
	fn migration_v3_to_v4_too_large_calls_are_ignored() {
		new_test_ext().execute_with(|| {
			// Assume that we are at V3.
			StorageVersion::new(3).put::<Scheduler>();

			let too_large_call = RuntimeCall::System(frame_system::Call::remark {
				remark: vec![0; <Test as Config>::Preimages::MAX_LENGTH + 1],
			});

			let i = 0u64;
			let k = i.twox_64_concat();
			let old = vec![Some(ScheduledV3Of::<Test> {
				maybe_id: None,
				priority: 1,
				call: too_large_call.clone().into(),
				maybe_periodic: None,
				origin: root(),
				_phantom: PhantomData::<u64>::default(),
			})];
			frame_support::migration::put_storage_value(b"Scheduler", b"Agenda", &k, old);

			// The pre_upgrade hook fails:
			let err = v3::MigrateToV4::<Test>::pre_upgrade().unwrap_err();
			assert!(err == "Call is too large".into());
			// But the migration itself works:
			let _w = v3::MigrateToV4::<Test>::on_runtime_upgrade();

			let mut x = Agenda::<Test>::iter().map(|x| (x.0, x.1.into_inner())).collect::<Vec<_>>();
			x.sort_by_key(|x| x.0);
			// The call becomes `None`.
			let expected = vec![(0, vec![None])];
			assert_eq_uvec!(x, expected);

			assert_eq!(StorageVersion::get::<Scheduler>(), 4);
		});
	}

	#[test]
	fn cleanup_agendas_works() {
		use sp_core::bounded_vec;
		new_test_ext().execute_with(|| {
			StorageVersion::new(4).put::<Scheduler>();

			let call = RuntimeCall::System(frame_system::Call::remark { remark: vec![] });
			let bounded_call = Preimage::bound(call).unwrap();
			let some = Some(ScheduledOf::<Test> {
				maybe_id: None,
				priority: 1,
				call: bounded_call,
				maybe_periodic: None,
				origin: root(),
				_phantom: Default::default(),
			});

			// Put some empty, and some non-empty agendas in there.
			let test_data: Vec<(
				BoundedVec<Option<ScheduledOf<Test>>, <Test as Config>::MaxScheduledPerBlock>,
				Option<
					BoundedVec<Option<ScheduledOf<Test>>, <Test as Config>::MaxScheduledPerBlock>,
				>,
			)> = vec![
				(bounded_vec![some.clone()], Some(bounded_vec![some.clone()])),
				(bounded_vec![None, some.clone()], Some(bounded_vec![None, some.clone()])),
				(bounded_vec![None, some.clone(), None], Some(bounded_vec![None, some.clone()])),
				(bounded_vec![some.clone(), None, None], Some(bounded_vec![some.clone()])),
				(bounded_vec![None, None], None),
				(bounded_vec![None, None, None], None),
				(bounded_vec![], None),
			];

			// Insert all the agendas.
			for (i, test) in test_data.iter().enumerate() {
				Agenda::<Test>::insert(i as u64, test.0.clone());
			}

			// Run the migration.
			let data = v4::CleanupAgendas::<Test>::pre_upgrade().unwrap();
			let _w = v4::CleanupAgendas::<Test>::on_runtime_upgrade();
			v4::CleanupAgendas::<Test>::post_upgrade(data).unwrap();

			// Check that the post-state is correct.
			for (i, test) in test_data.iter().enumerate() {
				match test.1.clone() {
					None => assert!(
						!Agenda::<Test>::contains_key(i as u64),
						"Agenda {} should be removed",
						i
					),
					Some(new) => {
						assert_eq!(Agenda::<Test>::get(i as u64), new, "Agenda wrong {}", i)
					},
				}
			}
		});
	}

	fn signed(i: u64) -> OriginCaller {
		system::RawOrigin::Signed(i).into()
	}
}
