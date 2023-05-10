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

// TODO gate
pub mod v10;
pub mod v11;
pub mod v9;

use crate::{weights::WeightInfo, Config, Error, MigrationInProgress, Pallet, Weight, LOG_TARGET};
use codec::{Codec, Decode};
use frame_support::{
	codec,
	pallet_prelude::*,
	traits::{ConstU32, Get, OnRuntimeUpgrade},
};
use sp_std::marker::PhantomData;

#[cfg(feature = "try-runtime")]
use sp_std::prelude::*;

const PROOF_ENCODE: &str = "Tuple::max_encoded_len() < Cursor::max_encoded_len()` is verified in `Self::integrity_test()`; qed";
const PROOF_DECODE: &str =
	"We encode to the same type in this trait only. No other code touches this item; qed";

fn invalid_version(version: StorageVersion) -> ! {
	panic!("Required migration {version:?} not supported by this runtime. This is a bug.");
}

pub type Cursor = BoundedVec<u8, ConstU32<1024>>;

type Migrations<T> = (v9::Migration<T>, v10::Migration<T>, v11::Migration<T>);

/// IsFinished describes whether a migration is finished or not.
pub enum IsFinished {
	Yes,
	No,
}

/// A trait that allows to migrate storage from one version to another.
///
/// The migration is done in steps. The migration is finished when
/// `step()` returns `IsFinished::Yes`.
pub trait Migrate: Codec + MaxEncodedLen + Default {
	/// Returns the version of the migration.
	const VERSION: u16;

	/// Returns the maximum weight that can be consumed in a single step.
	fn max_step_weight() -> Weight;

	/// Process one step of the migration.
	///
	/// Returns whether the migration is finished and the weight consumed.
	fn step(&mut self) -> (IsFinished, Weight);
}

/// A noop migration that can be used when there is no migration to be done for a given version.
#[doc(hidden)]
#[derive(frame_support::DefaultNoBound, Encode, Decode, MaxEncodedLen)]
pub struct NoopMigration<const N: u16>;

impl<const N: u16> Migrate for NoopMigration<N> {
	const VERSION: u16 = N;
	fn max_step_weight() -> Weight {
		Weight::zero()
	}
	fn step(&mut self) -> (IsFinished, Weight) {
		log::debug!(target: LOG_TARGET, "Noop migration for version {}", N);
		(IsFinished::Yes, Weight::zero())
	}
}

mod private {
	use crate::migration::Migrate;
	pub trait Sealed {}
	#[impl_trait_for_tuples::impl_for_tuples(10)]
	#[tuple_types_custom_trait_bound(Migrate)]
	impl Sealed for Tuple {}
}

/// Defines a sequence of migrations.
///
/// The sequence must be defined by a tuple of migrations, each of which must implement the
/// `Migrate` trait. Migrations must be ordered by their versions with no gaps.
pub trait MigrateSequence: private::Sealed {
	/// Returns the range of versions that this migration can handle.
	/// Migrations must be ordered by their versions with no gaps.
	/// The following code will fail to compile:
	///
	/// The following code will fail to compile:
	/// ```compile_fail
	///     # use pallet_contracts::{NoopMigration, MigrateSequence};
	/// 	let _ = <(NoopMigration<1>, NoopMigration<3>)>::VERSION_RANGE;
	/// ```
	/// The following code will compile:
	/// ```
	///     # use pallet_contracts::{NoopMigration, MigrateSequence};
	/// 	let _ = <(NoopMigration<1>, NoopMigration<2>)>::VERSION_RANGE;
	/// ```
	const VERSION_RANGE: (u16, u16);

	/// Returns the default cursor for the given version.
	fn new(version: StorageVersion) -> Cursor;

	/// Execute the migration step until the weight limit is reached.
	///
	/// Returns the new cursor or `None` if the migration is finished.
	fn steps(version: StorageVersion, cursor: &[u8], weight_left: &mut Weight) -> Option<Cursor>;

	/// Verify that each migration's cursor fits into `Cursor`.
	fn integrity_test();

	/// Returns whether migrating from `in_storage` to `target` is supported.
	///
	/// A migration is supported if (in_storage + 1, target) is contained by `VERSION_RANGE`.
	fn is_upgrade_supported(in_storage: StorageVersion, target: StorageVersion) -> bool {
		if in_storage == target {
			return true
		}
		if in_storage > target {
			return false
		}

		let (low, high) = Self::VERSION_RANGE;
		let Some(first_supported) = low.checked_sub(1) else {
			return false
		};

		in_storage == first_supported && target == high
	}
}

/// Performs all necessary migrations based on `StorageVersion`.
#[cfg(not(feature = "runtime-benchmarks"))]
pub struct Migration<T: Config, M: MigrateSequence = Migrations<T>>(PhantomData<(T, M)>);

/// Custom migration for running runtime-benchmarks.
#[cfg(feature = "runtime-benchmarks")]
pub struct Migration<T: Config, M: MigrateSequence = (NoopMigration<1>, NoopMigration<2>)>(
	PhantomData<(T, M)>,
);

impl<T: Config, M: MigrateSequence> OnRuntimeUpgrade for Migration<T, M> {
	fn on_runtime_upgrade() -> Weight {
		let latest_version = <Pallet<T>>::current_storage_version();
		let storage_version = <Pallet<T>>::on_chain_storage_version();

		if storage_version == latest_version {
			log::warn!(target: LOG_TARGET, "No Migration performed storage_version = latest_version = {:?}", &storage_version);
			return T::WeightInfo::on_runtime_upgrade_noop()
		}

		// In case a migration is already in progress we create the next migration
		// (if any) right when the current one finishes.
		if Self::in_progress() {
			log::warn!( target: LOG_TARGET, "Migration already in progress {:?}", &storage_version);
			return T::WeightInfo::on_runtime_upgrade_in_progress()
		}

		log::info!(
			target: LOG_TARGET,
			"Upgrading storage from {storage_version:?} to {latest_version:?}.",
		);

		let cursor = M::new(storage_version + 1);
		MigrationInProgress::<T>::set(Some(cursor));

		return T::WeightInfo::on_runtime_upgrade()
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		// We can't really do much here as our migrations do not happen during the runtime upgrade.
		// Instead, we call the migrations `pre_upgrade` and `post_upgrade` hooks when we iterate
		// over our migrations.
		let storage_version = <Pallet<T>>::on_chain_storage_version();
		let target_version = <Pallet<T>>::current_storage_version();
		if M::is_upgrade_supported(storage_version, target_version) {
			Ok(Vec::new())
		} else {
			log::error!(
				target: LOG_TARGET,
				"Range supported {:?}, range requested {:?}",
				M::VERSION_RANGE,
				(storage_version, target_version)
			);
			Err("New runtime does not contain the required migrations to perform this upgrade.")
		}
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(state: Vec<u8>) -> Result<(), &'static str> {
		let mut weight = Weight::zero();
		loop {
			use MigrateResult::*;
			match Self::migrate(Weight::MAX) {
				(InProgress, w) => {
					weight.saturating_add(w);
				},
				(NoMigrationPerformed | Completed, w) => {
					weight.saturating_add(w);
					break
				},
			}
		}

		log::info!(target: LOG_TARGET, "Migration steps weight = {}", weight);
		Ok(())
	}
}

/// The result of a migration step.
#[derive(Debug, PartialEq)]
pub enum MigrateResult {
	/// No migration was performed
	NoMigrationPerformed,
	/// A migration is in progress
	InProgress,
	/// All migrations are completed
	Completed,
}

impl<T: Config, M: MigrateSequence> Migration<T, M> {
	/// Verify that each migration's step of the MigrateSequence fits into `Cursor`.
	pub(crate) fn integrity_test() {
		M::integrity_test()
	}

	/// Migrate
	/// Return the weight used and whether or not a migration is in progress
	pub(crate) fn migrate(weight_limit: Weight) -> (MigrateResult, Weight) {
		let mut weight_left = weight_limit;

		if weight_left
			.checked_reduce(T::WeightInfo::migrate_update_storage_version())
			.is_none()
		{
			return (MigrateResult::NoMigrationPerformed, Weight::zero())
		}

		MigrationInProgress::<T>::mutate_exists(|progress| {
			let Some(cursor_before) = progress.as_mut() else {
				return (MigrateResult::NoMigrationPerformed, T::WeightInfo::migrate_noop())
			};

			// if a migration is running it is always upgrading to the next version
			let storage_version = <Pallet<T>>::on_chain_storage_version();
			let in_progress_version = storage_version + 1;

			log::info!(
				target: LOG_TARGET,
				"Migrating from {:?} to {:?},",
				storage_version,
				in_progress_version,
			);

			*progress =
				match M::steps(in_progress_version, cursor_before.as_ref(), &mut weight_left) {
					// ongoing
					Some(cursor) => {
						// refund as we did not update the storage version
						weight_left.saturating_accrue(T::WeightInfo::bump_storage_version());
						// we still have a cursor which keeps the pallet disabled
						Some(cursor)
					},
					// finished
					None => {
						in_progress_version.put::<Pallet<T>>();
						if <Pallet<T>>::current_storage_version() != in_progress_version {
							// chain the next migration
							log::info!(
								target: LOG_TARGET,
								"Next migration is {:?},",
								in_progress_version + 1,
							);
							Some(M::new(in_progress_version + 1))
						} else {
							// enable pallet by removing the storage item
							log::info!(
								target: LOG_TARGET,
								"All migrations done. At version {:?},",
								in_progress_version,
							);
							None
						}
					},
				};

			let state = match progress {
				Some(_) => MigrateResult::InProgress,
				None => MigrateResult::Completed,
			};

			(state, weight_limit.saturating_sub(weight_left))
		})
	}

	pub(crate) fn ensure_migrated() -> DispatchResult {
		if Self::in_progress() {
			Err(Error::<T>::MigrationInProgress.into())
		} else {
			Ok(())
		}
	}

	fn in_progress() -> bool {
		MigrationInProgress::<T>::exists()
	}
}

#[impl_trait_for_tuples::impl_for_tuples(10)]
#[tuple_types_custom_trait_bound(Migrate)]
impl MigrateSequence for Tuple {
	const VERSION_RANGE: (u16, u16) = {
		let mut versions: (u16, u16) = (0, 0);
		for_tuples!(
			#(
				match versions {
					(0, 0) => {
						versions = (Tuple::VERSION, Tuple::VERSION);
					},
					(min_version, last_version) if Tuple::VERSION == last_version + 1 => {
						versions = (min_version, Tuple::VERSION);
					},
					_ => panic!("Migrations must be ordered by their versions with no gaps.")
				}
			)*
		);
		versions
	};

	fn new(version: StorageVersion) -> Cursor {
		for_tuples!(
			#(
				if version == Tuple::VERSION {
					return Tuple::default().encode().try_into().expect(PROOF_ENCODE)
				}
			)*
		);
		invalid_version(version)
	}

	fn steps(
		version: StorageVersion,
		mut cursor: &[u8],
		weight_left: &mut Weight,
	) -> Option<Cursor> {
		for_tuples!(
			#(
				if version == Tuple::VERSION {
					let mut migration = <Tuple as Decode>::decode(&mut cursor)
						.expect(PROOF_DECODE);
					let max_weight = Tuple::max_step_weight();
					while weight_left.all_gt(max_weight) {
						let (finished, weight) = migration.step();
						weight_left.saturating_reduce(weight);
						if matches!(finished, IsFinished::Yes) {
							return None
						}
					}
					return Some(migration.encode().try_into().expect(PROOF_ENCODE))
				}
			)*
		);
		invalid_version(version)
	}

	fn integrity_test() {
		for_tuples!(
			#(
				let len = <Tuple as MaxEncodedLen>::max_encoded_len();
				let max = Cursor::bound();
				if len > max {
					let version = Tuple::VERSION;
					panic!(
						"Migration {} has size {} which is bigger than the maximum of {}",
						version, len, max,
					);
				}
			)*
		);
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::tests::{ExtBuilder, Test};

	#[derive(Default, Encode, Decode, MaxEncodedLen)]
	struct MockMigration<const N: u16> {
		// MockMigration<N> needs `N` steps to finish
		count: u16,
	}

	impl<const N: u16> Migrate for MockMigration<N> {
		const VERSION: u16 = N;
		fn max_step_weight() -> Weight {
			Weight::from_all(1)
		}
		fn step(&mut self) -> (IsFinished, Weight) {
			assert!(self.count != N);
			self.count += 1;
			if self.count == N {
				(IsFinished::Yes, Weight::from_all(1))
			} else {
				(IsFinished::No, Weight::from_all(1))
			}
		}
	}

	#[test]
	fn check_versions() {
		// this fails the compilation when running local tests
		// otherwise it will only be evaluated when the whole runtime is build
		let _ = Migrations::<Test>::VERSION_RANGE;
	}

	#[test]
	fn version_range_works() {
		let range = <(MockMigration<1>, MockMigration<2>)>::VERSION_RANGE;
		assert_eq!(range, (1, 2));
	}

	#[test]
	fn is_upgrade_supported_works() {
		type M = (MockMigration<7>, MockMigration<8>, MockMigration<9>);

		[(1, 1), (6, 9)].into_iter().for_each(|(from, to)| {
			assert!(
				M::is_upgrade_supported(StorageVersion::new(from), StorageVersion::new(to)),
				"{} -> {} is supported",
				from,
				to
			)
		});

		[(1, 0), (0, 3), (5, 9), (7, 10)].into_iter().for_each(|(from, to)| {
			assert!(
				!M::is_upgrade_supported(StorageVersion::new(from), StorageVersion::new(to)),
				"{} -> {} is not supported",
				from,
				to
			)
		});
	}

	// #[test]
	// fn steps_works() {
	// 	type M = (MockMigration<1>, MockMigration<2>);
	// 	let version = StorageVersion::new(1);
	// 	let cursor = M::new(version);
	//
	// 	let mut weight = Weight::MAX;
	// 	let cursor = M::steps(version, &cursor, &mut weight).unwrap();
	// 	assert_eq!(cursor.to_vec(), vec![1u8, 0]);
	//
	// 	assert!(M::steps(version, &cursor, &mut weight).is_none());
	// }

	#[test]
	fn no_migration_performed_works() {
		type M = (MockMigration<1>, MockMigration<2>);
		type TestMigration = Migration<Test, M>;

		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 2);
			assert_eq!(TestMigration::migrate(Weight::MAX).0, MigrateResult::NoMigrationPerformed)
		});
	}

	#[test]
	fn migration_works() {
		type M = (MockMigration<1>, MockMigration<2>);
		type TestMigration = Migration<Test, M>;

		ExtBuilder::default().set_storage_version(0).build().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 0);
			TestMigration::on_runtime_upgrade();
			for (version, status) in [(1, MigrateResult::InProgress), (2, MigrateResult::Completed)]
			{
				assert_eq!(TestMigration::migrate(Weight::MAX).0, status);
				assert_eq!(
					<Pallet<Test>>::on_chain_storage_version(),
					StorageVersion::new(version)
				);
			}

			assert_eq!(TestMigration::migrate(Weight::MAX).0, MigrateResult::NoMigrationPerformed);
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 2);
		});
	}
}
