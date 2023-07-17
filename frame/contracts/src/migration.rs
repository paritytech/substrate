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

//! Multi-block Migration framework for pallet-contracts.
//!
//! This module allows us to define a migration as a sequence of [`MigrationStep`]s that can be
//! executed across multiple blocks.
//!
//! # Usage
//!
//! A migration step is defined under `src/migration/vX.rs`, where `X` is the version number.
//! For example, `vX.rs` defines a migration from version `X - 1` to version `X`.
//!
//! ## Example:
//!
//! To configure a migration to `v11` for a runtime using `v10` of pallet-contracts on the chain,
//! you would set the `Migrations` type as follows:
//!
//! ```
//! use pallet_contracts::migration::{v10, v11};
//! # pub enum Runtime {};
//! type Migrations = (v10::Migration<Runtime>, v11::Migration<Runtime>);
//! ```
//!
//! ## Notes:
//!
//! - Migrations should always be tested with `try-runtime` before being deployed.
//! - By testing with `try-runtime` against a live network, you ensure that all migration steps work
//!   and that you have included the required steps.
//!
//! ## Low Level / Implementation Details
//!
//! When a migration starts and [`OnRuntimeUpgrade::on_runtime_upgrade`] is called, instead of
//! performing the actual migration, we set a custom storage item [`MigrationInProgress`].
//! This storage item defines a [`Cursor`] for the current migration.
//!
//! If the [`MigrationInProgress`] storage item exists, it means a migration is in progress, and its
//! value holds a cursor for the current migration step. These migration steps are executed during
//! [`Hooks<BlockNumber>::on_idle`] or when the [`Pallet::migrate`] dispatchable is
//! called.
//!
//! While the migration is in progress, all dispatchables except `migrate`, are blocked, and returns
//! a `MigrationInProgress` error.

pub mod v09;
pub mod v10;
pub mod v11;
pub mod v12;

use crate::{weights::WeightInfo, Config, Error, MigrationInProgress, Pallet, Weight, LOG_TARGET};
use codec::{Codec, Decode};
use frame_support::{
	codec,
	pallet_prelude::*,
	traits::{ConstU32, OnRuntimeUpgrade},
};
use sp_runtime::Saturating;
use sp_std::marker::PhantomData;

#[cfg(feature = "try-runtime")]
use sp_std::prelude::*;

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

const PROOF_ENCODE: &str = "Tuple::max_encoded_len() < Cursor::max_encoded_len()` is verified in `Self::integrity_test()`; qed";
const PROOF_DECODE: &str =
	"We encode to the same type in this trait only. No other code touches this item; qed";

fn invalid_version(version: StorageVersion) -> ! {
	panic!("Required migration {version:?} not supported by this runtime. This is a bug.");
}

/// The cursor used to encode the position (usually the last iterated key) of the current migration
/// step.
pub type Cursor = BoundedVec<u8, ConstU32<1024>>;

/// IsFinished describes whether a migration is finished or not.
pub enum IsFinished {
	Yes,
	No,
}

/// A trait that allows to migrate storage from one version to another.
///
/// The migration is done in steps. The migration is finished when
/// `step()` returns `IsFinished::Yes`.
pub trait MigrationStep: Codec + MaxEncodedLen + Default {
	/// Returns the version of the migration.
	const VERSION: u16;

	/// Returns the maximum weight that can be consumed in a single step.
	fn max_step_weight() -> Weight;

	/// Process one step of the migration.
	///
	/// Returns whether the migration is finished and the weight consumed.
	fn step(&mut self) -> (IsFinished, Weight);

	/// Verify that the migration step fits into `Cursor`, and that `max_step_weight` is not greater
	/// than `max_block_weight`.
	fn integrity_test(max_block_weight: Weight) {
		if Self::max_step_weight().any_gt(max_block_weight) {
			panic!(
				"Invalid max_step_weight for Migration {}. Value should be lower than {}",
				Self::VERSION,
				max_block_weight
			);
		}

		let len = <Self as MaxEncodedLen>::max_encoded_len();
		let max = Cursor::bound();
		if len > max {
			panic!(
				"Migration {} has size {} which is bigger than the maximum of {}",
				Self::VERSION,
				len,
				max,
			);
		}
	}

	/// Execute some pre-checks prior to running the first step of this migration.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		Ok(Vec::new())
	}

	/// Execute some post-checks after running the last step of this migration.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(_state: Vec<u8>) -> Result<(), TryRuntimeError> {
		Ok(())
	}
}

/// A noop migration that can be used when there is no migration to be done for a given version.
#[doc(hidden)]
#[derive(frame_support::DefaultNoBound, Encode, Decode, MaxEncodedLen)]
pub struct NoopMigration<const N: u16>;

impl<const N: u16> MigrationStep for NoopMigration<N> {
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
	use crate::migration::MigrationStep;
	pub trait Sealed {}
	#[impl_trait_for_tuples::impl_for_tuples(10)]
	#[tuple_types_custom_trait_bound(MigrationStep)]
	impl Sealed for Tuple {}
}

/// Defines a sequence of migrations.
///
/// The sequence must be defined by a tuple of migrations, each of which must implement the
/// `MigrationStep` trait. Migrations must be ordered by their versions with no gaps.
pub trait MigrateSequence: private::Sealed {
	/// Returns the range of versions that this migrations sequence can handle.
	/// Migrations must be ordered by their versions with no gaps.
	///
	/// The following code will fail to compile:
	///
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

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step(_version: StorageVersion) -> Result<Vec<u8>, TryRuntimeError> {
		Ok(Vec::new())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(_version: StorageVersion, _state: Vec<u8>) -> Result<(), TryRuntimeError> {
		Ok(())
	}

	/// Execute the migration step until the weight limit is reached.
	fn steps(version: StorageVersion, cursor: &[u8], weight_left: &mut Weight) -> StepResult;

	/// Verify that the migration step fits into `Cursor`, and that `max_step_weight` is not greater
	/// than `max_block_weight`.
	fn integrity_test(max_block_weight: Weight);

	/// Returns whether migrating from `in_storage` to `target` is supported.
	///
	/// A migration is supported if `VERSION_RANGE` is (in_storage + 1, target).
	fn is_upgrade_supported(in_storage: StorageVersion, target: StorageVersion) -> bool {
		let (low, high) = Self::VERSION_RANGE;
		target == high && in_storage + 1 == low
	}
}

/// Performs all necessary migrations based on `StorageVersion`.
///
/// If `TEST_ALL_STEPS == true` and `try-runtime` is enabled, this will run all the migrations
/// inside `on_runtime_upgrade`. This should be set to false in tests that want to ensure the step
/// by step migration works.
pub struct Migration<T: Config, const TEST_ALL_STEPS: bool = true>(PhantomData<T>);

#[cfg(feature = "try-runtime")]
impl<T: Config, const TEST_ALL_STEPS: bool> Migration<T, TEST_ALL_STEPS> {
	fn run_all_steps() -> Result<(), TryRuntimeError> {
		let mut weight = Weight::zero();
		let name = <Pallet<T>>::name();
		loop {
			let in_progress_version = <Pallet<T>>::on_chain_storage_version() + 1;
			let state = T::Migrations::pre_upgrade_step(in_progress_version)?;
			let (status, w) = Self::migrate(Weight::MAX);
			weight.saturating_accrue(w);
			log::info!(
				target: LOG_TARGET,
				"{name}: Migration step {:?} weight = {}",
				in_progress_version,
				weight
			);
			T::Migrations::post_upgrade_step(in_progress_version, state)?;
			if matches!(status, MigrateResult::Completed) {
				break
			}
		}

		let name = <Pallet<T>>::name();
		log::info!(target: LOG_TARGET, "{name}: Migration steps weight = {}", weight);
		Ok(())
	}
}

impl<T: Config, const TEST_ALL_STEPS: bool> OnRuntimeUpgrade for Migration<T, TEST_ALL_STEPS> {
	fn on_runtime_upgrade() -> Weight {
		let name = <Pallet<T>>::name();
		let latest_version = <Pallet<T>>::current_storage_version();
		let storage_version = <Pallet<T>>::on_chain_storage_version();

		if storage_version == latest_version {
			log::warn!(
				target: LOG_TARGET,
				"{name}: No Migration performed storage_version = latest_version = {:?}",
				&storage_version
			);
			return T::WeightInfo::on_runtime_upgrade_noop()
		}

		// In case a migration is already in progress we create the next migration
		// (if any) right when the current one finishes.
		if Self::in_progress() {
			log::warn!(
				target: LOG_TARGET,
				"{name}: Migration already in progress {:?}",
				&storage_version
			);

			return T::WeightInfo::on_runtime_upgrade_in_progress()
		}

		log::info!(
			target: LOG_TARGET,
			"{name}: Upgrading storage from {storage_version:?} to {latest_version:?}.",
		);

		let cursor = T::Migrations::new(storage_version + 1);
		MigrationInProgress::<T>::set(Some(cursor));

		#[cfg(feature = "try-runtime")]
		if TEST_ALL_STEPS {
			Self::run_all_steps().unwrap();
		}

		T::WeightInfo::on_runtime_upgrade()
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
		// We can't really do much here as our migrations do not happen during the runtime upgrade.
		// Instead, we call the migrations `pre_upgrade` and `post_upgrade` hooks when we iterate
		// over our migrations.
		let storage_version = <Pallet<T>>::on_chain_storage_version();
		let target_version = <Pallet<T>>::current_storage_version();

		ensure!(
			storage_version != target_version,
			"No upgrade: Please remove this migration from your runtime upgrade configuration."
		);

		log::debug!(
			target: LOG_TARGET,
			"Requested migration of {} from {:?}(on-chain storage version) to {:?}(current storage version)",
			<Pallet<T>>::name(), storage_version, target_version
		);

		ensure!(
			T::Migrations::is_upgrade_supported(storage_version, target_version),
			"Unsupported upgrade: VERSION_RANGE should be (on-chain storage version + 1, current storage version)"
		);
		Ok(Default::default())
	}
}

/// The result of running the migration.
#[derive(Debug, PartialEq)]
pub enum MigrateResult {
	/// No migration was performed
	NoMigrationPerformed,
	/// No migration currently in progress
	NoMigrationInProgress,
	/// A migration is in progress
	InProgress { steps_done: u32 },
	/// All migrations are completed
	Completed,
}

/// The result of running a migration step.
#[derive(Debug, PartialEq)]
pub enum StepResult {
	InProgress { cursor: Cursor, steps_done: u32 },
	Completed { steps_done: u32 },
}

impl<T: Config, const TEST_ALL_STEPS: bool> Migration<T, TEST_ALL_STEPS> {
	/// Verify that each migration's step of the [`Config::Migrations`] sequence fits into
	/// `Cursor`.
	pub(crate) fn integrity_test() {
		let max_weight = <T as frame_system::Config>::BlockWeights::get().max_block;
		T::Migrations::integrity_test(max_weight)
	}

	/// Migrate
	/// Return the weight used and whether or not a migration is in progress
	pub(crate) fn migrate(weight_limit: Weight) -> (MigrateResult, Weight) {
		let name = <Pallet<T>>::name();
		let mut weight_left = weight_limit;

		if weight_left.checked_reduce(T::WeightInfo::migrate()).is_none() {
			return (MigrateResult::NoMigrationPerformed, Weight::zero())
		}

		MigrationInProgress::<T>::mutate_exists(|progress| {
			let Some(cursor_before) = progress.as_mut() else {
				return (MigrateResult::NoMigrationInProgress, T::WeightInfo::migration_noop())
			};

			// if a migration is running it is always upgrading to the next version
			let storage_version = <Pallet<T>>::on_chain_storage_version();
			let in_progress_version = storage_version + 1;

			log::info!(
				target: LOG_TARGET,
				"{name}: Migrating from {:?} to {:?},",
				storage_version,
				in_progress_version,
			);

			let result = match T::Migrations::steps(
				in_progress_version,
				cursor_before.as_ref(),
				&mut weight_left,
			) {
				StepResult::InProgress { cursor, steps_done } => {
					*progress = Some(cursor);
					MigrateResult::InProgress { steps_done }
				},
				StepResult::Completed { steps_done } => {
					in_progress_version.put::<Pallet<T>>();
					if <Pallet<T>>::current_storage_version() != in_progress_version {
						log::info!(
							target: LOG_TARGET,
							"{name}: Next migration is {:?},",
							in_progress_version + 1
						);
						*progress = Some(T::Migrations::new(in_progress_version + 1));
						MigrateResult::InProgress { steps_done }
					} else {
						log::info!(
							target: LOG_TARGET,
							"{name}: All migrations done. At version {:?},",
							in_progress_version
						);
						*progress = None;
						MigrateResult::Completed
					}
				},
			};

			(result, weight_limit.saturating_sub(weight_left))
		})
	}

	pub(crate) fn ensure_migrated() -> DispatchResult {
		if Self::in_progress() {
			Err(Error::<T>::MigrationInProgress.into())
		} else {
			Ok(())
		}
	}

	pub(crate) fn in_progress() -> bool {
		MigrationInProgress::<T>::exists()
	}
}

#[impl_trait_for_tuples::impl_for_tuples(10)]
#[tuple_types_custom_trait_bound(MigrationStep)]
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

	#[cfg(feature = "try-runtime")]
	/// Execute the pre-checks of the step associated with this version.
	fn pre_upgrade_step(version: StorageVersion) -> Result<Vec<u8>, TryRuntimeError> {
		for_tuples!(
			#(
				if version == Tuple::VERSION {
					return Tuple::pre_upgrade_step()
				}
			)*
		);
		invalid_version(version)
	}

	#[cfg(feature = "try-runtime")]
	/// Execute the post-checks of the step associated with this version.
	fn post_upgrade_step(version: StorageVersion, state: Vec<u8>) -> Result<(), TryRuntimeError> {
		for_tuples!(
			#(
				if version == Tuple::VERSION {
					return Tuple::post_upgrade_step(state)
				}
			)*
		);
		invalid_version(version)
	}

	fn steps(version: StorageVersion, mut cursor: &[u8], weight_left: &mut Weight) -> StepResult {
		for_tuples!(
			#(
				if version == Tuple::VERSION {
					let mut migration = <Tuple as Decode>::decode(&mut cursor)
						.expect(PROOF_DECODE);
					let max_weight = Tuple::max_step_weight();
					let mut steps_done = 0;
					while weight_left.all_gt(max_weight) {
						let (finished, weight) = migration.step();
						steps_done.saturating_accrue(1);
						weight_left.saturating_reduce(weight);
						if matches!(finished, IsFinished::Yes) {
							return StepResult::Completed{ steps_done }
						}
					}
					return StepResult::InProgress{cursor: migration.encode().try_into().expect(PROOF_ENCODE), steps_done }
				}
			)*
		);
		invalid_version(version)
	}

	fn integrity_test(max_block_weight: Weight) {
		for_tuples!(
			#(
				Tuple::integrity_test(max_block_weight);
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

	impl<const N: u16> MigrationStep for MockMigration<N> {
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
	fn version_range_works() {
		let range = <(MockMigration<1>, MockMigration<2>)>::VERSION_RANGE;
		assert_eq!(range, (1, 2));
	}

	#[test]
	fn is_upgrade_supported_works() {
		type Migrations = (MockMigration<9>, MockMigration<10>, MockMigration<11>);
		assert!(Migrations::is_upgrade_supported(StorageVersion::new(8), StorageVersion::new(11)));
		assert!(!Migrations::is_upgrade_supported(StorageVersion::new(9), StorageVersion::new(11)));
		assert!(!Migrations::is_upgrade_supported(StorageVersion::new(8), StorageVersion::new(12)));
	}

	#[test]
	fn steps_works() {
		type Migrations = (MockMigration<2>, MockMigration<3>);
		let version = StorageVersion::new(2);
		let mut cursor = Migrations::new(version);

		let mut weight = Weight::from_all(2);
		let result = Migrations::steps(version, &cursor, &mut weight);
		cursor = vec![1u8, 0].try_into().unwrap();
		assert_eq!(result, StepResult::InProgress { cursor: cursor.clone(), steps_done: 1 });
		assert_eq!(weight, Weight::from_all(1));

		let mut weight = Weight::from_all(2);
		assert_eq!(
			Migrations::steps(version, &cursor, &mut weight),
			StepResult::Completed { steps_done: 1 }
		);
	}

	#[test]
	fn no_migration_in_progress_works() {
		type TestMigration = Migration<Test>;

		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 2);
			assert_eq!(TestMigration::migrate(Weight::MAX).0, MigrateResult::NoMigrationInProgress)
		});
	}

	#[test]
	fn migration_works() {
		type TestMigration = Migration<Test, false>;

		ExtBuilder::default().set_storage_version(0).build().execute_with(|| {
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 0);
			TestMigration::on_runtime_upgrade();
			for (version, status) in
				[(1, MigrateResult::InProgress { steps_done: 1 }), (2, MigrateResult::Completed)]
			{
				assert_eq!(TestMigration::migrate(Weight::MAX).0, status);
				assert_eq!(
					<Pallet<Test>>::on_chain_storage_version(),
					StorageVersion::new(version)
				);
			}

			assert_eq!(TestMigration::migrate(Weight::MAX).0, MigrateResult::NoMigrationInProgress);
			assert_eq!(StorageVersion::get::<Pallet<Test>>(), 2);
		});
	}
}
