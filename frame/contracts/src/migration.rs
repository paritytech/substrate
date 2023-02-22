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

mod v9;

use crate::{Config, Error, MigrationInProgress, Pallet, Weight, LOG_TARGET};
use codec::{Codec, Decode};
use frame_support::{
	codec,
	pallet_prelude::*,
	traits::{ConstU32, Get, OnRuntimeUpgrade},
};
use sp_std::{marker::PhantomData, prelude::*};

const PROOF_ENCODE: &str = "Tuple::max_encoded_len() < Cursor::max_encoded_len()` is verified in `Self::integrity_test()`; qed";
const PROOF_DECODE: &str =
	"We encode to the same type in this trait only. No other code touches this item; qed";
const PROOF_EXISTS: &str = "Required migration not supported by this runtime. This is a bug.";

pub type Cursor = BoundedVec<u8, ConstU32<1024>>;
type Migrations<T> = (v9::Migration<T>,);

enum IsFinished {
	Yes,
	No,
}

trait Migrate<T: Config>: Codec + MaxEncodedLen + Default {
	const VERSION: u16;

	fn max_step_weight() -> Weight;

	fn step(&mut self) -> (IsFinished, Option<Weight>);
}

trait MigrateSequence<T: Config> {
	const VERSION_RANGE: Option<(u16, u16)>;

	fn new(version: StorageVersion) -> Cursor;

	fn steps(version: StorageVersion, cursor: &[u8], weight_left: &mut Weight) -> Option<Cursor>;

	fn integrity_test();

	fn is_upgrade_supported(in_storage: StorageVersion, target: StorageVersion) -> bool {
		if in_storage == target {
			return true
		}
		if in_storage > target {
			return false
		}
		let Some((low, high)) = Self::VERSION_RANGE else {
			return false
		};
		let Some(first_supported) = low.checked_sub(1) else {
			return false
		};
		in_storage == first_supported && target == high
	}
}

/// Performs all necessary migrations based on `StorageVersion`.
pub struct Migration<T: Config>(PhantomData<T>);

impl<T: Config> OnRuntimeUpgrade for Migration<T> {
	fn on_runtime_upgrade() -> Weight {
		let latest_version = <Pallet<T>>::current_storage_version();
		let storage_version = <Pallet<T>>::on_chain_storage_version();
		let mut weight = T::DbWeight::get().reads(1);

		if storage_version == latest_version {
			return weight
		}

		// In case a migration is already in progress we create the next migration
		// (if any) right when the current one finishes.
		weight.saturating_accrue(T::DbWeight::get().reads(1));
		if Self::in_progress() {
			return weight
		}

		log::info!(
			target: LOG_TARGET,
			"RuntimeUpgraded. Upgrading storage from {storage_version:?} to {latest_version:?}.",
		);

		let cursor = Migrations::<T>::new(storage_version + 1);
		MigrationInProgress::<T>::set(Some(cursor));
		weight.saturating_accrue(T::DbWeight::get().writes(1));

		weight
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		// We can't really do much here as our migrations do not happen during the runtime upgrade.
		// Instead, we call the migrations `pre_upgrade` and `post_upgrade` hooks when we iterate
		// over our migrations.
		let storage_version = <Pallet<T>>::on_chain_storage_version();
		let target_version = <Pallet<T>>::current_storage_version();
		if Migrations::<T>::is_upgrade_supported(storage_version, target_version) {
			Ok(Vec::new())
		} else {
			Err("New runtime does not contain the required migrations to perform this upgrade.")
		}
	}
}

impl<T: Config> Migration<T> {
	pub(crate) fn integrity_test() {
		Migrations::<T>::integrity_test()
	}

	pub(crate) fn migrate(weight_limit: Weight) -> Result<Weight, (Weight, DispatchError)> {
		let mut weight_left = weight_limit;

		// for mutating `MigrationInProgress` and `StorageVersion`
		weight_left
			.checked_reduce(T::DbWeight::get().reads_writes(2, 2))
			.ok_or_else(|| (0.into(), Error::<T>::NoMigrationPerformed.into()))?;

		MigrationInProgress::<T>::try_mutate_exists(|progress| {
			let cursor_before = progress.as_mut().ok_or_else(|| {
				(weight_limit.saturating_sub(weight_left), Error::<T>::NoMigrationPerformed.into())
			})?;

			// if a migration is running it is always upgrading to the next version
			let storage_version = <Pallet<T>>::on_chain_storage_version();
			let in_progress_version = storage_version + 1;

			*progress = match Migrations::<T>::steps(
				in_progress_version,
				cursor_before.as_ref(),
				&mut weight_left,
			) {
				// ongoing
				Some(cursor) => {
					// refund as we did not update the storage version
					weight_left.saturating_accrue(T::DbWeight::get().writes(1));
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
							"Started migrating to {:?},",
							in_progress_version + 1,
						);
						Some(Migrations::<T>::new(in_progress_version + 1))
					} else {
						// enable pallet by removing the storage item
						log::info!(
							target: LOG_TARGET,
							"All migrations done. At version {:?},",
							in_progress_version + 1,
						);
						None
					}
				},
			};

			Ok(weight_limit.saturating_sub(weight_left))
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
#[tuple_types_custom_trait_bound(Migrate<T>)]
impl<T: Config> MigrateSequence<T> for Tuple {
	const VERSION_RANGE: Option<(u16, u16)> = {
		let mut versions: Option<(u16, u16)> = None;
		for_tuples!(
			#(
				match versions {
					None => {
						versions = Some((Tuple::VERSION, Tuple::VERSION));
					},
					Some((min_version, last_version)) if Tuple::VERSION == last_version + 1 => {
						versions = Some((min_version, Tuple::VERSION));
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
		panic!("{PROOF_EXISTS}")
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
						weight_left.saturating_reduce(weight.unwrap_or(max_weight));
						if matches!(finished, IsFinished::Yes) {
							return None
						}
					}
					return Some(migration.encode().try_into().expect(PROOF_ENCODE))
				}
			)*
		);
		panic!("{PROOF_EXISTS}")
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
	use crate::tests::Test;

	#[test]
	fn check_versions() {
		// this fails the compilation when running local tests
		// otherwise it will only be evaluated when the whole runtime is build
		let _ = Migrations::<Test>::VERSION_RANGE;
	}
}
