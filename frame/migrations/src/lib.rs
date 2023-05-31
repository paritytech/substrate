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

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

mod benchmarking;
mod mock;
mod tests;
pub mod weights;

pub use weights::WeightInfo;

use frame_support::{
	defensive,
	migrations::*,
	traits::{ConstU32, Get},
	weights::{Weight, WeightMeter},
	BoundedVec,
};

const LOG_TARGET: &'static str = "runtime::migrations";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_std::{boxed::Box, vec::Vec};

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// All the multi-block migrations to run.
		///
		/// Should only be updated in a runtime-upgrade once all the old ones have completed. (Check
		/// `Cursor` for `None`).
		type Migrations: Get<Vec<Box<dyn SteppedMigration>>>;

		type Suspender: ExtrinsicSuspender + ExtrinsicSuspenderQuery;

		/// The weight to spend each block to execute migrations.
		type ServiceWeight: Get<Weight>;

		type WeightInfo: WeightInfo;
	}

	/// The currently active migration to run and its cursor.
	///
	/// `None` indicates that no migration process is running.
	#[pallet::storage]
	pub type Cursor<T> = StorageValue<_, (u32, SteppedMigrationCursor), OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Runtime upgrade started.
		UpgradeStarted,
		/// Runtime upgrade completed with `migrations`.
		UpgradeCompleted { migrations: u32 },
		/// Migration `index` made progress.
		MigrationAdvanced { index: u32 },
		/// Migration `index` completed.
		MigrationCompleted { index: u32 },
		/// Migration `index` failed. TODO add `inner` error
		MigrationFailed { index: u32 },
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			if Cursor::<T>::exists() {
				log::error!(target: LOG_TARGET, "Defensive: migrations in progress will be aborted.");
				return Default::default() // FAIL-CI
			}
			Cursor::<T>::set(Some(Default::default()));
			Self::deposit_event(Event::UpgradeStarted);

			Default::default() // FAIL-CI
		}

		fn on_initialize(n: T::BlockNumber) -> Weight {
			let mut meter = WeightMeter::from_limit(T::ServiceWeight::get());

			let Some((index, inner_cursor)) = Cursor::<T>::get() else {
				log::debug!(target: LOG_TARGET, "[Block {n:?}] Nothing to do: waiting for cursor to become `Some`.");
				return meter.consumed;
			};
			let migrations = T::Migrations::get();

			let Some(migration) = migrations.get(index as usize) else {
				Cursor::<T>::kill();
				Self::deposit_event(Event::UpgradeCompleted { migrations: migrations.len() as u32 });
				return meter.consumed;
			};

			match migration.transactional_step(Some(inner_cursor), &mut meter) {
				Ok(Some(inner_cursor)) => {
					Cursor::<T>::set(Some((index, inner_cursor)));
					Self::deposit_event(Event::MigrationAdvanced { index });
				},
				Ok(None) => {
					Cursor::<T>::set(Some((index.saturating_add(1), Default::default())));
					Self::deposit_event(Event::MigrationCompleted { index });
				},
				Err(err) => {
					Cursor::<T>::kill();
					// TODO: handle errors
					Cursor::<T>::set(Some((index.saturating_add(1), Default::default())));
					Self::deposit_event(Event::MigrationFailed { index });
				},
			}

			meter.consumed
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Allows root to set the cursor to any value.
		///
		/// Should normally not be needed and is only in place as emergency measure.
		#[pallet::call_index(0)]
		#[pallet::weight((0, DispatchClass::Mandatory))]
		pub fn force_set_cursor(
			origin: OriginFor<T>,
			cursor: Option<(u32, SteppedMigrationCursor)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			Cursor::<T>::set(cursor);

			Ok(())
		}
	}
}
