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

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	defensive,
	migrations::*,
	traits::Get,
	weights::{Weight, WeightMeter},
};
use sp_runtime::Saturating;

const LOG_TARGET: &'static str = "runtime::migrations";

/// Points to the next migration to execute.
#[derive(Debug, Clone, Eq, PartialEq, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
pub enum MigrationCursor {
	/// Points to the currently active migration and its cursor.
	Active(u32, Option<SteppedMigrationCursor>),
	/// Migration got stuck and cannot proceed.
	Stuck,
}

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

		/// The weight to spend each block to execute migrations.
		type ServiceWeight: Get<Weight>;

		/// Weight information for the calls and functions of this pallet.
		type WeightInfo: WeightInfo;
	}

	/// The currently active migration to run and its cursor.
	///
	/// `None` indicates that no migration process is running.
	#[pallet::storage]
	pub type Cursor<T> = StorageValue<_, MigrationCursor, OptionQuery>;

	/// Set of all successfully executed migrations.
	///
	/// This is used as blacklist, to not re-execute migrations that have not been removed from the
	/// codebase yet.
	#[pallet::storage]
	pub type Executed<T> =
		StorageMap<_, Twox64Concat, BoundedVec<u8, ConstU32<32>>, (), OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Runtime upgrade started.
		UpgradeStarted,
		/// Runtime upgrade completed with `migrations`.
		UpgradeCompleted { migrations: u32 },
		/// Runtime upgrade failed.
		///
		/// This is very bad and will require governance intervention.
		UpgradeFailed,
		/// Migration `index` was skipped, since it already executed in the past.
		MigrationSkippedHistoric { index: u32 },
		/// Migration `index` made progress.
		MigrationAdvanced { index: u32 },
		/// Migration `index` completed.
		MigrationCompleted { index: u32 },
		/// Migration `index` failed.
		///
		/// This implies that the whole upgrade failed and governance intervention is required.
		MigrationFailed { index: u32 },
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			if Cursor::<T>::exists() {
				log::error!(target: LOG_TARGET, "Code for ongoing migrations was deleted.");
				Self::deposit_event(Event::UpgradeFailed);
				Cursor::<T>::set(Some(MigrationCursor::Stuck));
				return T::WeightInfo::on_runtime_upgrade()
			}

			if T::Migrations::get().len() > 0 {
				Cursor::<T>::set(Some(MigrationCursor::Active(0, None)));
				Self::deposit_event(Event::UpgradeStarted);
			}

			T::WeightInfo::on_runtime_upgrade()
		}

		fn on_initialize(n: T::BlockNumber) -> Weight {
			let mut meter = WeightMeter::from_limit(T::ServiceWeight::get());

			let (mut index, mut cursor) = match Cursor::<T>::get() {
				None => {
					log::debug!(target: LOG_TARGET, "[Block {n:?}] Waiting for cursor to become `Some`.");
					return meter.consumed
				},
				Some(MigrationCursor::Active(index, cursor)) => (index, cursor),
				Some(MigrationCursor::Stuck) => {
					defensive!("Migration stuck. Governance intervention required.");
					return meter.consumed
				},
			};
			debug_assert!(<Self as ExtrinsicSuspenderQuery>::is_suspended());

			let migrations = T::Migrations::get();
			for step in 0.. {
				let Some(migration) = migrations.get(index as usize) else {
					Self::deposit_event(Event::UpgradeCompleted { migrations: migrations.len() as u32 });
					Cursor::<T>::kill();
					return meter.consumed;
				};
				if Executed::<T>::contains_key(&migration.id()) {
					Self::deposit_event(Event::MigrationSkippedHistoric { index });
					index.saturating_inc();
					cursor = None;
					continue
				}

				match migration.transactional_step(cursor, &mut meter) {
					Ok(Some(next_cursor)) => {
						Self::deposit_event(Event::MigrationAdvanced { index });
						cursor = Some(next_cursor);
						// A migration has to make maximal progress per step, we therefore break.
						break
					},
					Ok(None) => {
						Self::deposit_event(Event::MigrationCompleted { index });
						Executed::<T>::insert(&migration.id(), ());
						index.saturating_inc();
						cursor = None;
					},
					Err(SteppedMigrationError::InsufficientWeight { required }) => {
						if step == 0 || required.any_gt(meter.limit) {
							Cursor::<T>::set(Some(MigrationCursor::Stuck));
							Self::deposit_event(Event::UpgradeFailed);
						} // else: Hope that it gets better next time.
						return meter.consumed
					},
					Err(SteppedMigrationError::Failed) => {
						Self::deposit_event(Event::MigrationFailed { index });
						Self::deposit_event(Event::UpgradeFailed);
						Cursor::<T>::set(Some(MigrationCursor::Stuck));
						return meter.consumed
					},
				}
			}

			Cursor::<T>::set(Some(MigrationCursor::Active(index, cursor)));

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
			cursor: Option<MigrationCursor>,
		) -> DispatchResult {
			ensure_root(origin)?;

			Cursor::<T>::set(cursor);

			Ok(())
		}
	}
}

impl<T: Config> ExtrinsicSuspenderQuery for Pallet<T> {
	fn is_suspended() -> bool {
		Cursor::<T>::exists()
	}
}
