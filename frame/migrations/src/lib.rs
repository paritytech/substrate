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

#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

//! # `pallet-migrations`
//!
//! Provides multi block migrations for FRAME runtimes.
//!
//! ## Overview
//!
//! The pallet takes care of executing a batch of multi-step migrations over multiple blocks. The
//! process starts on each runtime upgrade. Normal and operational transactions are paused while
//! migrations are on-going.
//!
//! ### Example
//!
//! This example demonstrates a simple mocked walk through of a basic success scenario. The pallet
//! is configured with two migrations: one succeeding after just one step, and the second one
//! succeeding after two steps. A runtime upgrade is then enacted and the block number is advanced
//! until all migrations finish executing. Afterwards, the recorded historic migrations are
//! checked and events are asserted.
#![doc = docify::embed!("frame/migrations/src/tests.rs", simple_works)]
//!
//! ## Pallet API
//!
//! See the [`pallet`] module for more information about the interfaces this pallet exposes,
//! including its configuration trait, dispatchables, storage items, events and errors.
//!
//! Otherwise noteworthy API of this pallet include its implementation of the
//! [`ExtrinsicSuspenderQuery`] trait. This can be plugged into `frame-executive` to check for
//! transaction suspension.
//!
//! ### Design Goals
//!
//! 1. Must automatically execute migrations over multiple blocks.
//! 2. Must prevent other (non-mandatory) transactions to execute in the meantime.
//! 3. Must respect pessimistic weight bounds of migrations.
//! 4. Must execute migrations in order. Skipping is not allowed; migrations are run on an
//! all-or-nothing basis. 5. Must prevent re-execution of migrations.
//! 6. Must provide transactional storage semantics for migrations.
//! 7. Must guarantee progress.
//!
//! ### Design
//!
//! Migrations are provided to the pallet through the associated type [`Config::Migrations`] of type
//! `Get<Vec<Box<dyn SteppedMigration<…`. This was done to have the most flexibility when it comes
//! to iterating and inspecting the migrations. It also simplifies the trait bounds since all
//! associated types of the trait must be provided by the pallet.  
//! The actual progress of the pallet is stored in its [`Cursor`] storage item. This can either be
//! [`MigrationCursor::Active`] or `Stuck`. In the active case it points to the currently active
//! migration and stores its inner cursor. The inner cursor can then be used by the migration to
//! store its inner state and advance. Each time when the migration returns `Some(cursor)`, it
//! signals the pallet that it is not done yet.   
//! The cursor is re-set on each runtime upgrade. This ensures that it starts to execute at the
//! first migration in the vector. The pallets cursor is only ever incremented or put into `Stuck`
//! once it encounters an error (Goal 4). Once in the stuck state, the pallet will stay stuck until
//! it is fixed through manual governance intervention.  
//! As soon as the cursor of the pallet becomes `Some(_)`; chain transaction processing is paused
//! by [`ExtrinsicSuspenderQuery::is_suspended`] returning `true`. This ensures that no other
//! transactions are processed until all migrations are complete (Goal 2).  
//! `on_initialize` the pallet will load the current migration and check whether it was already
//! executed in the past by checking for membership of its ID in the `Historic` set. Historic
//! migrations are skipped without causing an error. Each successfully executed migration is added
//! to this set (Goal 5).  
//! This proceeds until no more migrations remain. At that point, the event `UpgradeCompleted` is
//! emitted (Goal 1).  
//! The execution of each migration happens by calling [`SteppedMigration::transactional_step`].
//! This function wraps the inner `step` function into a transactional layer to allow rollback in
//! the error case (Goal 6).  
//! Weight limits must be checked by the migration itself. The pallet provides a [`WeightMeter`] for
//! that purpose. The pallet may return [`SteppedMigrationError::InsufficientWeight`] at any point.
//! In that scenario, the one of two things will happen: if that migration was exclusively executed
//! in this block, and therefore required more than the maximum amount of weight possible, the
//! pallet becomes `Stuck`. Otherwise one re-attempt is attempted with the same logic in the next
//! block (Goal 3). Progress through the migrations is guaranteed by providing a timeout for each
//! migration via [`SteppedMigration::max_steps`]. The pallet **ONLY** guarantees progress if this
//! is set to sensible limits (Goal 7).
//!
//! ### Scenario: Governance cleanup
//!
//! Every now and then, governance can make use of the [`clear_historic`][Pallet::clear_historic]
//! call. This ensures that no old migrations pile up in the [`Historic`] set. This can probably be
//! done very rarely, since the storage should not grow quickly and the lookup weight does not
//! suffer much.
//!
//! ### Scenario: Successful upgrade
//!
//! The standard procedure for a successful runtime upgrade can look like this:
//! 1. Migrations are configured in the `Migrations` config item. All migrations expose
//! [`max_steps`][SteppedMigration::max_steps], are error tolerant, check their weight bounds and
//! have a unique identifier. 2. The runtime upgrade is enacted. `UpgradeStarted` events are
//! followed by lots of `MigrationAdvanced` events. Finally `UpgradeCompleted` is emitted.  
//! 3. Cleanup as described in the governance scenario be executed at any time after the migration
//! completes.
//!
//! ### Advice: Failed upgrades
//!
//! Failed upgrades cannot recovered from automatically and require governance intervention. Set up
//! monitoring for `UpgradeFailed` events to be made aware of any failures. The hook
//! [`OnMigrationUpdate::failed`] should be setup in a way that it allows governance to act, but
//! still prevent other transactions from interacting with the inconsistent storage state. Note that
//! this is paramount, since the inconsistent state might contain a faulty balance amount or similar
//! that could cause great harm if user transactions don't remain suspended. One way to implement
//! this would be to use the `SafeMode` or `TxPause` pallets that can prevent most user interactions
//! but still allow a whitelisted set of governance calls.
//!
//! ### Remark: Failed migrations
//!
//! Failed migrations are not added to the `Historic` set. This means that an erroneous
//! migration must be removed and fixed manually. This already applies, even before considering the
//! historic set.
//!
//! ### Remark: Transactional processing
//!
//! You can see the transactional semantics for migrational steps as mostly useless, since in the
//! stuck case the state is already messed up. This just prevents it from becoming even more messed
//! up , but doesn't prevent it in the first place.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod mock;
mod tests;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

use codec::{Decode, Encode, FullCodec, MaxEncodedLen};
use core::ops::ControlFlow;
use frame_support::{
	dispatch::DispatchClass,
	migrations::*,
	traits::Get,
	weights::{Weight, WeightMeter},
};
use frame_system::Pallet as System;
use sp_runtime::Saturating;
use sp_std::{boxed::Box, vec::Vec};

const LOG: &'static str = "runtime::migrations";

/// Points to the next migration to execute.
#[derive(Debug, Clone, Eq, PartialEq, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
pub enum MigrationCursor<Cursor, BlockNumber> {
	/// Points to the currently active migration and its cursor.
	Active(ActiveCursor<Cursor, BlockNumber>),
	/// Migration got stuck and cannot proceed.
	Stuck,
}

impl<Cursor, BlockNumber> MigrationCursor<Cursor, BlockNumber> {
	/// Maybe return self as an `ActiveCursor`.
	pub fn as_active(&self) -> Option<&ActiveCursor<Cursor, BlockNumber>> {
		match self {
			MigrationCursor::Active(active) => Some(active),
			MigrationCursor::Stuck => None,
		}
	}
}

impl<Cursor, BlockNumber> From<ActiveCursor<Cursor, BlockNumber>>
	for MigrationCursor<Cursor, BlockNumber>
{
	fn from(active: ActiveCursor<Cursor, BlockNumber>) -> Self {
		MigrationCursor::Active(active)
	}
}

/// Points to the currently active migration and its inner cursor.
#[derive(Debug, Clone, Eq, PartialEq, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
pub struct ActiveCursor<Cursor, BlockNumber> {
	index: u32,
	inner_cursor: Option<Cursor>,
	started_at: BlockNumber,
}

impl<Cursor, BlockNumber> ActiveCursor<Cursor, BlockNumber> {
	/// Advance the cursor to the next migration.
	pub(crate) fn advance(&mut self, current_block: BlockNumber) {
		self.index.saturating_inc();
		self.inner_cursor = None;
		self.started_at = current_block;
	}
}

/// A collection of migrations that must be executed in order.
pub type MigrationsOf<T> = Vec<
	Box<
		dyn SteppedMigration<
			Cursor = <T as Config>::Cursor,
			Identifier = <T as Config>::Identifier,
		>,
	>,
>;

/// Convenience alias for [`MigrationCursor`].
pub type CursorOf<T> =
	MigrationCursor<<T as Config>::Cursor, <T as frame_system::Config>::BlockNumber>;

/// Convenience alias for [`ActiveCursor`].
pub type ActiveCursorOf<T> =
	ActiveCursor<<T as Config>::Cursor, <T as frame_system::Config>::BlockNumber>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type of the runtime.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// All the multi-block migrations to run.
		///
		/// Should only be updated in a runtime-upgrade once all the old migrations have completed.
		/// (Check that `Cursor` is `None`).
		type Migrations: Get<MigrationsOf<Self>>;

		/// The cursor type that is shared across all migrations.
		type Cursor: FullCodec + MaxEncodedLen + TypeInfo + Parameter;

		/// The identifier type that is shared across all migrations.
		type Identifier: FullCodec + MaxEncodedLen + TypeInfo;

		/// Notifications for status updates of a runtime upgrade.
		///
		/// Can be used to pause XCM etc.
		type OnMigrationUpdate: OnMigrationUpdate;

		/// The weight to spend each block to execute migrations.
		type ServiceWeight: Get<Weight>;

		/// Weight information for the calls and functions of this pallet.
		type WeightInfo: WeightInfo;
	}

	/// The currently active migration to run and its cursor.
	///
	/// `None` indicates that no migration is running.
	#[pallet::storage]
	pub type Cursor<T: Config> = StorageValue<_, CursorOf<T>, OptionQuery>;

	/// Set of all successfully executed migrations.
	///
	/// This is used as blacklist, to not re-execute migrations that have not been removed from the
	/// codebase yet. Governance can regularly clear this out via `clear_historic`.
	#[pallet::storage]
	pub type Historic<T: Config> = StorageMap<_, Twox64Concat, T::Identifier, (), OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A Runtime upgrade started.
		///
		/// Its end is indicated by `UpgradeCompleted` or `UpgradeFailed`.
		UpgradeStarted {
			/// The number of migrations that this upgrade contains.
			///
			/// This can be used to design a progress indicator in combination with counting the
			/// `MigrationCompleted` and `MigrationSkippedHistoric` events.
			migrations: u32,
		},
		/// The current runtime upgrade completed.
		///
		/// This implies that all of its migrations completed successfully as well.
		UpgradeCompleted,
		/// Runtime upgrade failed.
		///
		/// This is very bad and will require governance intervention.
		UpgradeFailed,
		/// A migration was skipped since it was already executed in the past.
		MigrationSkippedHistoric {
			/// The index of the skipped migration within the [`Config::Migrations`] list.
			index: u32,
		},
		/// A migration progressed.
		MigrationAdvanced {
			/// The index of the migration within the [`Config::Migrations`] list.
			index: u32,
			/// The number of blocks that elapsed since the migration started.
			blocks: T::BlockNumber,
		},
		/// A Migration completed.
		MigrationCompleted {
			/// The index of the migration within the [`Config::Migrations`] list.
			index: u32,
			/// The number of blocks that elapsed since the migration started.
			blocks: T::BlockNumber,
		},
		/// A Migration failed.
		///
		/// This implies that the whole upgrade failed and governance intervention is required.
		MigrationFailed {
			/// The index of the migration within the [`Config::Migrations`] list.
			index: u32,
			/// The number of blocks that elapsed since the migration started.
			blocks: T::BlockNumber,
		},
		/// The set of historical migrations has been cleared.
		HistoricCleared {
			/// Should be passed to `clear_historic` in a successive call.
			next_cursor: Option<Vec<u8>>,
		},
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			Self::onboard_new_mbms()
		}

		fn on_initialize(n: T::BlockNumber) -> Weight {
			Self::progress_mbms(n)
		}
	}

	#[pallet::call(weight = T::WeightInfo)]
	impl<T: Config> Pallet<T> {
		/// Allows root to set the cursor to any value.
		///
		/// Should normally not be needed and is only in place as emergency measure.
		#[pallet::call_index(0)]
		pub fn force_set_cursor(
			origin: OriginFor<T>,
			cursor: Option<MigrationCursor<T::Cursor, T::BlockNumber>>,
		) -> DispatchResult {
			ensure_root(origin)?;

			Cursor::<T>::set(cursor);

			Ok(())
		}

		/// Clears the `Historic` set.
		///
		/// `map_cursor` must be set to the last value that was returned by the
		/// `HistoricCleared` event. The first time `None` can be used. `limit` must be chosen in a
		/// way that will result in a sensible weight.
		#[pallet::call_index(1)]
		#[pallet::weight({0})] // FAIL-CI
		pub fn clear_historic(
			origin: OriginFor<T>,
			limit: Option<u32>,
			map_cursor: Option<Vec<u8>>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let next = Historic::<T>::clear(limit.unwrap_or_default(), map_cursor.as_deref());
			Self::deposit_event(Event::HistoricCleared { next_cursor: next.maybe_cursor });

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Onboard all new Multi-Block-Migrations and start the process of executing them.
	///
	/// Should only be called once all previous migrations completed.
	fn onboard_new_mbms() -> Weight {
		if let Some(cursor) = Cursor::<T>::get() {
			log::error!(target: LOG, "Ongoing migrations interrupted - chain stuck");

			let maybe_index = cursor.as_active().map(|c| c.index);
			Self::upgrade_failed(maybe_index);
			return T::WeightInfo::on_runtime_upgrade()
		}

		let migrations = T::Migrations::get().len() as u32;
		if migrations > 0 {
			Cursor::<T>::set(Some(
				ActiveCursor {
					index: 0,
					inner_cursor: None,
					started_at: System::<T>::block_number(),
				}
				.into(),
			));
			Self::deposit_event(Event::UpgradeStarted { migrations });
			T::OnMigrationUpdate::started();
		}

		T::WeightInfo::on_runtime_upgrade()
	}

	/// Tries to make progress on the Multi-Block-Migrations process.
	fn progress_mbms(n: T::BlockNumber) -> Weight {
		let mut meter = WeightMeter::from_limit(T::ServiceWeight::get());
		meter.defensive_saturating_accrue(T::WeightInfo::on_init_base());

		let mut cursor = match Cursor::<T>::get() {
			None => {
				log::trace!(target: LOG, "[Block {n:?}] Waiting for cursor to become `Some`.");
				return meter.consumed
			},
			Some(MigrationCursor::Active(cursor)) => cursor,
			Some(MigrationCursor::Stuck) => {
				log::error!(target: LOG, "Migration stuck. Governance intervention required.");
				return meter.consumed
			},
		};
		debug_assert!(<Self as ExtrinsicSuspenderQuery>::is_suspended(DispatchClass::Normal));

		let migrations = T::Migrations::get();
		for i in 0.. {
			match Self::exec_migration(&mut meter, &migrations, cursor, i == 0) {
				None => return meter.consumed,
				Some(ControlFlow::Break(last_cursor)) => {
					cursor = last_cursor;
					break
				},
				Some(ControlFlow::Continue(next_cursor)) => {
					cursor = next_cursor;
				},
			}
		}

		Cursor::<T>::set(Some(cursor.into()));

		meter.consumed
	}

	/// Try to make progress on the current migration.
	///
	/// Returns whether processing should continue or break for this block. The `meter` contains the
	/// remaining weight that can be consumed.
	fn exec_migration(
		meter: &mut WeightMeter,
		migrations: &MigrationsOf<T>,
		mut cursor: ActiveCursorOf<T>,
		is_first: bool,
	) -> Option<ControlFlow<ActiveCursorOf<T>, ActiveCursorOf<T>>> {
		let Some(migration) = migrations.get(cursor.index as usize) else {
			Self::deposit_event(Event::UpgradeCompleted);
			Cursor::<T>::kill();
			T::OnMigrationUpdate::completed();
			return None;
		};
		if Historic::<T>::contains_key(&migration.id()) {
			Self::deposit_event(Event::MigrationSkippedHistoric { index: cursor.index });
			cursor.advance(System::<T>::block_number());
			return Some(ControlFlow::Continue(cursor))
		}

		let blocks = System::<T>::block_number().saturating_sub(cursor.started_at);
		match migration.transactional_step(cursor.inner_cursor.clone(), meter) {
			Ok(Some(next_cursor)) => {
				Self::deposit_event(Event::MigrationAdvanced { index: cursor.index, blocks });
				cursor.inner_cursor = Some(next_cursor);

				// We only progress one step per block.
				if migration.max_steps().map_or(false, |max| blocks > max.into()) {
					Self::deposit_event(Event::MigrationFailed { index: cursor.index, blocks });
					Self::upgrade_failed(Some(cursor.index));
					None
				} else {
					// A migration cannot progress more than one step per block, we therefore break.
					Some(ControlFlow::Break(cursor))
				}
			},
			Ok(None) => {
				Self::deposit_event(Event::MigrationCompleted { index: cursor.index, blocks });
				Historic::<T>::insert(&migration.id(), ());
				cursor.advance(System::<T>::block_number());
				return Some(ControlFlow::Continue(cursor))
			},
			Err(SteppedMigrationError::InsufficientWeight { required }) => {
				if !is_first || required.any_gt(meter.limit) {
					Self::deposit_event(Event::MigrationFailed { index: cursor.index, blocks });
					Self::upgrade_failed(Some(cursor.index));
					None
				} else {
					// else: Hope that it gets better in the next block.
					Some(ControlFlow::Continue(cursor))
				}
			},
			Err(SteppedMigrationError::InvalidCursor | SteppedMigrationError::Failed) => {
				Self::deposit_event(Event::MigrationFailed { index: cursor.index, blocks });
				Self::upgrade_failed(Some(cursor.index));
				return None
			},
		}
	}

	/// Fail the current runtime upgrade.
	fn upgrade_failed(migration: Option<u32>) {
		use FailedUpgradeHandling::*;
		Self::deposit_event(Event::UpgradeFailed);

		match T::OnMigrationUpdate::failed(migration) {
			KeepStuck => Cursor::<T>::set(Some(MigrationCursor::Stuck)),
			ForceUnstuck => Cursor::<T>::kill(),
		}
	}
}

impl<T: Config> ExtrinsicSuspenderQuery for Pallet<T> {
	fn is_suspended(class: DispatchClass) -> bool {
		match class {
			DispatchClass::Mandatory => false,
			DispatchClass::Normal | DispatchClass::Operational => Cursor::<T>::exists(),
		}
	}
}
