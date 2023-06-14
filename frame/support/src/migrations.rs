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

#[cfg(feature = "try-runtime")]
use crate::storage::unhashed::contains_prefixed_key;
use crate::{
	storage::transactional::with_transaction_opaque_err,
	traits::{GetStorageVersion, NoStorageVersionSet, PalletInfoAccess, StorageVersion},
	weights::{RuntimeDbWeight, Weight, WeightMeter},
};
use codec::{Decode, Encode, MaxEncodedLen};
use impl_trait_for_tuples::impl_for_tuples;
use sp_core::Get;
use sp_io::{hashing::twox_128, storage::clear_prefix, KillStorageResult};
use sp_std::marker::PhantomData;
#[cfg(feature = "try-runtime")]
use sp_std::vec::Vec;

/// Can store the current pallet version in storage.
pub trait StoreCurrentStorageVersion<T: GetStorageVersion + PalletInfoAccess> {
	/// Write the current storage version to the storage.
	fn store_current_storage_version();
}

impl<T: GetStorageVersion<CurrentStorageVersion = StorageVersion> + PalletInfoAccess>
	StoreCurrentStorageVersion<T> for StorageVersion
{
	fn store_current_storage_version() {
		let version = <T as GetStorageVersion>::current_storage_version();
		version.put::<T>();
	}
}

impl<T: GetStorageVersion<CurrentStorageVersion = NoStorageVersionSet> + PalletInfoAccess>
	StoreCurrentStorageVersion<T> for NoStorageVersionSet
{
	fn store_current_storage_version() {
		StorageVersion::default().put::<T>();
	}
}

/// Trait used by [`migrate_from_pallet_version_to_storage_version`] to do the actual migration.
pub trait PalletVersionToStorageVersionHelper {
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight;
}

impl<T: GetStorageVersion + PalletInfoAccess> PalletVersionToStorageVersionHelper for T
where
	T::CurrentStorageVersion: StoreCurrentStorageVersion<T>,
{
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight {
		const PALLET_VERSION_STORAGE_KEY_POSTFIX: &[u8] = b":__PALLET_VERSION__:";

		fn pallet_version_key(name: &str) -> [u8; 32] {
			crate::storage::storage_prefix(name.as_bytes(), PALLET_VERSION_STORAGE_KEY_POSTFIX)
		}

		sp_io::storage::clear(&pallet_version_key(<T as PalletInfoAccess>::name()));

		<T::CurrentStorageVersion as StoreCurrentStorageVersion<T>>::store_current_storage_version(
		);

		db_weight.writes(2)
	}
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl PalletVersionToStorageVersionHelper for T {
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight {
		let mut weight = Weight::zero();

		for_tuples!( #( weight = weight.saturating_add(T::migrate(db_weight)); )* );

		weight
	}
}

/// Migrate from the `PalletVersion` struct to the new
/// [`StorageVersion`](crate::traits::StorageVersion) struct.
///
/// This will remove all `PalletVersion's` from the state and insert the current storage version.
pub fn migrate_from_pallet_version_to_storage_version<
	Pallets: PalletVersionToStorageVersionHelper,
>(
	db_weight: &RuntimeDbWeight,
) -> Weight {
	Pallets::migrate(db_weight)
}

/// `RemovePallet` is a utility struct used to remove all storage items associated with a specific
/// pallet.
///
/// This struct is generic over two parameters:
/// - `P` is a type that implements the `Get` trait for a static string, representing the pallet's
///   name.
/// - `DbWeight` is a type that implements the `Get` trait for `RuntimeDbWeight`, providing the
///   weight for database operations.
///
/// On runtime upgrade, the `on_runtime_upgrade` function will clear all storage items associated
/// with the specified pallet, logging the number of keys removed. If the `try-runtime` feature is
/// enabled, the `pre_upgrade` and `post_upgrade` functions can be used to verify the storage
/// removal before and after the upgrade.
///
/// # Examples:
/// ```ignore
/// construct_runtime! {
/// 	pub enum Runtime where
/// 		Block = Block,
/// 		NodeBlock = primitives::Block,
/// 		UncheckedExtrinsic = UncheckedExtrinsic
/// 	{
/// 		System: frame_system::{Pallet, Call, Storage, Config, Event<T>} = 0,
///
/// 		SomePalletToRemove: pallet_something::{Pallet, Call, Storage, Event<T>} = 1,
/// 		AnotherPalletToRemove: pallet_something_else::{Pallet, Call, Storage, Event<T>} = 2,
///
/// 		YourOtherPallets...
/// 	}
/// };
///
/// parameter_types! {
/// 		pub const SomePalletToRemoveStr: &'static str = "SomePalletToRemove";
/// 		pub const AnotherPalletToRemoveStr: &'static str = "AnotherPalletToRemove";
/// }
///
/// pub type Migrations = (
/// 	RemovePallet<SomePalletToRemoveStr, RocksDbWeight>,
/// 	RemovePallet<AnotherPalletToRemoveStr, RocksDbWeight>,
/// 	AnyOtherMigrations...
/// );
///
/// pub type Executive = frame_executive::Executive<
/// 	Runtime,
/// 	Block,
/// 	frame_system::ChainContext<Runtime>,
/// 	Runtime,
/// 	Migrations
/// >;
/// ```
///
/// WARNING: `RemovePallet` has no guard rails preventing it from bricking the chain if the
/// operation of removing storage for the given pallet would exceed the block weight limit.
///
/// If your pallet has too many keys to be removed in a single block, it is advised to wait for
/// a multi-block scheduler currently under development which will allow for removal of storage
/// items (and performing other heavy migrations) over multiple blocks
/// (see <https://github.com/paritytech/substrate/issues/13690>).
pub struct RemovePallet<P: Get<&'static str>, DbWeight: Get<RuntimeDbWeight>>(
	PhantomData<(P, DbWeight)>,
);
impl<P: Get<&'static str>, DbWeight: Get<RuntimeDbWeight>> frame_support::traits::OnRuntimeUpgrade
	for RemovePallet<P, DbWeight>
{
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		let hashed_prefix = twox_128(P::get().as_bytes());
		let keys_removed = match clear_prefix(&hashed_prefix, None) {
			KillStorageResult::AllRemoved(value) => value,
			KillStorageResult::SomeRemaining(value) => {
				log::error!(
					"`clear_prefix` failed to remove all keys for {}. THIS SHOULD NEVER HAPPEN! 🚨",
					P::get()
				);
				value
			},
		} as u64;

		log::info!("Removed {} {} keys 🧹", keys_removed, P::get());

		DbWeight::get().reads_writes(keys_removed + 1, keys_removed)
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		let hashed_prefix = twox_128(P::get().as_bytes());
		match contains_prefixed_key(&hashed_prefix) {
			true => log::info!("Found {} keys pre-removal 👀", P::get()),
			false => log::warn!(
				"Migration RemovePallet<{}> can be removed (no keys found pre-removal).",
				P::get()
			),
		};
		Ok(Vec::new())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(_state: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		let hashed_prefix = twox_128(P::get().as_bytes());
		match contains_prefixed_key(&hashed_prefix) {
			true => {
				log::error!("{} has keys remaining post-removal ❗", P::get());
				return Err("Keys remaining post-removal, this should never happen 🚨".into())
			},
			false => log::info!("No {} keys found post-removal 🎉", P::get()),
		};
		Ok(())
	}
}

/// A migration that can proceed in multiple steps.
pub trait SteppedMigration {
	/// The cursor type that stores the progress (aka. state) of this migration.
	type Cursor: codec::FullCodec + codec::MaxEncodedLen;

	/// The unique identifier type of this migration.
	type Identifier: codec::FullCodec + codec::MaxEncodedLen;

	/// The unique identifier of this migration.
	///
	/// If two migrations have the same identifier, then they are assumed to be identical.
	fn id(&self) -> Self::Identifier;

	/// The maximum number of steps that this migration can take at most.
	///
	/// This can be used to enforce progress and prevent migrations to be stuck forever. A migration
	/// that exceeds its max steps is treated as failed. `None` means that there is no limit.
	fn max_steps(&self) -> Option<u32> {
		None
	}

	/// Try to migrate as much as possible with the given weight.
	///
	/// **ANY STORAGE CHANGES MUST BE ROLLED-BACK BY THE CALLER UPON ERROR.** This is necessary
	/// since the caller cannot return a cursor in the error case. `Self::transactional_step` is
	/// provided as convenience for a caller. A cursor of `None` implies that the migration is at
	/// its end. TODO: Think about iterator `fuse` requirement.
	fn step(
		&self,
		cursor: &Option<Self::Cursor>,
		meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError>;

	/// Same as [`Self::step`], but rolls back pending changes in the error case.
	fn transactional_step(
		&self,
		mut cursor: Option<Self::Cursor>,
		meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		with_transaction_opaque_err(move || match self.step(&cursor, meter) {
			Ok(new_cursor) => {
				cursor = new_cursor;
				sp_api::TransactionOutcome::Commit(Ok(cursor))
			},
			Err(err) => sp_api::TransactionOutcome::Rollback(Err(err)),
		})
		.map_err(|()| SteppedMigrationError::Failed)?
	}
}

#[derive(Debug, Encode, Decode, MaxEncodedLen, scale_info::TypeInfo)]
pub enum SteppedMigrationError {
	// Transient errors:
	/// The remaining weight is not enough to do anything.
	///
	/// Can be resolved by calling with at least `required` weight. Note that calling it with
	/// exactly `required` weight could cause it to not make any progress.
	InsufficientWeight { required: Weight },
	// Permanent errors:
	/// The migration cannot decode its cursor and therefore not proceed.
	///
	/// This should not happen unless (1) the migration itself returned an invalid cursor in a
	/// previous iteration, (2) the storage got corrupted or (3) there is a bug in the caller's
	/// code.
	InvalidCursor,
	/// The migration encountered a permanent error and cannot continue.
	Failed,
}

/// Notification handler for status updates regarding runtime upgrades.
pub trait OnMigrationUpdate {
	/// Notifies of the start of a runtime upgrade.
	fn started() {}

	/// Notifies of the completion of a runtime upgrade.
	fn completed() {}

	/// Infallibly handle a failed runtime upgrade.
	///
	/// Gets passed in the optional index of the migration that caused the failure.
	fn failed(migration: Option<u32>) -> FailedUpgradeHandling;
}

/// How to proceed after a runtime upgrade failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailedUpgradeHandling {
	/// Resume extrinsic processing of the chain. This will not resume the upgrade.
	///
	/// This should be supplemented with additional measures to ensure that the broken chain state
	/// does not get further messed up by user extrinsics.
	ForceUnstuck,
	/// Do nothing and keep blocking extrinsics.
	KeepStuck,
}

impl OnMigrationUpdate for () {
	fn failed(_migration: Option<u32>) -> FailedUpgradeHandling {
		FailedUpgradeHandling::KeepStuck
	}
}

/// Something that can do multi step migrations.
pub trait MultiStepMigrator {
	fn is_upgrading() -> bool;
	/// Do the next step in the MBM process.
	fn step() -> Weight;
}

impl MultiStepMigrator for () {
	fn is_upgrading() -> bool {
		false
	}

	fn step() -> Weight {
		Weight::zero()
	}
}
