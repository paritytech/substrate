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

//! Tests for VersionedRuntimeUpgrade

#![cfg(all(feature = "experimental", feature = "try-runtime"))]

use frame_support::{
	construct_runtime, derive_impl,
	migrations::VersionedRuntimeUpgrade,
	parameter_types,
	traits::{GetStorageVersion, OnRuntimeUpgrade, StorageVersion},
	weights::constants::RocksDbWeight,
};
use frame_system::Config;
use sp_core::ConstU64;
use sp_runtime::BuildStorage;

type Block = frame_system::mocking::MockBlock<Test>;

#[frame_support::pallet]
mod dummy_pallet {
	use frame_support::pallet_prelude::*;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::storage]
	pub type SomeStorage<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::genesis_config]
	#[derive(frame_support::DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		#[serde(skip)]
		_config: sp_std::marker::PhantomData<T>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {}
	}
}

impl dummy_pallet::Config for Test {}

construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>} = 0,
		DummyPallet: dummy_pallet::{Pallet, Config<T>, Storage} = 1,
	}
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type Block = Block;
	type BlockHashCount = ConstU64<10>;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let storage = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	let mut ext: sp_io::TestExternalities = sp_io::TestExternalities::from(storage);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

/// A dummy migration for testing the `VersionedRuntimeUpgrade` trait.
/// Sets SomeStorage to S.
struct SomeUnversionedMigration<T: Config, const S: u32>(sp_std::marker::PhantomData<T>);

parameter_types! {
	const UpgradeReads: u64 = 4;
	const UpgradeWrites: u64 = 2;
	const PreUpgradeReturnBytes: [u8; 4] = [0, 1, 2, 3];
	static PreUpgradeCalled: bool = false;
	static PostUpgradeCalled: bool = false;
	static PostUpgradeCalledWith: Vec<u8> = Vec::new();
}

/// Implement `OnRuntimeUpgrade` for `SomeUnversionedMigration`.
/// It sets SomeStorage to S, and returns a weight derived from UpgradeReads and UpgradeWrites.
impl<T: dummy_pallet::Config, const S: u32> OnRuntimeUpgrade for SomeUnversionedMigration<T, S> {
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		PreUpgradeCalled::set(true);
		Ok(PreUpgradeReturnBytes::get().to_vec())
	}

	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		dummy_pallet::SomeStorage::<T>::put(S);
		RocksDbWeight::get().reads_writes(UpgradeReads::get(), UpgradeWrites::get())
	}

	fn post_upgrade(state: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		PostUpgradeCalled::set(true);
		PostUpgradeCalledWith::set(state);
		Ok(())
	}
}

type VersionedMigrationV0ToV1 =
	VersionedRuntimeUpgrade<0, 1, SomeUnversionedMigration<Test, 1>, DummyPallet, RocksDbWeight>;

type VersionedMigrationV1ToV2 =
	VersionedRuntimeUpgrade<1, 2, SomeUnversionedMigration<Test, 2>, DummyPallet, RocksDbWeight>;

type VersionedMigrationV2ToV4 =
	VersionedRuntimeUpgrade<2, 4, SomeUnversionedMigration<Test, 4>, DummyPallet, RocksDbWeight>;

#[test]
fn successful_upgrade_path() {
	new_test_ext().execute_with(|| {
		// on-chain storage version and value in storage start at zero
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 0);

		// Execute the migration from version 0 to 1 and verify it was successful
		VersionedMigrationV0ToV1::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(1));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 1);

		// Execute the migration from version 1 to 2 and verify it was successful
		VersionedMigrationV1ToV2::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(2));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 2);

		// Execute the migration from version 2 to 4 and verify it was successful
		VersionedMigrationV2ToV4::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(4));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 4);
	});
}

#[test]
fn future_version_upgrade_is_ignored() {
	new_test_ext().execute_with(|| {
		// Executing V1 to V2 on V0 should be a noop
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 0);
		VersionedMigrationV1ToV2::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 0);
	});
}

#[test]
fn past_version_upgrade_is_ignored() {
	new_test_ext().execute_with(|| {
		// Upgrade to V2
		VersionedMigrationV0ToV1::on_runtime_upgrade();
		VersionedMigrationV1ToV2::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(2));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 2);

		// Now, V0 to V1 and V1 to V2 should both be noops
		dummy_pallet::SomeStorage::<Test>::put(1000);
		VersionedMigrationV0ToV1::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(2));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 1000);
		VersionedMigrationV1ToV2::on_runtime_upgrade();
		assert_eq!(DummyPallet::on_chain_storage_version(), StorageVersion::new(2));
		assert_eq!(dummy_pallet::SomeStorage::<Test>::get(), 1000);
	});
}

#[test]
fn weights_are_returned_correctly() {
	new_test_ext().execute_with(|| {
		// Successful upgrade requires 1 additional read and write
		let weight = VersionedMigrationV0ToV1::on_runtime_upgrade();
		assert_eq!(
			weight,
			RocksDbWeight::get().reads_writes(UpgradeReads::get() + 1, UpgradeWrites::get() + 1)
		);

		// Noop upgrade requires only 1 read
		let weight = VersionedMigrationV0ToV1::on_runtime_upgrade();
		assert_eq!(weight, RocksDbWeight::get().reads(1));
	});
}

#[test]
fn pre_and_post_checks_behave_correctly() {
	new_test_ext().execute_with(|| {
		// Check initial state
		assert_eq!(PreUpgradeCalled::get(), false);
		assert_eq!(PostUpgradeCalled::get(), false);
		assert_eq!(PostUpgradeCalledWith::get(), Vec::<u8>::new());

		// Check pre/post hooks are called correctly when upgrade occurs.
		VersionedMigrationV0ToV1::try_on_runtime_upgrade(true).unwrap();
		assert_eq!(PreUpgradeCalled::get(), true);
		assert_eq!(PostUpgradeCalled::get(), true);
		assert_eq!(PostUpgradeCalledWith::get(), PreUpgradeReturnBytes::get().to_vec());

		// Reset hook tracking state.
		PreUpgradeCalled::set(false);
		PostUpgradeCalled::set(false);

		// Check pre/post hooks are not called when an upgrade is skipped.
		VersionedMigrationV0ToV1::try_on_runtime_upgrade(true).unwrap();
		assert_eq!(PreUpgradeCalled::get(), false);
		assert_eq!(PostUpgradeCalled::get(), false);
	})
}
