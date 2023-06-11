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

use frame_support::{
	construct_runtime,
	migrations::VersionedRuntimeUpgrade,
	parameter_types,
	traits::{ConstU32, ConstU64, GetStorageVersion, OnRuntimeUpgrade, StorageVersion},
	weights::constants::RocksDbWeight,
};
use frame_system::Config;
use sp_core::{ConstU16, Get, H256};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

#[frame_support::pallet]
mod dummy_pallet {
	use frame_support::pallet_prelude::*;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::storage]
	pub type SomeStorage<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::event]
	pub enum Event<T: Config> {}

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig {}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {}
	}
}

impl dummy_pallet::Config for Test {
	type RuntimeEvent = RuntimeEvent;
}

construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>} = 0,
		DummyPallet: dummy_pallet::{Pallet, Config, Storage, Event<T>} = 1,
	}
);

type AccountId = u64;

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<3>;
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let storage = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let mut ext: sp_io::TestExternalities = sp_io::TestExternalities::from(storage);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

/// A dummy migration for testing the `VersionedRuntimeUpgrade` trait.
/// Sets SomeStorage to S.
struct SomeUnversionedMigration<T: Config, S: Get<u32>>(sp_std::marker::PhantomData<(T, S)>);

parameter_types! {
	const UpgradeReads: u64 = 4;
	const UpgradeWrites: u64 = 2;
}

/// Implement `OnRuntimeUpgrade` for `SomeUnversionedMigration`.
/// It sets SomeStorage to S, and returns a weight derived from UpgradeReads and UpgradeWrites.
impl<T: dummy_pallet::Config, S: Get<u32>> OnRuntimeUpgrade for SomeUnversionedMigration<T, S> {
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		// This is a dummy migration that just sets the storage version to 4.
		// It is used to test the `VersionedRuntimeUpgrade` trait.
		dummy_pallet::SomeStorage::<T>::put(S::get());
		RocksDbWeight::get().reads_writes(UpgradeReads::get(), UpgradeWrites::get())
	}
}

type VersionedMigrationV0ToV1 = VersionedRuntimeUpgrade<
	ConstU16<0>,
	ConstU16<1>,
	SomeUnversionedMigration<Test, ConstU32<1>>,
	DummyPallet,
	RocksDbWeight,
>;

type VersionedMigrationV1ToV2 = VersionedRuntimeUpgrade<
	ConstU16<1>,
	ConstU16<2>,
	SomeUnversionedMigration<Test, ConstU32<2>>,
	DummyPallet,
	RocksDbWeight,
>;

type VersionedMigrationV2ToV4 = VersionedRuntimeUpgrade<
	ConstU16<2>,
	ConstU16<4>,
	SomeUnversionedMigration<Test, ConstU32<4>>,
	DummyPallet,
	RocksDbWeight,
>;

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
