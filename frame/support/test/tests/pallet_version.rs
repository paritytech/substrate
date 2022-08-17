// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Tests related to the pallet version.

#![recursion_limit="128"]

use codec::{Decode, Encode};
use sp_runtime::{generic, traits::{BlakeTwo256, Block as _, Verify}};
use frame_support::{
	traits::{PALLET_VERSION_STORAGE_KEY_POSTFIX, PalletVersion, OnRuntimeUpgrade},
	crate_to_pallet_version, weights::Weight,
};
use sp_core::{H256, sr25519};

mod system;

/// A version that we will check for in the tests
const SOME_TEST_VERSION: PalletVersion = PalletVersion { major: 3000, minor: 30, patch: 13 };

/// Checks that `on_runtime_upgrade` sets the latest pallet version when being called without
/// being provided by the user.
mod module1 {
	use super::*;

	pub trait Trait: system::Trait {}

	frame_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where
			origin: <T as system::Trait>::Origin,
			system = system,
		{}
	}
}

/// Checks that `on_runtime_upgrade` sets the latest pallet version when being called and also
/// being provided by the user.
mod module2 {
	use super::*;

	pub trait Trait<I=DefaultInstance>: system::Trait {}

	frame_support::decl_module! {
		pub struct Module<T: Trait<I>, I: Instance=DefaultInstance> for enum Call where
			origin: <T as system::Trait>::Origin,
			system = system
		{
			fn on_runtime_upgrade() -> Weight {
				assert_eq!(crate_to_pallet_version!(), Self::current_version());

				let version_key = PalletVersion::storage_key::<T::PalletInfo, Self>().unwrap();
				let version_value = sp_io::storage::get(&version_key);

				if version_value.is_some() {
					assert_eq!(SOME_TEST_VERSION, Self::storage_version().unwrap());
				} else {
					// As the storage version does not exist yet, it should be `None`.
					assert!(Self::storage_version().is_none());
				}

				0
			}
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Module2 {}
	}
}

impl module1::Trait for Runtime {}
impl module2::Trait for Runtime {}
impl module2::Trait<module2::Instance1> for Runtime {}
impl module2::Trait<module2::Instance2> for Runtime {}

pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

impl system::Trait for Runtime {
	type BaseCallFilter= ();
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type Event = Event;
	type PalletInfo = PalletInfo;
	type Call = Call;
	type DbWeight = ();
}

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module, Call, Event<T>},
		Module1: module1::{Module, Call},
		Module2: module2::{Module, Call},
		Module2_1: module2::<Instance1>::{Module, Call},
		Module2_2: module2::<Instance2>::{Module, Call},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, Call, Signature, ()>;

/// Returns the storage key for `PalletVersion` for the given `pallet`.
fn get_pallet_version_storage_key_for_pallet(pallet: &str) -> [u8; 32] {
	let pallet_name = sp_io::hashing::twox_128(pallet.as_bytes());
	let postfix = sp_io::hashing::twox_128(PALLET_VERSION_STORAGE_KEY_POSTFIX);

	let mut final_key = [0u8; 32];
	final_key[..16].copy_from_slice(&pallet_name);
	final_key[16..].copy_from_slice(&postfix);

	final_key
}

/// Checks the version of the given `pallet`.
///
/// It is expected that the pallet version can be found in the storage and equals the
/// current crate version.
fn check_pallet_version(pallet: &str) {
	let key = get_pallet_version_storage_key_for_pallet(pallet);
	let value = sp_io::storage::get(&key).expect("Pallet version exists");
	let version = PalletVersion::decode(&mut &value[..])
		.expect("Pallet version is encoded correctly");

	assert_eq!(crate_to_pallet_version!(), version);
}

#[test]
fn on_runtime_upgrade_sets_the_pallet_versions_in_storage() {
	sp_io::TestExternalities::new_empty().execute_with(|| {
		AllModules::on_runtime_upgrade();

		check_pallet_version("Module1");
		check_pallet_version("Module2");
		check_pallet_version("Module2_1");
		check_pallet_version("Module2_2");
	});
}

#[test]
fn on_runtime_upgrade_overwrites_old_version() {
	sp_io::TestExternalities::new_empty().execute_with(|| {
		let key = get_pallet_version_storage_key_for_pallet("Module2");
		sp_io::storage::set(&key, &SOME_TEST_VERSION.encode());

		AllModules::on_runtime_upgrade();

		check_pallet_version("Module1");
		check_pallet_version("Module2");
		check_pallet_version("Module2_1");
		check_pallet_version("Module2_2");
	});
}
