// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

#![recursion_limit = "128"]

use codec::{Decode, Encode};
use frame_support::{
	crate_to_pallet_version,
	traits::{
		GetPalletVersion, OnRuntimeUpgrade, PalletVersion, PALLET_VERSION_STORAGE_KEY_POSTFIX,
	},
	weights::Weight,
};
use sp_core::{sr25519, H256};
use sp_runtime::{
	generic,
	traits::{BlakeTwo256, Verify},
	BuildStorage,
};

/// A version that we will check for in the tests
const SOME_TEST_VERSION: PalletVersion = PalletVersion { major: 3000, minor: 30, patch: 13 };

/// Checks that `on_runtime_upgrade` sets the latest pallet version when being called without
/// being provided by the user.
mod module1 {
	pub trait Config: frame_system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where
			origin: <T as frame_system::Config>::Origin,
		{}
	}
}

/// Checks that `on_runtime_upgrade` sets the latest pallet version when being called and also
/// being provided by the user.
mod module2 {
	use super::*;

	pub trait Config<I = DefaultInstance>: frame_system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config<I>, I: Instance=DefaultInstance> for enum Call where
			origin: <T as frame_system::Config>::Origin,
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
		trait Store for Module<T: Config<I>, I: Instance=DefaultInstance> as Module2 {}
	}
}

#[frame_support::pallet]
mod pallet3 {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			return 3
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

#[frame_support::pallet]
mod pallet4 {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn on_runtime_upgrade() -> Weight {
			return 3
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {}
}

impl module1::Config for Runtime {}
impl module2::Config for Runtime {}
impl module2::Config<module2::Instance1> for Runtime {}
impl module2::Config<module2::Instance2> for Runtime {}

impl pallet3::Config for Runtime {}
impl pallet4::Config for Runtime {}
impl pallet4::Config<pallet4::Instance1> for Runtime {}
impl pallet4::Config<pallet4::Instance2> for Runtime {}

pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

frame_support::parameter_types!(
	pub const BlockHashCount: u32 = 250;
);

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::AllowAll;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>},
		Module1: module1::{Pallet, Call},
		Module2: module2::{Pallet, Call},
		Module2_1: module2::<Instance1>::{Pallet, Call},
		Module2_2: module2::<Instance2>::{Pallet, Call},
		Pallet3: pallet3::{Pallet, Call},
		Pallet4: pallet4::{Pallet, Call},
		Pallet4_1: pallet4::<Instance1>::{Pallet, Call},
		Pallet4_2: pallet4::<Instance2>::{Pallet, Call},
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
	let version =
		PalletVersion::decode(&mut &value[..]).expect("Pallet version is encoded correctly");

	assert_eq!(crate_to_pallet_version!(), version);
}

#[test]
fn on_runtime_upgrade_sets_the_pallet_versions_in_storage() {
	sp_io::TestExternalities::new_empty().execute_with(|| {
		AllPallets::on_runtime_upgrade();

		check_pallet_version("Module1");
		check_pallet_version("Module2");
		check_pallet_version("Module2_1");
		check_pallet_version("Module2_2");
		check_pallet_version("Pallet3");
		check_pallet_version("Pallet4");
		check_pallet_version("Pallet4_1");
		check_pallet_version("Pallet4_2");
	});
}

#[test]
fn on_runtime_upgrade_overwrites_old_version() {
	sp_io::TestExternalities::new_empty().execute_with(|| {
		let key = get_pallet_version_storage_key_for_pallet("Module2");
		sp_io::storage::set(&key, &SOME_TEST_VERSION.encode());

		AllPallets::on_runtime_upgrade();

		check_pallet_version("Module1");
		check_pallet_version("Module2");
		check_pallet_version("Module2_1");
		check_pallet_version("Module2_2");
		check_pallet_version("Pallet3");
		check_pallet_version("Pallet4");
		check_pallet_version("Pallet4_1");
		check_pallet_version("Pallet4_2");
	});
}

#[test]
fn genesis_init_puts_pallet_version_into_storage() {
	let storage = GenesisConfig::default().build_storage().expect("Builds genesis storage");

	sp_io::TestExternalities::new(storage).execute_with(|| {
		check_pallet_version("Module1");
		check_pallet_version("Module2");
		check_pallet_version("Module2_1");
		check_pallet_version("Module2_2");
		check_pallet_version("Pallet3");
		check_pallet_version("Pallet4");
		check_pallet_version("Pallet4_1");
		check_pallet_version("Pallet4_2");

		let system_version = System::storage_version().expect("System version should be set");
		assert_eq!(System::current_version(), system_version);
	});
}
