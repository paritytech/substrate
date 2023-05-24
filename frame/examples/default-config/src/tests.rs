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

//! This module tests the `pallet-default-config-example` and serves as a reference example for
//! how to use [`derive_impl`] to vastly simplify declaring a `Test` config.
//!
//! See the comments on line 49 for a detailed explanation.

use crate::*;
use frame_support::{assert_ok, macro_magic::use_attr, traits::ConstU64};
use sp_runtime::{testing::Header, BuildStorage};

// Because `derive_impl` is a [macro_magic](https://crates.io/crates/macro_magic) attribute
// macro, [`#[use_attr]`](`frame_support::macro_magic::use_attr`) must be attached to any use
// statement that brings it into scope.
#[use_attr]
use frame_support::derive_impl;

// Reexport crate as its pallet name for construct_runtime.
use crate as pallet_default_config_example;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// For testing the pallet, we construct a mock runtime.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Example: pallet_default_config_example::{Pallet, Call, Storage, Event<T>},
	}
);

/// Normally this impl statement would need to have the areas that are commented out below
/// be specified manually. Attaching the `derive_impl` attribute, specifying
/// `frame_system::prelude::testing::TestDefaultConfig` as the `default_impl` and
/// `frame_system::pallet::DefaultConfig` as the `disambiguation_path` allows us to bring in
/// defaults for this impl from the `TestDefaultConfig` impl. This will fill in defaults for
/// anything in the `default_impl` that isn't present in our local impl, allowing us to
/// override the `default_impl` in any cases where we want to be explicit and differ from the
/// `default_impl`.
#[derive_impl(frame_system::prelude::testing::TestDefaultConfig as frame_system::pallet::DefaultConfig)]
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	// type BlockWeights = ();
	// type BlockLength = ();
	// type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	// type Index = u64;
	type BlockNumber = u64;
	// type Hash = sp_core::H256;
	type RuntimeCall = RuntimeCall;
	// type Hashing = BlakeTwo256;
	// type AccountId = u64;
	// type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	// type BlockHashCount = ConstU64<250>;
	// type Version = ();
	type PalletInfo = PalletInfo;

	/// we override `AccountData`, since we want a u64 not a u32.
	type AccountData = pallet_balances::AccountData<u64>;

	// type OnNewAccount = ();
	// type OnKilledAccount = ();
	// type SystemWeightInfo = ();
	// type SS58Prefix = ();
	type OnSetCode = ();
	// type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type HoldIdentifier = ();
	type MaxHolds = ();
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
}

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = GenesisConfig {
		// We use default for brevity, but you can configure as desired if needed.
		system: Default::default(),
		balances: Default::default(),
	}
	.build_storage()
	.unwrap();
	t.into()
}

#[test]
fn it_works_for_optional_value() {
	new_test_ext().execute_with(|| {
		assert_eq!(Person::<Test>::get(), None);

		let val1 = 42;
		assert_ok!(Example::add_person(RuntimeOrigin::root(), val1));
		assert_eq!(Person::<Test>::get(), Some(vec![val1]));

		// Check that accumulate works when we have Some value in Person already.
		let val2 = 27;
		assert_ok!(Example::add_person(RuntimeOrigin::root(), val2));
		assert_eq!(Person::<Test>::get(), Some(vec![val1, val2]));
	});
}

#[test]
fn set_person_works() {
	new_test_ext().execute_with(|| {
		let test_val = 133;
		assert_ok!(Example::set_points(RuntimeOrigin::signed(1), test_val.into()));
		assert_eq!(Points::<Test>::get(1), Some(test_val));
	});
}
