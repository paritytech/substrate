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

//! Tests for pallet-example-basic.

use crate::*;
use frame_support::{
	assert_ok,
	dispatch::{DispatchInfo, GetDispatchInfo},
	traits::{ConstU64, OnInitialize},
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};
// Reexport crate as its pallet name for construct_runtime.
use crate as pallet_example_basic;

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
		Example: pallet_example_basic::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
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
	type MagicNumber = ConstU64<1_000_000_000>;
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
}

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = GenesisConfig {
		// We use default for brevity, but you can configure as desired if needed.
		system: Default::default(),
		balances: Default::default(),
		example: pallet_example_basic::GenesisConfig {
			dummy: 42,
			// we configure the map with (key, value) pairs.
			bar: vec![(1, 2), (2, 3)],
			foo: 24,
		},
	}
	.build_storage()
	.unwrap();
	t.into()
}

#[test]
fn it_works_for_optional_value() {
	new_test_ext().execute_with(|| {
		// Check that GenesisBuilder works properly.
		let val1 = 42;
		let val2 = 27;
		assert_eq!(Example::dummy(), Some(val1));

		// Check that accumulate works when we have Some value in Dummy already.
		assert_ok!(Example::accumulate_dummy(RuntimeOrigin::signed(1), val2));
		assert_eq!(Example::dummy(), Some(val1 + val2));

		// Check that accumulate works when we Dummy has None in it.
		<Example as OnInitialize<u64>>::on_initialize(2);
		assert_ok!(Example::accumulate_dummy(RuntimeOrigin::signed(1), val1));
		assert_eq!(Example::dummy(), Some(val1 + val2 + val1));
	});
}

#[test]
fn it_works_for_default_value() {
	new_test_ext().execute_with(|| {
		assert_eq!(Example::foo(), 24);
		assert_ok!(Example::accumulate_foo(RuntimeOrigin::signed(1), 1));
		assert_eq!(Example::foo(), 25);
	});
}

#[test]
fn set_dummy_works() {
	new_test_ext().execute_with(|| {
		let test_val = 133;
		assert_ok!(Example::set_dummy(RuntimeOrigin::root(), test_val.into()));
		assert_eq!(Example::dummy(), Some(test_val));
	});
}

#[test]
fn signed_ext_watch_dummy_works() {
	new_test_ext().execute_with(|| {
		let call = pallet_example_basic::Call::set_dummy { new_value: 10 }.into();
		let info = DispatchInfo::default();

		assert_eq!(
			WatchDummy::<Test>(PhantomData)
				.validate(&1, &call, &info, 150)
				.unwrap()
				.priority,
			u64::MAX,
		);
		assert_eq!(
			WatchDummy::<Test>(PhantomData).validate(&1, &call, &info, 250),
			InvalidTransaction::ExhaustsResources.into(),
		);
	})
}

#[test]
fn counted_map_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(CountedMap::<Test>::count(), 0);
		CountedMap::<Test>::insert(3, 3);
		assert_eq!(CountedMap::<Test>::count(), 1);
	})
}

#[test]
fn weights_work() {
	// must have a defined weight.
	let default_call = pallet_example_basic::Call::<Test>::accumulate_dummy { increase_by: 10 };
	let info1 = default_call.get_dispatch_info();
	// aka. `let info = <Call<Test> as GetDispatchInfo>::get_dispatch_info(&default_call);`
	// TODO: account for proof size weight
	assert!(info1.weight.ref_time() > 0);

	// `set_dummy` is simpler than `accumulate_dummy`, and the weight
	//   should be less.
	let custom_call = pallet_example_basic::Call::<Test>::set_dummy { new_value: 20 };
	let info2 = custom_call.get_dispatch_info();
	// TODO: account for proof size weight
	assert!(info1.weight.ref_time() > info2.weight.ref_time());
}
