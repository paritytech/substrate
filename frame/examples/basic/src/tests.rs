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

use core::hash::Hash;

use crate::*;
use frame_support::{
	assert_ok,
	dispatch::{DispatchInfo, GetDispatchInfo},
	traits::{ConstU64, Hash as _, OnInitialize},
};
use sp_core::H256;
use sp_io::DefaultChildStorage;
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

// Overall goal: implement config of a pallet for some struct `Impl`, while implementing the
// `Config` for `Runtime`, use `Impl` to get the defaults. We first do it manually, later on we will
// use a derive macro.w
//
// 3 approaches:
// 1. implement the real config using generics for things that cannot be mocked.
//   - lead to unexpected compiler issues.
// 2. implement the real config using fake types for things that cannot be a
//   - not fully explored.
// 3. generate a sub `DefaultConfig` that only has the things that can have a default, implement
//    that.
//
// Option 3 seems to be the best at the end of the day because it will also avoid the need to
// implement `system::Config`.

// parameterize `testing::Impl` with the items that cannot have a default.
type SystemRuntime = frame_system::pallet::preludes::testing::Impl<
	RuntimeCall,
	RuntimeOrigin,
	RuntimeEvent,
	PalletInfo,
>;

// a bit of extra boilerplate needed to make the compiler happy.
impl From<frame_system::Call<SystemRuntime>> for RuntimeCall {
	fn from(_: frame_system::Call<SystemRuntime>) -> Self {
		unreachable!()
	}
}
impl From<frame_system::Event<SystemRuntime>> for RuntimeEvent {
	fn from(_: frame_system::Event<SystemRuntime>) -> Self {
		unreachable!()
	}
}

type SystemRuntime2 = frame_system::preludes::testing::Impl2;

// Once this impl block can almost gully be delegated to `SystemRuntime`, we can move it to a
// proc-macro. That's the easy part.
type __AccountId = <SystemRuntime as frame_system::Config>::AccountId;
type __Hash = <SystemRuntime as frame_system::Config>::Hash;












#[frame_system::derive_impl(test)]
impl frame_system::Config for Test {
	// these cannot be overwritten.
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type BaseCallFilter = frame_support::traits::Everything;
	type OnSetCode = ();
	type Header = <Block as sp_runtime::traits::Block>::Header;

	// type AccountId = u32;
	// type AccountId = <frame_system::prelude::testing::Impl as frame_system::DefaultConfig>::AccountId;
	type X = <frame_system::prelude::testing::Impl as frame_system::DefaultConfig>::X;
	type Y = <frame_system::prelude::testing::Impl as frame_system::DefaultConfig>::Y;
	type Z = <frame_system::prelude::testing::Impl as frame_system::DefaultConfig>::Z;
}











impl pallet_balances::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type DustRemoval = ();
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
	type MagicNumber = ConstU64<1_000_000_000>;
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
