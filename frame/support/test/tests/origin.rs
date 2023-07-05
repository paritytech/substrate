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

//! RuntimeOrigin tests for construct_runtime macro

#![recursion_limit = "128"]

use frame_support::traits::{Contains, OriginTrait};
use sp_runtime::{generic, traits::BlakeTwo256};

mod nested {
	#[frame_support::pallet(dev_mode)]
	pub mod module {
		use self::frame_system::pallet_prelude::*;
		use frame_support::pallet_prelude::*;
		use frame_support_test as frame_system;

		#[pallet::pallet]
		pub struct Pallet<T>(_);

		#[pallet::config]
		pub trait Config: frame_system::Config {
			type RuntimeEvent: From<Event<Self>>
				+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		}

		#[pallet::call]
		impl<T: Config> Pallet<T> {
			pub fn fail(_origin: OriginFor<T>) -> DispatchResult {
				Err(Error::<T>::Something.into())
			}
		}

		#[pallet::origin]
		#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
		pub struct Origin;

		#[pallet::event]
		pub enum Event<T> {
			A,
		}

		#[pallet::error]
		pub enum Error<T> {
			Something,
		}

		#[pallet::genesis_config]
		#[derive(Default)]
		pub struct GenesisConfig {}

		#[pallet::genesis_build]
		impl<T: Config> GenesisBuild<T> for GenesisConfig {
			fn build(&self) {}
		}
	}
}

#[frame_support::pallet(dev_mode)]
pub mod module {
	use self::frame_system::pallet_prelude::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn fail(_origin: OriginFor<T>) -> DispatchResult {
			Err(Error::<T>::Something.into())
		}
		pub fn aux_1(_origin: OriginFor<T>, #[pallet::compact] _data: u32) -> DispatchResult {
			unreachable!()
		}
		pub fn aux_2(
			_origin: OriginFor<T>,
			_data: i32,
			#[pallet::compact] _data2: u32,
		) -> DispatchResult {
			unreachable!()
		}
		#[pallet::weight(0)]
		pub fn aux_3(_origin: OriginFor<T>, _data: i32, _data2: String) -> DispatchResult {
			unreachable!()
		}
		#[pallet::weight(3)]
		pub fn aux_4(_origin: OriginFor<T>) -> DispatchResult {
			unreachable!()
		}
		#[pallet::weight((5, DispatchClass::Operational))]
		pub fn operational(_origin: OriginFor<T>) -> DispatchResult {
			unreachable!()
		}
	}

	#[pallet::origin]
	#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
	pub struct Origin<T>(pub PhantomData<T>);

	#[pallet::event]
	pub enum Event<T> {
		A,
	}

	#[pallet::error]
	pub enum Error<T> {
		Something,
	}

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig {}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {}
	}
}

pub struct BaseCallFilter;
impl Contains<RuntimeCall> for BaseCallFilter {
	fn contains(c: &RuntimeCall) -> bool {
		match c {
			RuntimeCall::NestedModule(_) => true,
			_ => false,
		}
	}
}

pub type BlockNumber = u32;
pub type AccountId = u32;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

frame_support::construct_runtime!(
	pub enum RuntimeOriginTest where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_support_test,
		NestedModule: nested::module,
		Module: module,
	}
);

impl frame_support_test::Config for RuntimeOriginTest {
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type BaseCallFilter = BaseCallFilter;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type DbWeight = ();
}

impl nested::module::Config for RuntimeOriginTest {
	type RuntimeEvent = RuntimeEvent;
}
impl module::Config for RuntimeOriginTest {
	type RuntimeEvent = RuntimeEvent;
}

#[test]
fn origin_default_filter() {
	let accepted_call = nested::module::Call::fail {}.into();
	let rejected_call = module::Call::fail {}.into();

	assert_eq!(RuntimeOrigin::root().filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::root().filter_call(&rejected_call), true);
	assert_eq!(RuntimeOrigin::none().filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::none().filter_call(&rejected_call), false);
	assert_eq!(RuntimeOrigin::signed(0).filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::signed(0).filter_call(&rejected_call), false);
	assert_eq!(RuntimeOrigin::from(Some(0)).filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::from(Some(0)).filter_call(&rejected_call), false);
	assert_eq!(RuntimeOrigin::from(None).filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::from(None).filter_call(&rejected_call), false);
	assert_eq!(RuntimeOrigin::from(nested::module::Origin).filter_call(&accepted_call), true);
	assert_eq!(RuntimeOrigin::from(nested::module::Origin).filter_call(&rejected_call), false);

	let mut origin = RuntimeOrigin::from(Some(0));
	origin.add_filter(|c| matches!(c, RuntimeCall::Module(_)));
	assert_eq!(origin.filter_call(&accepted_call), false);
	assert_eq!(origin.filter_call(&rejected_call), false);

	// Now test for root origin and filters:
	let mut origin = RuntimeOrigin::from(Some(0));
	origin.set_caller_from(RuntimeOrigin::root());
	assert!(matches!(origin.caller, OriginCaller::system(frame_support_test::RawOrigin::Root)));

	// Root origin bypass all filter.
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), true);

	origin.set_caller_from(RuntimeOrigin::from(Some(0)));

	// Back to another signed origin, the filtered are now effective again
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), false);

	origin.set_caller_from(RuntimeOrigin::root());
	origin.reset_filter();

	// Root origin bypass all filter, even when they are reset.
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), true);
}
