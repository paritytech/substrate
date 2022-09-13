// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Origin tests for construct_runtime macro

#![recursion_limit = "128"]

use codec::MaxEncodedLen;
use frame_support::traits::{Contains, OriginTrait};
use scale_info::TypeInfo;
use sp_core::{sr25519, H256};
use sp_runtime::{generic, traits::BlakeTwo256};

mod system;

mod nested {
	use super::*;

	pub mod module {

		use super::*;

		pub trait Config: system::Config {}

		frame_support::decl_module! {
			pub struct Module<T: Config> for enum Call
				where origin: <T as system::Config>::Origin, system=system
			{
				#[weight = 0]
				pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
					Err(Error::<T>::Something.into())
				}
			}
		}

		#[derive(
			Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode, TypeInfo, MaxEncodedLen,
		)]
		pub struct Origin;

		frame_support::decl_event! {
			pub enum Event {
				A,
			}
		}

		frame_support::decl_error! {
			pub enum Error for Module<T: Config> {
				Something
			}
		}

		frame_support::decl_storage! {
			trait Store for Module<T: Config> as Module {}
			add_extra_genesis {
				build(|_config| {})
			}
		}
	}
}

pub mod module {
	use super::*;

	pub trait Config: system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call
			where origin: <T as system::Config>::Origin, system=system
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T>::Something.into())
			}
			#[weight = 0]
			pub fn aux_1(_origin, #[compact] _data: u32) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 0]
			pub fn aux_2(_origin, _data: i32, #[compact] _data2: u32) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 0]
			fn aux_3(_origin, _data: i32, _data2: String) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 3]
			fn aux_4(_origin) -> frame_support::dispatch::DispatchResult { unreachable!() }
			#[weight = (5, frame_support::dispatch::DispatchClass::Operational)]
			fn operational(_origin) { unreachable!() }
		}
	}

	#[derive(
		Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode, TypeInfo, MaxEncodedLen,
	)]
	pub struct Origin<T>(pub core::marker::PhantomData<T>);

	frame_support::decl_event! {
		pub enum Event {
			A,
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Config> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Module {}
		add_extra_genesis {
			build(|_config| {})
		}
	}
}

impl nested::module::Config for RuntimeOriginTest {}
impl module::Config for RuntimeOriginTest {}

pub struct BaseCallFilter;
impl Contains<RuntimeCall> for BaseCallFilter {
	fn contains(c: &RuntimeCall) -> bool {
		match c {
			RuntimeCall::NestedModule(_) => true,
			_ => false,
		}
	}
}

impl system::Config for RuntimeOriginTest {
	type BaseCallFilter = BaseCallFilter;
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type AccountId = u32;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type RuntimeCall = RuntimeCall;
	type DbWeight = ();
}

frame_support::construct_runtime!(
	pub enum RuntimeOriginTest where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Event<T>, Origin<T>},
		NestedModule: nested::module::{Pallet, Origin, Call},
		Module: module::{Pallet, Origin<T>, Call},
	}
);

pub type Signature = sr25519::Signature;
pub type BlockNumber = u64;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

#[test]
fn origin_default_filter() {
	let accepted_call = nested::module::Call::fail {}.into();
	let rejected_call = module::Call::fail {}.into();

	assert_eq!(Origin::root().filter_call(&accepted_call), true);
	assert_eq!(Origin::root().filter_call(&rejected_call), true);
	assert_eq!(Origin::none().filter_call(&accepted_call), true);
	assert_eq!(Origin::none().filter_call(&rejected_call), false);
	assert_eq!(Origin::signed(0).filter_call(&accepted_call), true);
	assert_eq!(Origin::signed(0).filter_call(&rejected_call), false);
	assert_eq!(Origin::from(Some(0)).filter_call(&accepted_call), true);
	assert_eq!(Origin::from(Some(0)).filter_call(&rejected_call), false);
	assert_eq!(Origin::from(None).filter_call(&accepted_call), true);
	assert_eq!(Origin::from(None).filter_call(&rejected_call), false);
	assert_eq!(Origin::from(nested::module::Origin).filter_call(&accepted_call), true);
	assert_eq!(Origin::from(nested::module::Origin).filter_call(&rejected_call), false);

	let mut origin = Origin::from(Some(0));
	origin.add_filter(|c| matches!(c, RuntimeCall::Module(_)));
	assert_eq!(origin.filter_call(&accepted_call), false);
	assert_eq!(origin.filter_call(&rejected_call), false);

	// Now test for root origin and filters:
	let mut origin = Origin::from(Some(0));
	origin.set_caller_from(Origin::root());
	assert!(matches!(origin.caller, OriginCaller::system(system::RawOrigin::Root)));

	// Root origin bypass all filter.
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), true);

	origin.set_caller_from(Origin::from(Some(0)));

	// Back to another signed origin, the filtered are now effective again
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), false);

	origin.set_caller_from(Origin::root());
	origin.reset_filter();

	// Root origin bypass all filter, even when they are reset.
	assert_eq!(origin.filter_call(&accepted_call), true);
	assert_eq!(origin.filter_call(&rejected_call), true);
}
