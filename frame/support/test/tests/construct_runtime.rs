// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! General tests for construct_runtime macro, test for:
//! * error declareed with decl_error works
//! * integrity test is generated

#![recursion_limit="128"]

use sp_runtime::{generic, traits::{BlakeTwo256, Block as _, Verify}, DispatchError};
use sp_core::{H256, sr25519};
use sp_std::cell::RefCell;

mod system;

pub trait Currency {}

thread_local! {
    pub static INTEGRITY_TEST_EXEC: RefCell<u32> = RefCell::new(0);
}

mod module1 {
	use super::*;

	pub trait Trait<I>: system::Trait {}

	frame_support::decl_module! {
		pub struct Module<T: Trait<I>, I: Instance = DefaultInstance> for enum Call
			where origin: <T as system::Trait>::Origin
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T, I>::Something.into())
			}
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Trait<I>, I: Instance> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Module {}
	}
}

mod module2 {
	use super::*;

	pub trait Trait: system::Trait {}

	frame_support::decl_module! {
		pub struct Module<T: Trait> for enum Call
			where origin: <T as system::Trait>::Origin
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T>::Something.into())
			}

			fn integrity_test() {
				INTEGRITY_TEST_EXEC.with(|i| *i.borrow_mut() += 1);
			}
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Trait> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Trait> as Module {}
	}
}

impl module1::Trait<module1::Instance1> for Runtime {}
impl module1::Trait<module1::Instance2> for Runtime {}
impl module2::Trait for Runtime {}

pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

impl system::Trait for Runtime {
	type BaseCallFilter = ();
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type Event = Event;
	type ModuleToIndex = ModuleToIndex;
	type Call = Call;
}

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module, Call, Event<T>},
		Module1_1: module1::<Instance1>::{Module, Call, Storage},
		Module2: module2::{Module, Call, Storage},
		Module1_2: module1::<Instance2>::{Module, Call, Storage},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, Call, Signature, ()>;

#[test]
fn check_module1_1_error_type() {
	assert_eq!(
		Module1_1::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 1, error: 0, message: Some("Something") }),
	);
}

#[test]
fn check_module1_2_error_type() {
	assert_eq!(
		Module1_2::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 3, error: 0, message: Some("Something") }),
	);
}

#[test]
fn check_module2_error_type() {
	assert_eq!(
		Module2::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 2, error: 0, message: Some("Something") }),
	);
}

#[test]
fn integrity_test_works() {
	__construct_runtime_integrity_test::runtime_integrity_tests();
	assert_eq!(INTEGRITY_TEST_EXEC.with(|i| *i.borrow()), 1);
}
