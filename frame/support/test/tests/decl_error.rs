// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#![recursion_limit="128"]

use sp_runtime::{generic, traits::{BlakeTwo256, Block as _, Verify}, DispatchError};
use sp_core::{H256, sr25519};


mod system;

pub trait Currency {}

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
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type Event = Event;
	type ModuleToIndex = ModuleToIndex;
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
