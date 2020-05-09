// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Test utilities

use super::*;

use frame_support::{
	impl_outer_origin, impl_outer_dispatch, impl_outer_event, parameter_types,
	weights::Weight,
	traits::{OnInitialize, OnFinalize},
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header,
};

use crate as sudo;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}
impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		sudo<T>,
	}
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		sudo::Sudo,
		priveleged_fn_test_module::Priveleged,
	}
}

// Dummy module for the testing the sudo modules's ability to limit access to root
mod priveleged_fn_test_module {
	use frame_support::{decl_module, dispatch};
	use frame_system::{self as system, ensure_root};
	pub trait Trait: frame_system::Trait {}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			#[weight = 0]
			pub fn privileged_function(origin) -> dispatch::DispatchResult {
				ensure_root(origin)?;
				println!("privellege_function was passed a valid root origin");
				Ok(())
			}
		}
	}

}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Trait for Test {
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>; 
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

// Implement the sudo modules's Trait on the Test runtime
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
}

// Implement the privelleged test module's Trait on the Test runtime
impl priveleged_fn_test_module::Trait for Test {}

// New type that wraps the runtime mock in the pallets module
pub type Sudo = Module<Test>;
pub type System = frame_system::Module<Test>;
// New type that wraps the runtime mock in the priveleged module
pub type Priveleged = priveleged_fn_test_module::Module<Test>;

// New type for dispatchable functions from priveleged module for the mock runtime
pub type PrivelegedCall = priveleged_fn_test_module::Call<Test>;