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
	weights::{Weight, DispatchClass}
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use sp_io;
use crate as sudo;

// This logger module used by privileged_function() to track execution.
// Adapted from the logger in `frame/scheduler/src/lib.rs` `tests`. Logs u64 to 
// represent AccountId
pub mod logger {
	use super::*;
	use std::cell::RefCell;
	use frame_system::ensure_root;

	thread_local! {
		static LOG: RefCell<Vec<u64>> = RefCell::new(Vec::new());
	}
	pub fn log() -> Vec<u64> {
		LOG.with(|log| log.borrow().clone())
	}
	pub trait Trait: system::Trait {
		type Event: From<Event> + Into<<Self as system::Trait>::Event>;
	}
	decl_storage! {
		trait Store for Module<T: Trait> as Logger {
		}
	}
	decl_event! {
		pub enum Event {
			Logged(u64, Weight),
		}
	}
	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
			fn deposit_event() = default;

			#[weight = FunctionOf(
				|args: (&u64, &Weight)| *args.1,
				|_: (&u64, &Weight)| DispatchClass::Normal,
				Pays::Yes,
			)]
			fn log(origin, i: u64, weight: Weight){
				ensure_root(origin)?;
				Self::deposit_event(Event::Logged(i, weight));
				LOG.with(|log| {
					log.borrow_mut().push(i);
				})
			}

			#[weight = FunctionOf(
				|args: (&u64, &Weight)| *args.1,
				|_: (&u64, &Weight)| DispatchClass::Normal,
				Pays::Yes,
			)]
			fn non_priveleged_log(origin, i: u64, weight: Weight){
				// Ensure that the origin is some signed account. For these tests 
				// the 'Signer' is root_key using sudo_as() and it is not a literal 
				// signature but instead `frame_system::RawOrigin::Signed(who)`.
				ensure_signed(origin)?;
				Self::deposit_event(Event::Logged(i, weight));
				LOG.with(|log| {
					log.borrow_mut().push(i);
				})
			}
		}
	}
}

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

mod test_events {
    pub use crate::Event;
}

impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		sudo<T>,
		logger, // why does this not need to be generic over T?
	}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		sudo::Sudo,
		logger::Logger,
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

// Implement the logger module's Trait on the Test runtime
impl logger::Trait for Test {
	type Event = TestEvent;
}

// Implement the sudo modules's Trait on the Test runtime
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
}

// Assign back to type variables so we can make dispatched calls of these modules later
pub type Sudo = Module<Test>;
pub type Logger = logger::Module<Test>;
pub type System = system::Module<Test>;

// New types for dispatchable functions
pub type SudoCall = sudo::Call<Test>;
pub type LoggerCall = logger::Call<Test>;

// Build test enviroment by setting the root_key for the Genesis
pub fn new_test_ext(root_key: u64) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	GenesisConfig::<Test>{
		key: root_key,
	}.assimilate_storage(&mut t).unwrap();
	t.into()
}
