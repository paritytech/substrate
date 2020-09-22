// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Test utilities

use super::*;
use frame_support::{
	impl_outer_origin, impl_outer_dispatch, impl_outer_event, parameter_types,
	weights::Weight,
};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use sp_io;
use crate as sudo;
use frame_support::traits::Filter;

// Logger module to track execution.
pub mod logger {
	use super::*;
	use frame_system::ensure_root;

	pub trait Trait: frame_system::Trait {
		type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	}

	decl_storage! {
		trait Store for Module<T: Trait> as Logger {
			AccountLog get(fn account_log): Vec<T::AccountId>;
			I32Log get(fn i32_log): Vec<i32>;
		}
	}

	decl_event! {
		pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
			AppendI32(i32, Weight),
			AppendI32AndAccount(AccountId, i32, Weight),
		}
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: <T as frame_system::Trait>::Origin {
			fn deposit_event() = default;

			#[weight = *weight]
			fn privileged_i32_log(origin, i: i32, weight: Weight){
				// Ensure that the `origin` is `Root`.
				ensure_root(origin)?;
				<I32Log>::append(i);
				Self::deposit_event(RawEvent::AppendI32(i, weight));
			}

			#[weight = *weight]
			fn non_privileged_log(origin, i: i32, weight: Weight){
				// Ensure that the `origin` is some signed account.
				let sender = ensure_signed(origin)?;
				<I32Log>::append(i);
				<AccountLog<T>>::append(sender.clone());
				Self::deposit_event(RawEvent::AppendI32AndAccount(sender, i, weight));
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
		frame_system<T>,
		sudo<T>,
		logger<T>,
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

pub struct BlockEverything;
impl Filter<Call> for BlockEverything {
	fn filter(_: &Call) -> bool {
		false
	}
}

impl frame_system::Trait for Test {
	type BaseCallFilter = BlockEverything;
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
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type PalletInfo = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

// Implement the logger module's `Trait` on the Test runtime.
impl logger::Trait for Test {
	type Event = TestEvent;
}

// Implement the sudo module's `Trait` on the Test runtime.
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
}

// Assign back to type variables in order to make dispatched calls of these modules later.
pub type Sudo = Module<Test>;
pub type Logger = logger::Module<Test>;
pub type System = frame_system::Module<Test>;

// New types for dispatchable functions.
pub type SudoCall = sudo::Call<Test>;
pub type LoggerCall = logger::Call<Test>;

// Build test environment by setting the root `key` for the Genesis.
pub fn new_test_ext(root_key: u64) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	GenesisConfig::<Test>{
		key: root_key,
	}.assimilate_storage(&mut t).unwrap();
	t.into()
}
