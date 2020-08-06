// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::*;
use sp_std::cell::RefCell;
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	testing::Header,
};
use frame_support::{
	impl_outer_origin, parameter_types,
	weights::PostDispatchInfo,
};

impl_outer_origin! {
	pub enum Origin for Test where system = super {}
}

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 10;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumExtrinsicWeight: Weight = 768;
	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
	pub const MaximumBlockLength: u32 = 1024;
	pub Version: RuntimeVersion = RuntimeVersion {
		spec_name: sp_version::create_runtime_str!("test"),
		impl_name: sp_version::create_runtime_str!("system-test"),
		authoring_version: 1,
		spec_version: 1,
		impl_version: 1,
		apis: sp_version::create_apis_vec!([]),
		transaction_version: 1,
	};
	pub const BlockExecutionWeight: Weight = 10;
	pub const ExtrinsicBaseWeight: Weight = 5;
	pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
		read: 10,
		write: 100,
	};
}

thread_local!{
	pub static KILLED: RefCell<Vec<u64>> = RefCell::new(vec![]);
}

pub struct RecordKilled;
impl OnKilledAccount<u64> for RecordKilled {
	fn on_killed_account(who: &u64) { KILLED.with(|r| r.borrow_mut().push(*who)) }
}

#[derive(Debug, codec::Encode, codec::Decode)]
pub struct Call;

impl Dispatchable for Call {
	type Origin = Origin;
	type Trait = ();
	type Info = DispatchInfo;
	type PostInfo = PostDispatchInfo;
	fn dispatch(self, _origin: Self::Origin)
		-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
			panic!("Do not use dummy implementation for dispatch.");
	}
}

impl Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event<Self>;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = DbWeight;
	type BlockExecutionWeight = BlockExecutionWeight;
	type ExtrinsicBaseWeight = ExtrinsicBaseWeight;
	type MaximumExtrinsicWeight = MaximumExtrinsicWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = Version;
	type ModuleToIndex = ();
	type AccountData = u32;
	type OnNewAccount = ();
	type OnKilledAccount = RecordKilled;
	type SystemWeightInfo = ();
}

pub type System = Module<Test>;
pub type SysEvent = <Test as Trait>::Event;

pub const CALL: &<Test as Trait>::Call = &Call;

/// Create new externalities for `System` module tests.
pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut ext: sp_io::TestExternalities = GenesisConfig::default().build_storage::<Test>().unwrap().into();
	// Add to each test the initial weight of a block
	ext.execute_with(|| System::register_extra_weight_unchecked(
		<Test as Trait>::BlockExecutionWeight::get(),
		DispatchClass::Mandatory
	));
	ext
}
