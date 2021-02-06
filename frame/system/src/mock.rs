// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
const MAX_BLOCK_WEIGHT: Weight = 1024;

parameter_types! {
	pub const BlockHashCount: u64 = 10;
	pub Version: RuntimeVersion = RuntimeVersion {
		spec_name: sp_version::create_runtime_str!("test"),
		impl_name: sp_version::create_runtime_str!("system-test"),
		authoring_version: 1,
		spec_version: 1,
		impl_version: 1,
		apis: sp_version::create_apis_vec!([]),
		transaction_version: 1,
	};
	pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
		read: 10,
		write: 100,
	};
	pub RuntimeBlockWeights: limits::BlockWeights = limits::BlockWeights::builder()
		.base_block(10)
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = 5;
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAX_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAX_BLOCK_WEIGHT);
			weights.reserved = Some(
				MAX_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAX_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(Perbill::from_percent(0))
		.build_or_panic();
	pub RuntimeBlockLength: limits::BlockLength =
		limits::BlockLength::max_with_normal_ratio(1024, NORMAL_DISPATCH_RATIO);
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
	type Config = ();
	type Info = DispatchInfo;
	type PostInfo = PostDispatchInfo;
	fn dispatch(self, _origin: Self::Origin)
		-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
			panic!("Do not use dummy implementation for dispatch.");
	}
}

impl Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = RuntimeBlockWeights;
	type BlockLength = RuntimeBlockLength;
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
	type DbWeight = DbWeight;
	type Version = Version;
	type PalletInfo = ();
	type AccountData = u32;
	type OnNewAccount = ();
	type OnKilledAccount = RecordKilled;
	type SystemWeightInfo = ();
	type SS58Prefix = ();
}

pub type System = Module<Test>;
pub type SysEvent = <Test as Config>::Event;

pub const CALL: &<Test as Config>::Call = &Call;

/// Create new externalities for `System` module tests.
pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut ext: sp_io::TestExternalities = GenesisConfig::default().build_storage::<Test>().unwrap().into();
	// Add to each test the initial weight of a block
	ext.execute_with(|| System::register_extra_weight_unchecked(
		<Test as crate::Config>::BlockWeights::get().base_block,
		DispatchClass::Mandatory
	));
	ext
}
