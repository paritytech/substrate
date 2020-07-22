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

//! Mock file for system benchmarking.

#![cfg(test)]

use sp_runtime::traits::IdentityLookup;
use frame_support::{
	impl_outer_origin,
	dispatch::{Dispatchable, DispatchInfo, PostDispatchInfo},
};

type AccountId = u64;
type AccountIndex = u32;
type BlockNumber = u64;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Debug, codec::Encode, codec::Decode)]
pub struct Call;

impl Dispatchable for Call {
	type Origin = ();
	type Trait = ();
	type Info = DispatchInfo;
	type PostInfo = PostDispatchInfo;
	fn dispatch(self, _origin: Self::Origin)
		-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
			panic!("Do not use dummy implementation for dispatch.");
	}
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;

impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = ();
	type BlockHashCount = ();
	type MaximumBlockWeight = ();
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = ();
	type AvailableBlockRatio = ();
	type MaximumBlockLength = ();
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl crate::Trait for Test {}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	sp_io::TestExternalities::new(t)
}
