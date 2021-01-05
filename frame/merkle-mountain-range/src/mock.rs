// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use crate::primitives::{LeafDataProvider, Compact};

use codec::{Encode, Decode};
use frame_support::{
	impl_outer_origin, parameter_types,
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{
		BlakeTwo256, Keccak256, IdentityLookup,
	},
};
use sp_std::cell::RefCell;
use sp_std::prelude::*;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type BlockWeights = ();
	type BlockLength = ();
	type Version = ();
	type PalletInfo = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
}

impl Config for Test {
	const INDEXING_PREFIX: &'static [u8] = b"mmr-";

	type Hashing = Keccak256;
	type Hash = H256;
	type LeafData = Compact<Keccak256, (frame_system::Module<Test>, LeafData)>;
	type OnNewRoot = ();
	type WeightInfo = ();
}

#[derive(Encode, Decode, Clone, Default, Eq, PartialEq, Debug)]
pub struct LeafData {
	pub a: u64,
	pub b: Vec<u8>,
}

impl LeafData {
	pub fn new(a: u64) -> Self {
		Self {
			a,
			b: Default::default(),
		}
	}
}

thread_local! {
	pub static LEAF_DATA: RefCell<LeafData> = RefCell::new(Default::default());
}

impl LeafDataProvider for LeafData {
	type LeafData = Self;

	fn leaf_data() -> Self::LeafData {
		LEAF_DATA.with(|r| r.borrow().clone())
	}
}

pub(crate) type MMR = Module<Test>;
