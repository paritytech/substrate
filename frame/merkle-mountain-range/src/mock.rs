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

use crate as pallet_mmr;
use crate::*;

use codec::{Decode, Encode};
use frame_support::traits::{ConstU32, ConstU64};
use pallet_mmr_primitives::{Compact, LeafDataProvider};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, Keccak256},
};
use sp_std::{cell::RefCell, prelude::*};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		MMR: pallet_mmr::{Pallet, Storage},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type BlockWeights = ();
	type BlockLength = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl Config for Test {
	const INDEXING_PREFIX: &'static [u8] = b"mmr-";

	type Hashing = Keccak256;
	type Hash = H256;
	type LeafData = Compact<Keccak256, (frame_system::Pallet<Test>, LeafData)>;
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
		Self { a, b: Default::default() }
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
