// Copyright 2019 Parity Technologies (UK) Ltd.
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
#![allow(dead_code)]
use sr_primitives::{
	traits::IdentityLookup, Perbill,
	testing::Header,
};
use srml_support::{impl_outer_origin, parameter_types};
use runtime_io;
use primitives::{H256, Blake2Hasher, sr25519::Public};
use crate::{Module, GenesisConfig};
use sr_primitives::BuildStorage;

impl_outer_origin!{
	pub enum Origin for Test {}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
	pub const MinimumPeriod: u64 = 1;
	pub const EpochDuration: u64 = 3;
	pub const ExpectedBlockTime: u64 = 1;
}

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::sr_primitives::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = ();
	type Call = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
}

impl super::Trait for Test {
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ExpectedBlockTime;
}

pub fn new_test_ext(authorities: Vec<Public>) -> runtime_io::TestExternalities<Blake2Hasher> {
	GenesisConfig {
		authorities: authorities.into_iter().map(|a| (a.into(), 1)).collect(),
	}.build_storage().unwrap().build_storage().unwrap().into()
}

pub type System = system::Module<Test>;
pub type Babe = Module<Test>;
