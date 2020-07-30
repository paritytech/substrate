// Copyright 2019-2020
//     by  Centrality Investments Ltd.
//     and Parity Technologies (UK) Ltd.
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

//! Mocks for the module.

#![cfg(test)]

use sp_runtime::{
	Perbill,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
use sp_core::H256;
use frame_support::{parameter_types, impl_outer_event, impl_outer_origin, weights::Weight};

use super::*;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<u64>;
	type Header = Header;
	type Event = TestEvent;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl Trait for Test {
	type Balance = u64;
	type AssetId = u32;
	type Event = TestEvent;
}

mod generic_asset {
	pub use crate::Event;
}

use frame_system as system;
impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		generic_asset<T>,
	}
}

pub type GenericAsset = Module<Test>;

pub type System = frame_system::Module<Test>;

pub struct ExtBuilder {
	asset_id: u32,
	next_asset_id: u32,
	accounts: Vec<u64>,
	initial_balance: u64,
}

// Returns default values for genesis config
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			asset_id: 0,
			next_asset_id: 1000,
			accounts: vec![0],
			initial_balance: 0,
		}
	}
}

impl ExtBuilder {
	// Sets free balance to genesis config
	pub fn free_balance(mut self, free_balance: (u32, u64, u64)) -> Self {
		self.asset_id = free_balance.0;
		self.accounts = vec![free_balance.1];
		self.initial_balance = free_balance.2;
		self
	}

	pub fn next_asset_id(mut self, asset_id: u32) -> Self {
		self.next_asset_id = asset_id;
		self
	}

	// builds genesis config
	pub fn build(self) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

		GenesisConfig::<Test> {
			assets: vec![self.asset_id],
			endowed_accounts: self.accounts,
			initial_balance: self.initial_balance,
			next_asset_id: self.next_asset_id,
			staking_asset_id: 16000,
			spending_asset_id: 16001,
		}.assimilate_storage(&mut t).unwrap();

		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default()
		.build_storage::<Test>()
		.unwrap()
		.into()
}
