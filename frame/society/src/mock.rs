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

use super::*;

use support::{impl_outer_origin, parameter_types};
use primitives::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
use sp_runtime::{
	Perbill, traits::{BlakeTwo256, IdentityLookup, OnInitialize, OnFinalize}, testing::Header,
};
use system::EnsureSignedBy;

impl_outer_origin! {
	pub enum Origin for Test {}
}

// For testing the module, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of modules we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const CandidateDeposit: u64 = 25;
	pub const WrongSideDeduction: u64 = 2;
	pub const MaxStrikes: u32 = 2;
	pub const Period: u64 = 4;
	pub const PeriodSpend: u64 = 1000;
	pub const MaxLockDuration: u64 = 100;
	pub const FounderSetAccount: u64 = 1;

	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();

	pub const ExistentialDeposit: u64 = 0;
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
}

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = ();
	type Hashing = BlakeTwo256;
	type AccountId = u128;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
}

impl balances::Trait for Test {
	type Balance = u64;
	type OnFreeBalanceZero = ();
	type OnNewAccount = ();
	type Event = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
}

impl Trait for Test {
	type Event = ();
	type Currency = balances::Module<Self>;
	type Randomness = ();
	type CandidateDeposit = CandidateDeposit;
	type WrongSideDeduction = WrongSideDeduction;
	type MaxStrikes = MaxStrikes;
	type PeriodSpend = PeriodSpend;
	type MembershipChanged = ();
	type Period = Period;
	type MaxLockDuration = MaxLockDuration;
	type FounderOrigin = EnsureSignedBy<FounderSetAccount, u128>;
}

pub type Society = Module<Test>;
pub type System = system::Module<Test>;
pub type Balances = balances::Module<Test>;

pub struct EnvBuilder {
	members: Vec<u128>,
	balance: u64,
	balances: Vec<(u128, u64)>,
	pot: u64,
}

impl EnvBuilder {
	pub fn new() -> Self {
		Self {
			members: vec![10],
			balance: 10_000,
			balances: vec![
				(10, 50),
				(20, 50),
				(30, 50),
				(40, 50),
				(50, 50),
				(60, 50),
			],
			pot: 0,
		}
	}

	pub fn execute<R, F: FnOnce() -> R>(mut self, f: F) -> R {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		self.balances.push((Society::account_id(), self.balance.max(self.pot)));
		balances::GenesisConfig::<Test> {
			balances: self.balances,
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::<Test>{
			members: self.members,
			pot: self.pot,
		}.assimilate_storage(&mut t).unwrap();
		let mut ext: runtime_io::TestExternalities = t.into();
		ext.execute_with(f)
	}

	pub fn with_members(mut self, m: Vec<u128>) -> Self {
		self.members = m;
		self
	}

	pub fn with_balances(mut self, b: Vec<(u128, u64)>) -> Self {
		self.balances = b;
		self
	}

	pub fn with_pot(mut self, p: u64) -> Self {
		self.pot = p;
		self
	}

	pub fn with_balance(mut self, b: u64) -> Self {
		self.balance = b;
		self
	}
}

/// Run until a particular block.
pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		if System::block_number() > 1 {
			System::on_finalize(System::block_number());
		}
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		Society::on_initialize(System::block_number());
	}
}
