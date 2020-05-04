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
	impl_outer_origin, parameter_types, ord_parameter_types, traits::{OnInitialize, OnFinalize}
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	Perbill,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
use frame_system::EnsureSignedBy;

impl_outer_origin! {
	pub enum Origin for Test {}
}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const CandidateDeposit: u64 = 25;
	pub const WrongSideDeduction: u64 = 2;
	pub const MaxStrikes: u32 = 2;
	pub const RotationPeriod: u64 = 4;
	pub const PeriodSpend: u64 = 1000;
	pub const MaxLockDuration: u64 = 100;
	pub const ChallengePeriod: u64 = 8;

	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();

	pub const ExistentialDeposit: u64 = 1;
	pub const SocietyModuleId: ModuleId = ModuleId(*b"py/socie");
}

ord_parameter_types! {
	pub const FounderSetAccount: u128 = 1;
	pub const SuspensionJudgementSetAccount: u128 = 2;
}

impl frame_system::Trait for Test {
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
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type AccountData = pallet_balances::AccountData<u64>;
}

impl pallet_balances::Trait for Test {
	type Balance = u64;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}

impl Trait for Test {
	type Event = ();
	type Currency = pallet_balances::Module<Self>;
	type Randomness = ();
	type CandidateDeposit = CandidateDeposit;
	type WrongSideDeduction = WrongSideDeduction;
	type MaxStrikes = MaxStrikes;
	type PeriodSpend = PeriodSpend;
	type MembershipChanged = ();
	type RotationPeriod = RotationPeriod;
	type MaxLockDuration = MaxLockDuration;
	type FounderSetOrigin = EnsureSignedBy<FounderSetAccount, u128>;
	type SuspensionJudgementOrigin = EnsureSignedBy<SuspensionJudgementSetAccount, u128>;
	type ChallengePeriod = ChallengePeriod;
	type ModuleId = SocietyModuleId;
}

pub type Society = Module<Test>;
pub type System = frame_system::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;

pub struct EnvBuilder {
	members: Vec<u128>,
	balance: u64,
	balances: Vec<(u128, u64)>,
	pot: u64,
	max_members: u32,
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
				(70, 50),
				(80, 50),
				(90, 50),
			],
			pot: 0,
			max_members: 100,
		}
	}

	pub fn execute<R, F: FnOnce() -> R>(mut self, f: F) -> R {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		self.balances.push((Society::account_id(), self.balance.max(self.pot)));
		pallet_balances::GenesisConfig::<Test> {
			balances: self.balances,
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::<Test>{
			members: self.members,
			pot: self.pot,
			max_members: self.max_members,
		}.assimilate_storage(&mut t).unwrap();
		let mut ext: sp_io::TestExternalities = t.into();
		ext.execute_with(f)
	}
	#[allow(dead_code)]
	pub fn with_members(mut self, m: Vec<u128>) -> Self {
		self.members = m;
		self
	}
	#[allow(dead_code)]
	pub fn with_balances(mut self, b: Vec<(u128, u64)>) -> Self {
		self.balances = b;
		self
	}
	#[allow(dead_code)]
	pub fn with_pot(mut self, p: u64) -> Self {
		self.pot = p;
		self
	}
	#[allow(dead_code)]
	pub fn with_balance(mut self, b: u64) -> Self {
		self.balance = b;
		self
	}
	#[allow(dead_code)]
	pub fn with_max_members(mut self, n: u32) -> Self {
		self.max_members = n;
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

/// Creates a bid struct using input parameters.
pub fn create_bid<AccountId, Balance>(
	value: Balance,
	who: AccountId,
	kind: BidKind<AccountId, Balance>
) -> Bid<AccountId, Balance>
{
	Bid {
		who,
		kind,
		value
	}
}
