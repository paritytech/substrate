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
	pub const PeriodSpend: u64 = 100;
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
	type AccountId = u64;
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
	type FounderOrigin = EnsureSignedBy<FounderSetAccount, u64>;
}

pub type Society = Module<Test>;
pub type System = system::Module<Test>;
pub type Balances = balances::Module<Test>;

/// This function basically just builds a genesis storage key/value store according to
/// our desired mockup.
pub fn new_test_ext() -> runtime_io::TestExternalities {
	let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	// We use default for brevity, but you can configure as desired if needed.
	balances::GenesisConfig::<Test> {
		balances: vec![
			(5, 500_000),
			(10, 500_000),
			(15, 500_000),
			(20, 500_000),
			(31, 500_000),
			(40, 500_000),
			(99, 1),
		],
		vesting: vec![],
	}.assimilate_storage(&mut t).unwrap();
	// Can be enabled once we have #4315
	/*GenesisConfig::<Test>{
		members: vec![5],
	}.assimilate_storage(&mut t).unwrap();*/
	t.into()
}

/// Run until a particular block.
pub fn run_to_block(n: u64) {
	println!("Running until block {}", n);
	while System::block_number() < n {
		if System::block_number() > 1 {
			println!("Finalizing {}", System::block_number());
			System::on_finalize(System::block_number());
		}
		System::set_block_number(System::block_number() + 1);
		println!("Initializing {}", System::block_number());
		System::on_initialize(System::block_number());
		Society::on_initialize(System::block_number());
	}
}
