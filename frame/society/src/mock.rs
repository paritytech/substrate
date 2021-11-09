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

//! Test utilities

use super::*;
use crate as pallet_society;

use frame_support::{ord_parameter_types, parameter_types, traits::EqualPrivilegeOnly};
use frame_support_test::TestRandomness;
use frame_system::{EnsureOneOf, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	Perbill,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Scheduler: pallet_scheduler::{Pallet, Call, Storage, Event<T>},
		Society: pallet_society::{Pallet, Call, Storage, Event<T>, Config<T>},
	}
);

parameter_types! {
	pub const CandidateDeposit: u64 = 25;
	pub const WrongSideDeduction: u64 = 2;
	pub const MaxStrikes: u32 = 2;
	pub const RotationPeriod: u64 = 4;
	pub const PeriodSpend: u64 = 1000;
	pub const MaxLockDuration: u64 = 100;
	pub const ChallengePeriod: u64 = 8;
	pub const BlockHashCount: u64 = 250;
	pub const ExistentialDeposit: u64 = 1;
	pub const MaxCandidateIntake: u32 = 10;
	pub const SocietyPalletId: PalletId = PalletId(*b"py/socie");
	pub const ActionByteDeposit: u64 = 1;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) * BlockWeights::get().max_block;
	pub const MaxScheduledPerBlock: u32 = 50;
	pub const SchedulerBlocksOffset: u32 = 4;
}

ord_parameter_types! {
	pub const FounderSetAccount: u128 = 1;
	pub const SocietySubAccount: &'static [u8] = b"society";
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u128;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}

impl pallet_scheduler::Config for Test {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = frame_system::EnsureRoot<u128>;
	type MaxScheduledPerBlock = MaxScheduledPerBlock;
	type WeightInfo = ();
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

impl Config for Test {
	type Event = Event;
	type SocietySubAccount = SocietySubAccount;
	type Currency = pallet_balances::Pallet<Self>;
	type Randomness = TestRandomness<Self>;
	type CandidateDeposit = CandidateDeposit;
	type WrongSideDeduction = WrongSideDeduction;
	type MaxStrikes = MaxStrikes;
	type PeriodSpend = PeriodSpend;
	type MembershipChanged = ();
	type RotationPeriod = RotationPeriod;
	type MaxLockDuration = MaxLockDuration;
	type FounderSetOrigin = EnsureSignedBy<FounderSetAccount, u128>;
	type SuspensionJudgementOrigin = EnsureOneOf<u128, EnsureFounder<Test>, EnsureSociety<Test>>;
	type ChallengePeriod = ChallengePeriod;
	type MaxCandidateIntake = MaxCandidateIntake;
	type PalletId = SocietyPalletId;
	type Call = Call;
	type ActionByteDeposit = ActionByteDeposit;
	type PalletsOrigin = OriginCaller;
	type Scheduler = Scheduler;
	type SchedulerBlocksOffset = SchedulerBlocksOffset;
}

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
				(100, 50),
			],
			pot: 0,
			max_members: 100,
		}
	}

	pub fn execute<R, F: FnOnce() -> R>(mut self, f: F) -> R {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		self.balances.push((Society::treasury(), self.balance.max(self.pot)));
		pallet_balances::GenesisConfig::<Test> { balances: self.balances }
			.assimilate_storage(&mut t)
			.unwrap();
		pallet_society::GenesisConfig::<Test> {
			members: self.members,
			pot: self.pot,
			max_members: self.max_members,
		}
		.assimilate_storage(&mut t)
		.unwrap();
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
		Scheduler::on_initialize(System::block_number());
	}
}

/// Creates a bid struct using input parameters.
pub fn create_bid<AccountId, Balance, Call>(
	value: Balance,
	who: AccountId,
	kind: BidKind<AccountId, Balance, Call>,
) -> Bid<AccountId, Balance, Call> {
	Bid { who, kind, value }
}

type BalancesCall = pallet_balances::Call<Test>;
type SocietyCall = pallet_society::Call<Test>;

/// Returns the founder account.
pub fn society_founder() -> u128 {
	Society::founder().unwrap()
}

/// Returns the society account.
pub fn society_account() -> u128 {
	Society::account().unwrap()
}

/// Creates a transfer Call to be used by bid_action().
pub fn call_transfer(dest: u128, value: u64) -> Call {
	Call::Balances(BalancesCall::transfer { dest, value })
}

/// Creates a judge_suspended_member Call to be used by bid_action().
pub fn call_judge_suspended_member(who: u128, forgive: bool) -> Call {
	Call::Society(SocietyCall::judge_suspended_member { who, forgive })
}

/// Creates a judge_suspended_candidate Call to be used by bid_action().
pub fn call_judge_suspended_candidate(who: u128, judgement: Judgement) -> Call {
	Call::Society(SocietyCall::judge_suspended_candidate { who, judgement })
}
