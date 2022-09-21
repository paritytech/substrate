// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Test utilities for safe mode pallet.

use super::*;
use crate as pallet_safe_mode;

use frame_support::{
	parameter_types,
	traits::{Everything, InsideBoth, SortedMembers},
};
use frame_system::{EnsureSignedBy, RawOrigin};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};

parameter_types! {
	pub const BlockHashCount: u64 = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = InsideBoth<Everything, SafeMode>;
	type BlockWeights = ();
	type BlockLength = ();
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub const MaxLocks: u32 = 10;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = MaxLocks;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

/// Filter to block balance pallet calls
pub struct MockSafeModeFilter;
impl Contains<Call> for MockSafeModeFilter {
	fn contains(call: &Call) -> bool {
		match call {
			Call::System(_) | Call::SafeMode(_) => true,
			Call::Balances(_) => false,
		}
	}
}

/// An origin that can enable the safe-mode by force.
pub enum ForceEnableOrigin {
	Weak,
	Medium,
	Strong,
}

/// An origin that can extend the safe-mode by force.
pub enum ForceExtendOrigin {
	Weak,
	Medium,
	Strong,
}

impl ForceEnableOrigin {
	/// The duration of how long the safe-mode will be enabled.
	pub fn duration(&self) -> u64 {
		match self {
			Self::Weak => 5,
			Self::Medium => 7,
			Self::Strong => 11,
		}
	}

	/// Account id of the origin.
	pub const fn acc(&self) -> u64 {
		match self {
			Self::Weak => 100,
			Self::Medium => 101,
			Self::Strong => 102,
		}
	}

	/// Signed origin.
	pub fn signed(&self) -> <Test as frame_system::Config>::Origin {
		RawOrigin::Signed(self.acc()).into()
	}
}

impl ForceExtendOrigin {
	/// The duration of how long the safe-mode will be extended.
	pub fn duration(&self) -> u64 {
		match self {
			Self::Weak => 13,
			Self::Medium => 17,
			Self::Strong => 19,
		}
	}

	/// Account id of the origin.
	pub const fn acc(&self) -> u64 {
		match self {
			Self::Weak => 200,
			Self::Medium => 201,
			Self::Strong => 202,
		}
	}

	/// Signed origin.
	pub fn signed(&self) -> <Test as frame_system::Config>::Origin {
		RawOrigin::Signed(self.acc()).into()
	}
}

impl<O: Into<Result<RawOrigin<u64>, O>> + From<RawOrigin<u64>> + std::fmt::Debug> EnsureOrigin<O>
	for ForceEnableOrigin
{
	type Success = u64;

	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(acc) if acc == ForceEnableOrigin::Weak.acc() =>
				Ok(ForceEnableOrigin::Weak.duration()),
			RawOrigin::Signed(acc) if acc == ForceEnableOrigin::Medium.acc() =>
				Ok(ForceEnableOrigin::Medium.duration()),
			RawOrigin::Signed(acc) if acc == ForceEnableOrigin::Strong.acc() =>
				Ok(ForceEnableOrigin::Strong.duration()),
			r => Err(O::from(r)),
		})
	}
}

impl<O: Into<Result<RawOrigin<u64>, O>> + From<RawOrigin<u64>> + std::fmt::Debug> EnsureOrigin<O>
	for ForceExtendOrigin
{
	type Success = u64;

	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(acc) if acc == ForceExtendOrigin::Weak.acc() =>
				Ok(ForceExtendOrigin::Weak.duration()),
			RawOrigin::Signed(acc) if acc == ForceExtendOrigin::Medium.acc() =>
				Ok(ForceExtendOrigin::Medium.duration()),
			RawOrigin::Signed(acc) if acc == ForceExtendOrigin::Strong.acc() =>
				Ok(ForceExtendOrigin::Strong.duration()),
			r => Err(O::from(r)),
		})
	}
}

parameter_types! {
	pub const EnableDuration: u64 = 3;
	pub const ExtendDuration: u64 = 30;
	pub const EnableStakeAmount: u64 = 100; //TODO This needs to be something sensible for the implications of enablement!
	pub const ExtendStakeAmount: u64 = 100; //TODO This needs to be something sensible for the implications of enablement!
	pub const DisableOrigin: u64 =3;
	pub const RepayOrigin: u64 = 4;
}

// Required impl to use some <Configured Origin>::get() in tests
impl SortedMembers<u64> for DisableOrigin {
	fn sorted_members() -> Vec<u64> {
		vec![Self::get()]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}
impl SortedMembers<u64> for RepayOrigin {
	fn sorted_members() -> Vec<u64> {
		vec![Self::get()]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}

impl Config for Test {
	type Event = Event;
	type Currency = Balances;
	type SafeModeFilter = MockSafeModeFilter;
	type EnableDuration = EnableDuration;
	type ExtendDuration = ExtendDuration;
	type EnableOrigin = ForceEnableOrigin;
	type ExtendOrigin = ForceExtendOrigin;
	type DisableOrigin = EnsureSignedBy<DisableOrigin, Self::AccountId>;
	type RepayOrigin = EnsureSignedBy<RepayOrigin, Self::AccountId>;
	type EnableStakeAmount = EnableStakeAmount;
	type ExtendStakeAmount = ExtendStakeAmount;
	type WeightInfo = ();
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		SafeMode: pallet_safe_mode,
	}
);

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(0, 1234), (1, 5678), (2, 5678), (3, 5678), (4, 5678)], /* The 0 account
		                                                                        * is NOT a special
		                                                                        * origin, the
		                                                                        * rest may be. */
	}
	.assimilate_storage(&mut t)
	.unwrap();

	// TODO requires a GenesisConfig impl
	// GenesisBuild::<Test>::assimilate_storage(
	// 	&pallet_safe_mode::GenesisConfig {
	// 		enabled: None,
	// 		stakes: None,
	// 	},
	// 	&mut t,
	// )
	// .unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		System::set_block_number(1);
	});
	ext
}

#[cfg(feature = "runtime-benchmarks")]
pub fn new_bench_ext() -> sp_io::TestExternalities {
	GenesisConfig::default().build_storage().unwrap().into()
}

pub fn next_block() {
	SafeMode::on_finalize(System::block_number());
	Balances::on_finalize(System::block_number());
	System::on_finalize(System::block_number());
	System::set_block_number(System::block_number() + 1);
	System::on_initialize(System::block_number());
	Balances::on_initialize(System::block_number());
	SafeMode::on_initialize(System::block_number());
}

pub fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}
