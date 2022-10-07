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
};

parameter_types! {
	pub const BlockHashCount: u64 = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = InsideBoth<Everything, SafeMode>;
	type BlockWeights = ();
	type BlockLength = ();
	type Origin = Origin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
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
	pub const MaxReserves: u32 = 10;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = Self::BlockNumber;
}

/// Filter to block balance pallet calls
pub struct MockUnfilterableCalls;
impl Contains<RuntimeCall> for MockUnfilterableCalls {
	fn contains(call: &RuntimeCall) -> bool {
		match call {
			RuntimeCall::System(_) | RuntimeCall::SafeMode(_) => true,
			RuntimeCall::Balances(_) => false,
		}
	}
}

/// An origin that can enable the safe-mode by force.
pub enum ForceActivateOrigin {
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

impl ForceActivateOrigin {
	/// The duration of how long the safe-mode will be activated.
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
	for ForceActivateOrigin
{
	type Success = u64;

	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(acc) if acc == ForceActivateOrigin::Weak.acc() =>
				Ok(ForceActivateOrigin::Weak.duration()),
			RawOrigin::Signed(acc) if acc == ForceActivateOrigin::Medium.acc() =>
				Ok(ForceActivateOrigin::Medium.duration()),
			RawOrigin::Signed(acc) if acc == ForceActivateOrigin::Strong.acc() =>
				Ok(ForceActivateOrigin::Strong.duration()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Signed(ForceActivateOrigin::Strong.acc()))
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

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Signed(ForceExtendOrigin::Strong.acc()))
	}
}

parameter_types! {
	pub const SignedActivationDuration: u64 = 3;
	pub const SignedExtendDuration: u64 = 30;
	pub const ActivateReservationAmount: u64 = 100;
	pub const ExtendReservationAmount: u64 = 100;
	pub const ForceDeactivateOrigin: u64 = 3;
	pub const RepayOrigin: u64 = 4;
}

// Required impl to use some <Configured Origin>::get() in tests
impl SortedMembers<u64> for ForceDeactivateOrigin {
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
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type UnfilterableCalls = MockUnfilterableCalls;
	type SignedActivationDuration = SignedActivationDuration;
	type ActivateReservationAmount = ActivateReservationAmount;
	type SignedExtendDuration = SignedExtendDuration;
	type ExtendReservationAmount = ExtendReservationAmount;
	type ForceActivateOrigin = ForceActivateOrigin;
	type ForceExtendOrigin = ForceExtendOrigin;
	type ForceDeactivateOrigin = EnsureSignedBy<ForceDeactivateOrigin, Self::AccountId>;
	type RepayOrigin = EnsureSignedBy<RepayOrigin, Self::AccountId>;
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
		// The 0 account is NOT a special origin, the rest may be.
		balances: vec![(0, 1234), (1, 5678), (2, 5678), (3, 5678), (4, 5678)],
	}
	.assimilate_storage(&mut t)
	.unwrap();

	GenesisBuild::<Test>::assimilate_storage(
		&pallet_safe_mode::GenesisConfig { active: None, _phantom: Default::default() },
		&mut t,
	)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		System::set_block_number(1);
	});
	ext
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
