// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use super::*;
use crate as pallet_safe_mode;

use frame_support::{
	parameter_types,
	traits::{ConstU64, Everything, InsideBoth, InstanceFilter, IsInVec},
};
use frame_system::EnsureSignedBy;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

impl frame_system::Config for Test {
	type BaseCallFilter = InsideBoth<Everything, SafeMode>;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
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

/// Identifies a hold on an account's balance.
#[derive(
	Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Encode, Decode, MaxEncodedLen, Debug, TypeInfo,
)]
pub enum HoldReason {
	/// The safe-mode pallet holds funds since an account either entered or extended the safe-mode.
	SafeMode,
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<2>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ConstU32<10>;
	type ReserveIdentifier = Self::BlockNumber;
	type HoldIdentifier = HoldReason;
	type FreezeIdentifier = ();
	type MaxHolds = ConstU32<10>;
	type MaxFreezes = ConstU32<0>;
}

impl pallet_utility::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
}

/// Mocked proxies to check that the safe-mode also works with the proxy pallet.
#[derive(
	Copy,
	Clone,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	Encode,
	Decode,
	RuntimeDebug,
	MaxEncodedLen,
	scale_info::TypeInfo,
)]
pub enum ProxyType {
	Any,
	JustTransfer,
	JustUtility,
}

impl Default for ProxyType {
	fn default() -> Self {
		Self::Any
	}
}

impl InstanceFilter<RuntimeCall> for ProxyType {
	fn filter(&self, c: &RuntimeCall) -> bool {
		match self {
			ProxyType::Any => true,
			ProxyType::JustTransfer => {
				matches!(c, RuntimeCall::Balances(pallet_balances::Call::transfer { .. }))
			},
			ProxyType::JustUtility => matches!(c, RuntimeCall::Utility { .. }),
		}
	}
	fn is_superset(&self, o: &Self) -> bool {
		self == &ProxyType::Any || self == o
	}
}

impl pallet_proxy::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type Currency = Balances;
	type ProxyType = ProxyType;
	type ProxyDepositBase = ConstU64<1>;
	type ProxyDepositFactor = ConstU64<1>;
	type MaxProxies = ConstU32<4>;
	type WeightInfo = ();
	type CallHasher = BlakeTwo256;
	type MaxPending = ConstU32<2>;
	type AnnouncementDepositBase = ConstU64<1>;
	type AnnouncementDepositFactor = ConstU64<1>;
}

/// The calls that can always bypass the safe-mode.
pub struct WhitelistedCalls;
impl Contains<RuntimeCall> for WhitelistedCalls {
	fn contains(call: &RuntimeCall) -> bool {
		match call {
			RuntimeCall::Balances(_) => false,
			_ => true,
		}
	}
}

parameter_types! {
	pub const EnterDuration: u64 = 7;
	pub const ExtendDuration: u64 = 30;
	pub const EnterStakeAmount: u64 = 100;
	pub const ExtendStakeAmount: u64 = 100;
	pub const ReleaseDelay: u64 = 20;
	pub const SafeModeHoldReason: HoldReason = HoldReason::SafeMode;

	pub const ForceEnterWeak: u64 = 3;
	pub const ForceEnterStrong: u64 = 5;

	pub const ForceExtendWeak: u64 = 11;
	pub const ForceExtendStrong: u64 = 15;

	// NOTE: The account ID maps to the duration. Easy for testing.
	pub ForceEnterOrigins: Vec<u64> = vec![ForceEnterWeak::get(), ForceEnterStrong::get()];
	pub ForceExtendOrigins: Vec<u64> = vec![ForceExtendWeak::get(), ForceExtendStrong::get()];
}

frame_support::ord_parameter_types! {
	pub const ForceExitOrigin: u64 = 100;
	pub const ForceStakeOrigin: u64 = 200;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type HoldReason = SafeModeHoldReason;
	type WhitelistedCalls = WhitelistedCalls;
	type EnterDuration = EnterDuration;
	type EnterStakeAmount = EnterStakeAmount;
	type ExtendDuration = ExtendDuration;
	type ExtendStakeAmount = ExtendStakeAmount;
	type ForceEnterOrigin = EnsureSignedBy<IsInVec<ForceEnterOrigins>, u64>;
	type ForceExtendOrigin = EnsureSignedBy<IsInVec<ForceExtendOrigins>, u64>;
	type ForceExitOrigin = EnsureSignedBy<ForceExitOrigin, Self::AccountId>;
	type ForceStakeOrigin = EnsureSignedBy<ForceStakeOrigin, Self::AccountId>;
	type ReleaseDelay = ReleaseDelay;
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
		Utility: pallet_utility,
		Proxy: pallet_proxy,
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
		&pallet_safe_mode::GenesisConfig { entered_until: None, _phantom: Default::default() },
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
