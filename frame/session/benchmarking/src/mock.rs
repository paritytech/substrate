// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Mock file for session benchmarking.

#![cfg(test)]

use sp_runtime::traits::{Convert, SaturatedConversion, IdentityLookup};
use frame_support::{impl_outer_origin, impl_outer_dispatch, parameter_types};

type AccountId = u64;
type AccountIndex = u32;
type BlockNumber = u64;
type Balance = u64;

type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Staking = pallet_staking::Module<Test>;
type Session = pallet_session::Module<Test>;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		pallet_staking::Staking,
	}
}

pub struct CurrencyToVoteHandler;
impl Convert<u64, u64> for CurrencyToVoteHandler {
	fn convert(x: u64) -> u64 {
		x
	}
}
impl Convert<u128, u64> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u64 {
		x.saturated_into()
	}
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;

impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = ();
	type BlockHashCount = ();
	type MaximumBlockWeight = ();
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = ();
	type AvailableBlockRatio = ();
	type MaximumBlockLength = ();
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = Balances;
	type SystemWeightInfo = ();
}
parameter_types! {
	pub const ExistentialDeposit: Balance = 10;
}
impl pallet_balances::Trait for Test {
	type Balance = Balance;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub const MinimumPeriod: u64 = 5;
}
impl pallet_timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}
impl pallet_session::historical::Trait for Test {
	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Test>;
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {
		pub foo: sp_runtime::testing::UintAuthorityId,
	}
}

pub struct TestSessionHandler;
impl pallet_session::SessionHandler<AccountId> for TestSessionHandler {
	const KEY_TYPE_IDS: &'static [sp_runtime::KeyTypeId] = &[];

	fn on_genesis_session<Ks: sp_runtime::traits::OpaqueKeys>(_validators: &[(AccountId, Ks)]) {}

	fn on_new_session<Ks: sp_runtime::traits::OpaqueKeys>(
		_: bool,
		_: &[(AccountId, Ks)],
		_: &[(AccountId, Ks)],
	) {}

	fn on_disabled(_: usize) {}
}

impl pallet_session::Trait for Test {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<(), ()>;
	type NextSessionRotation = pallet_session::PeriodicSessions<(), ()>;
	type SessionHandler = TestSessionHandler;
	type Event = ();
	type ValidatorId = AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Test>;
	type DisabledValidatorsThreshold = ();
	type WeightInfo = ();
}
pallet_staking_reward_curve::build! {
	const I_NPOS: sp_runtime::curve::PiecewiseLinear<'static> = curve!(
		min_inflation: 0_025_000,
		max_inflation: 0_100_000,
		ideal_stake: 0_500_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}
parameter_types! {
	pub const RewardCurve: &'static sp_runtime::curve::PiecewiseLinear<'static> = &I_NPOS;
	pub const MaxNominatorRewardedPerValidator: u32 = 64;
	pub const UnsignedPriority: u64 = 1 << 20;
}

pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

impl<C> frame_system::offchain::SendTransactionTypes<C> for Test where
	Call: From<C>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

impl pallet_staking::Trait for Test {
	type Currency = Balances;
	type UnixTime = pallet_timestamp::Module<Self>;
	type CurrencyToVote = CurrencyToVoteHandler;
	type RewardRemainder = ();
	type Event = ();
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = ();
	type SlashDeferDuration = ();
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = ();
	type SessionInterface = Self;
	type RewardCurve = RewardCurve;
	type NextNewSession = Session;
	type ElectionLookahead = ();
	type Call = Call;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type UnsignedPriority = UnsignedPriority;
	type MaxIterations = ();
	type MinSolutionScoreBump = ();
	type WeightInfo = ();
}

impl crate::Trait for Test {}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	sp_io::TestExternalities::new(t)
}
