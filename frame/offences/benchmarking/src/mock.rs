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

//! Mock file for offences benchmarking.

#![cfg(test)]

use super::*;
use frame_election_provider_support::onchain;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
	weights::constants::WEIGHT_PER_SECOND,
};
use frame_system as system;
use pallet_session::historical as pallet_session_historical;
use sp_runtime::{
	testing::{Header, UintAuthorityId},
	traits::IdentityLookup,
};

type AccountId = u64;
type AccountIndex = u32;
type BlockNumber = u64;
type Balance = u64;

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(2 * WEIGHT_PER_SECOND);
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
	type BlockHashCount = ();
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
	pub const ExistentialDeposit: Balance = 10;
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<5>;
	type WeightInfo = ();
}
impl pallet_session::historical::Config for Test {
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
	) {
	}

	fn on_disabled(_: u32) {}
}

parameter_types! {
	pub const Period: u64 = 1;
	pub const Offset: u64 = 0;
}

impl pallet_session::Config for Test {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = TestSessionHandler;
	type Event = Event;
	type ValidatorId = AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Test>;
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
}

pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

impl onchain::Config for Test {
	type Accuracy = Perbill;
	type DataProvider = Staking;
}

impl pallet_staking::Config for Test {
	const MAX_NOMINATIONS: u32 = 16;
	type Currency = Balances;
	type UnixTime = pallet_timestamp::Pallet<Self>;
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
	type RewardRemainder = ();
	type Event = Event;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = ();
	type SlashDeferDuration = ();
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = ();
	type SessionInterface = Self;
	type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
	type NextNewSession = Session;
	type MaxNominatorRewardedPerValidator = ConstU32<64>;
	type OffendingValidatorsThreshold = ();
	type ElectionProvider = onchain::OnChainSequentialPhragmen<Self>;
	type GenesisElectionProvider = Self::ElectionProvider;
	type SortedListProvider = pallet_staking::UseNominatorsMap<Self>;
	type BenchmarkingConfig = pallet_staking::TestBenchmarkingConfig;
	type WeightInfo = ();
}

impl pallet_im_online::Config for Test {
	type AuthorityId = UintAuthorityId;
	type Event = Event;
	type ValidatorSet = Historical;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type ReportUnresponsiveness = Offences;
	type UnsignedPriority = ();
	type WeightInfo = ();
	type MaxKeys = ConstU32<10_000>;
	type MaxPeerInHeartbeats = ConstU32<10_000>;
	type MaxPeerDataEncodingSize = ConstU32<1_000>;
}

impl pallet_offences::Config for Test {
	type Event = Event;
	type IdentificationTuple = pallet_session::historical::IdentificationTuple<Self>;
	type OnOffenceHandler = Staking;
}

impl<T> frame_system::offchain::SendTransactionTypes<T> for Test
where
	Call: From<T>,
{
	type Extrinsic = Extrinsic;
	type OverarchingCall = Call;
}

impl crate::Config for Test {}

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, Call, u64, ()>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Call, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Staking: pallet_staking::{Pallet, Call, Config<T>, Storage, Event<T>},
		Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
		ImOnline: pallet_im_online::{Pallet, Call, Storage, Event<T>, ValidateUnsigned, Config<T>},
		Offences: pallet_offences::{Pallet, Storage, Event},
		Historical: pallet_session_historical::{Pallet},
	}
);

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	sp_io::TestExternalities::new(t)
}
