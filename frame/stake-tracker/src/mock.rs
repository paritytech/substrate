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

#![cfg(test)]

use crate::{self as pallet_stake_tracker, *};

use frame_election_provider_support::{ScoreProvider, VoteWeight};
use frame_support::{derive_impl, parameter_types, traits::ConstU32};
use sp_runtime::BuildStorage;
use sp_staking::StakingInterface;

pub(crate) type AccountId = u64;
pub(crate) type Balance = u64;

type Block = frame_system::mocking::MockBlockU32<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system,
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		VoterBagsList: pallet_bags_list::<Instance1>::{Pallet, Call, Storage, Event<T>},
		TargetBagsList: pallet_bags_list::<Instance2>::{Pallet, Call, Storage, Event<T>},
		StakeTracker: crate,
	}
);

parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
}

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Test {
	type Block = Block;
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockHashCount = ConstU32<10>;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();

	type AccountData = pallet_balances::AccountData<Balance>;
}

impl pallet_balances::Config for Test {
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = frame_support::traits::ConstU32<1024>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type FreezeIdentifier = ();
	type MaxHolds = ();
	type RuntimeHoldReason = ();
	type MaxFreezes = ();
}

const THRESHOLDS: [sp_npos_elections::VoteWeight; 9] =
	[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [VoteWeight] = &THRESHOLDS;
}

type VoterBagsListInstance = pallet_bags_list::Instance1;
impl pallet_bags_list::Config<VoterBagsListInstance> for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type ScoreProvider = StakingMock;
	type BagThresholds = BagThresholds;
	type Score = VoteWeight;
}

type TargetBagsListInstance = pallet_bags_list::Instance2;
impl pallet_bags_list::Config<TargetBagsListInstance> for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type ScoreProvider = StakingMock;
	type BagThresholds = BagThresholds;
	type Score = <StakingMock as StakingInterface>::Balance;
}

impl pallet_stake_tracker::Config for Test {
	type Currency = Balances;

	type Staking = StakingMock;
	type VoterList = VoterBagsList;
	type TargetList = TargetBagsList;
}

pub struct StakingMock {}

impl ScoreProvider<AccountId> for StakingMock {
	type Score = VoteWeight;

	fn score(_id: &AccountId) -> Self::Score {
		todo!();
	}

	fn set_score_of(_: &AccountId, _: Self::Score) {
		unreachable!();
	}
}

impl StakingInterface for StakingMock {
	type Balance = Balance;
	type AccountId = AccountId;
	type CurrencyToVote = ();

	fn minimum_nominator_bond() -> Self::Balance {
		unreachable!();
	}

	fn minimum_validator_bond() -> Self::Balance {
		unreachable!();
	}

	fn stash_by_ctrl(
		_controller: &Self::AccountId,
	) -> Result<Self::AccountId, sp_runtime::DispatchError> {
		unreachable!();
	}

	fn bonding_duration() -> sp_staking::EraIndex {
		unreachable!();
	}

	fn current_era() -> sp_staking::EraIndex {
		unreachable!();
	}

	fn stake(
		_who: &Self::AccountId,
	) -> Result<sp_staking::Stake<Self::Balance>, sp_runtime::DispatchError> {
		unreachable!();
	}

	fn bond(
		_who: &Self::AccountId,
		_value: Self::Balance,
		_payee: &Self::AccountId,
	) -> sp_runtime::DispatchResult {
		unreachable!();
	}

	fn nominate(
		_who: &Self::AccountId,
		_validators: Vec<Self::AccountId>,
	) -> sp_runtime::DispatchResult {
		unreachable!();
	}

	fn chill(_who: &Self::AccountId) -> sp_runtime::DispatchResult {
		unreachable!();
	}

	fn bond_extra(_who: &Self::AccountId, _extra: Self::Balance) -> sp_runtime::DispatchResult {
		unreachable!();
	}

	fn withdraw_unbonded(
		_stash: Self::AccountId,
		_num_slashing_spans: u32,
	) -> Result<bool, sp_runtime::DispatchError> {
		unreachable!();
	}

	fn desired_validator_count() -> u32 {
		unreachable!();
	}

	fn election_ongoing() -> bool {
		unreachable!();
	}

	fn force_unstake(_who: Self::AccountId) -> sp_runtime::DispatchResult {
		unreachable!();
	}

	fn is_exposed_in_era(_who: &Self::AccountId, _era: &sp_staking::EraIndex) -> bool {
		unreachable!();
	}

	fn status(
		_who: &Self::AccountId,
	) -> Result<sp_staking::StakerStatus<Self::AccountId>, sp_runtime::DispatchError> {
		unreachable!();
	}

	fn unbond(_stash: &Self::AccountId, _value: Self::Balance) -> sp_runtime::DispatchResult {
		unreachable!();
	}
}

#[derive(Default)]
pub struct ExtBuilder {}

impl ExtBuilder {
	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let storage = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
		sp_io::TestExternalities::from(storage)
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		sp_tracing::try_init_simple();

		let mut ext = self.build();
		ext.execute_with(test);
	}
}
