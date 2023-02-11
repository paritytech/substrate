// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

use crate::{self as pallet_stake_tracker, *};
use frame_election_provider_support::{ScoreProvider, VoteWeight};
use frame_support::{parameter_types, weights::constants::RocksDbWeight};
use sp_runtime::{
	testing::{Header, H256},
	traits::IdentityLookup,
	DispatchError, DispatchResult,
};
use sp_staking::{EraIndex, Stake, StakingInterface};
use Currency;

pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u128;

type Block = frame_system::mocking::MockBlock<Runtime>;
type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		VoterBagsList: pallet_bags_list::<Instance1>::{Pallet, Call, Storage, Event<T>},
		StakeTracker: pallet_stake_tracker::{Pallet, Storage},
	}
);

parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = RocksDbWeight;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = frame_support::traits::ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = frame_support::traits::ConstU32<1024>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

impl pallet_stake_tracker::Config for Runtime {
	type Currency = Balances;
	type Staking = StakingMock;
	type VoterList = VoterBagsList;
}
const THRESHOLDS: [sp_npos_elections::VoteWeight; 9] =
	[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
}

type VoterBagsListInstance = pallet_bags_list::Instance1;
impl pallet_bags_list::Config<VoterBagsListInstance> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	// Staking is the source of truth for voter bags list, since they are not kept up to date.
	type ScoreProvider = StakingMock;
	type BagThresholds = BagThresholds;
	type Score = VoteWeight;
}

pub struct StakingMock {}

// We don't really care about this yet in the context of testing stake-tracker logic.
impl ScoreProvider<AccountId> for StakingMock {
	type Score = VoteWeight;

	fn score(_id: &AccountId) -> Self::Score {
		VoteWeight::default()
	}

	frame_election_provider_support::runtime_benchmarks_or_test_enabled! {
		fn set_score_of(_: &AccountId, _: Self::Score) {
			// not use yet.
		}
	}
}

impl StakingInterface for StakingMock {
	type Balance = Balance;
	type AccountId = AccountId;
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;

	fn minimum_nominator_bond() -> Self::Balance {
		unreachable!();
	}

	fn minimum_validator_bond() -> Self::Balance {
		unreachable!();
	}

	fn stash_by_ctrl(_: &Self::AccountId) -> Result<Self::AccountId, DispatchError> {
		unreachable!();
	}

	fn bonding_duration() -> EraIndex {
		unreachable!();
	}

	fn current_era() -> EraIndex {
		unreachable!();
	}

	fn stake(
		who: &Self::AccountId,
	) -> Result<Stake<Self::AccountId, Self::Balance>, DispatchError> {
		if *who >= 30 {
			return Err(DispatchError::Other("not bonded"))
		}
		let stake = Balances::total_balance(who);
		Ok(Stake {
			stash: *who,
			active: stake.saturating_sub(ExistentialDeposit::get()),
			total: stake,
		})
	}

	fn bond(_: &Self::AccountId, _: Self::Balance, _: &Self::AccountId) -> DispatchResult {
		unreachable!();
	}

	fn nominate(_: &Self::AccountId, _: Vec<Self::AccountId>) -> DispatchResult {
		unreachable!();
	}

	fn chill(_: &Self::AccountId) -> DispatchResult {
		unreachable!();
	}

	fn bond_extra(_: &Self::AccountId, _: Self::Balance) -> DispatchResult {
		unreachable!();
	}

	fn unbond(_: &Self::AccountId, _: Self::Balance) -> DispatchResult {
		unreachable!();
	}

	fn withdraw_unbonded(_: Self::AccountId, _: u32) -> Result<bool, DispatchError> {
		unreachable!();
	}

	fn desired_validator_count() -> u32 {
		unreachable!();
	}

	fn election_ongoing() -> bool {
		unreachable!();
	}

	fn force_unstake(_: Self::AccountId) -> DispatchResult {
		unreachable!();
	}

	fn is_exposed_in_era(_: &Self::AccountId, _: &EraIndex) -> bool {
		unreachable!();
	}

	fn is_validator(who: &Self::AccountId) -> bool {
		*who >= 10 && *who <= 14
	}

	fn nominations(who: &Self::AccountId) -> Option<Vec<Self::AccountId>> {
		if *who >= 20 && *who <= 24 {
			Some(Vec::new())
		} else {
			None
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_era_stakers(
		_: &EraIndex,
		_: &Self::AccountId,
		_: Vec<(Self::AccountId, Self::Balance)>,
	) {
		unreachable!();
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn set_current_era(_: EraIndex) {
		unreachable!();
	}
}

#[derive(Default)]
pub struct ExtBuilder {}

impl ExtBuilder {
	fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();

		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![
				// Random users, used to test some edge-cases, where we don't want the user to be
				// neither a nominator nor validator.
				(1, 10),
				(2, 20),
				(3, 30),
				// Validator stashes, for simplicity we assume stash == controller as StakeTracker
				// really does not care.
				(10, 10),
				(11, 20),
				(12, 30),
				(13, 40),
				(14, 50),
				// nominators
				(20, 10),
				(21, 20),
				(22, 30),
				(23, 40),
				(24, 50),
			],
		}
		.assimilate_storage(&mut storage);

		let ext = sp_io::TestExternalities::from(storage);

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		sp_tracing::try_init_simple();
		let mut ext = self.build();
		ext.execute_with(test);
	}
}
