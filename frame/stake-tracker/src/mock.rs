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
use std::collections::BTreeMap;

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
		// TODO: we should remove this. This is ONLY needed because of this to_vote_weight
		// calculation which might ver well happen in the staking side. For now balances should NOT
		// be used anywhere here. Note that we are using SaturatingCurrencyToVote which ignores the
		// issuance value.
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
	type HoldIdentifier = ();
	type FreezeIdentifier = ();
	type MaxHolds = ();
	type MaxFreezes = ();
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

pub struct StakingMock;

// We don't really care about this yet in the context of testing stake-tracker logic.
impl ScoreProvider<AccountId> for StakingMock {
	type Score = VoteWeight;

	fn score(_id: &AccountId) -> Self::Score {
		todo!();
	}

	frame_election_provider_support::runtime_benchmarks_or_test_enabled! {
		fn set_score_of(_: &AccountId, _: Self::Score) {
			unreachable!();
		}
	}
}

// some nominators and validators that are ready to be reported.
parameter_types! {
	pub static TestNominators: BTreeMap<AccountId, Balance> = Default::default();
	pub static TestValidators: BTreeMap<AccountId, Balance> = Default::default();
}

pub(crate) fn set_nominator_stake(who: AccountId, stake: Balance) {
	let old_stake = StakingMock::stake(&who).unwrap();
	TestNominators::mutate(|x| {
		*x.get_mut(&who).unwrap() = stake;
	});
	StakeTracker::on_stake_update(&who, Some(old_stake));
}

pub(crate) fn add_nominator(who: AccountId, stake: Balance) {
	TestNominators::mutate(|x| {
		x.insert(who, stake);
	});
	// TODO: check how the flow is on the staking side.
	StakeTracker::on_nominator_add(&who);
	StakeTracker::on_stake_update(&who, None);
}

pub(crate) fn add_validator(who: AccountId, stake: Balance) {
	TestValidators::mutate(|x| {
		x.insert(who, stake);
	});
	// TODO: check how the flow is on the staking side.
	StakeTracker::on_validator_add(&who);
	StakeTracker::on_stake_update(&who, None);
}

pub(crate) fn set_validator_stake(who: AccountId, stake: Balance) {
	let old_stake = StakingMock::stake(&who).unwrap();
	TestValidators::mutate(|x| {
		*x.get_mut(&who).unwrap() = stake;
	});
	StakeTracker::on_stake_update(&who, Some(old_stake));
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
		let stake = TestNominators::get()
			.get(who)
			.cloned()
			.or_else(|| TestValidators::get().get(who).cloned())
			.ok_or(DispatchError::Other("not bonded"))?;
		Ok(Stake { stash: *who, active: stake, total: stake })
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
		TestValidators::get().contains_key(who)
	}

	fn nominations(who: &Self::AccountId) -> Option<Vec<Self::AccountId>> {
		if TestNominators::get().contains_key(who) {
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
		let storage = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		let mut ext = sp_io::TestExternalities::from(storage);

		// we have some initial accounts, spread across different bags. for simplicity, all
		// account's balance is equal to their account id.
		// validator accounts start from the boundary of bags, eg 10, 11 etc.
		// nominator accounts start from the middle of the bag, eg 5, 15 etc.
		// given that we don't care about the order within bags here, we stick to one node per bag.
		ext.execute_with(|| {
			for x in [10, 20, 30] {
				add_validator(x, x.into());
			}
			for x in [5, 15, 25] {
				add_nominator(x, x.into());
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		sp_tracing::try_init_simple();
		let mut ext = self.build();
		ext.execute_with(test);
		// TODO: call try_state of `AllPallets`.
	}
}
