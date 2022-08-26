// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use super::*;
use crate::{self as fast_unstake};
use frame_support::{
	assert_ok,
	pallet_prelude::*,
	parameter_types,
	traits::{ConstU64, ConstU8, Currency},
	PalletId,
};
use sp_runtime::{
	traits::{Convert, IdentityLookup},
	FixedU128,
};

use frame_system::RawOrigin;
use pallet_nomination_pools::{BondedPools, LastPoolId, PoolId, PoolState};
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};

pub type AccountId = u128;
pub type AccountIndex = u32;
pub type BlockNumber = u64;
pub type Balance = u128;

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
	type BlockHashCount = ();
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

impl pallet_timestamp::Config for Runtime {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<5>;
	type WeightInfo = ();
}

parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
}

impl pallet_balances::Config for Runtime {
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
	pub static BondingDuration: u32 = 3;
	pub static MinJoinBondConfig: Balance = 2;
	pub static CurrentEra: u32 = 0;
	pub storage BondedBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	pub storage UnbondingBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	#[derive(Clone, PartialEq)]
	pub static MaxUnbonding: u32 = 8;
	pub static StakingMinBond: Balance = 10;
	pub storage Nominations: Option<Vec<AccountId>> = None;
}

impl pallet_staking::Config for Runtime {
	type MaxNominations = ConstU32<16>;
	type Currency = Balances;
	type CurrencyBalance = Balance;
	type UnixTime = pallet_timestamp::Pallet<Self>;
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
	type RewardRemainder = ();
	type Event = Event;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = ();
	type SlashDeferDuration = ();
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = BondingDuration;
	type SessionInterface = ();
	type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
	type NextNewSession = ();
	type MaxNominatorRewardedPerValidator = ConstU32<64>;
	type OffendingValidatorsThreshold = ();
	type ElectionProvider =
		frame_election_provider_support::NoElection<(AccountId, BlockNumber, Staking)>;
	type GenesisElectionProvider = Self::ElectionProvider;
	type VoterList = pallet_staking::UseNominatorsAndValidatorsMap<Self>;
	type MaxUnlockingChunks = ConstU32<32>;
	type OnStakerSlash = Pools;
	type BenchmarkingConfig = pallet_staking::TestBenchmarkingConfig;
	type WeightInfo = ();
}

pub struct BalanceToU256;
impl Convert<Balance, sp_core::U256> for BalanceToU256 {
	fn convert(n: Balance) -> sp_core::U256 {
		n.into()
	}
}

pub struct U256ToBalance;
impl Convert<sp_core::U256, Balance> for U256ToBalance {
	fn convert(n: sp_core::U256) -> Balance {
		n.try_into().unwrap()
	}
}

parameter_types! {
	pub const PostUnbondingPoolsWindow: u32 = 10;
	pub const PoolsPalletId: PalletId = PalletId(*b"py/nopls");
	pub static MaxMetadataLen: u32 = 2;
	pub static CheckLevel: u8 = 255;
}

impl pallet_nomination_pools::Config for Runtime {
	type Event = Event;
	type WeightInfo = ();
	type Currency = Balances;
	type CurrencyBalance = Balance;
	type RewardCounter = FixedU128;
	type BalanceToU256 = BalanceToU256;
	type U256ToBalance = U256ToBalance;
	type StakingInterface = Staking;
	type PostUnbondingPoolsWindow = PostUnbondingPoolsWindow;
	type MaxMetadataLen = MaxMetadataLen;
	type MaxUnbonding = ConstU32<8>;
	type MaxPointsToBalance = ConstU8<10>;
	type PalletId = PoolsPalletId;
}

pub struct FastUnstakeWeightInfo;
impl fast_unstake::WeightInfo for FastUnstakeWeightInfo {
	fn register_fast_unstake() -> Weight {
		10
	}
	fn deregister() -> Weight {
		5
	}
	fn control() -> Weight {
		2
	}
	fn on_idle_unstake() -> Weight {
		10
	}
	fn on_idle_check(e: u32) -> Weight {
		10
	}
}

parameter_types! {
	pub static SlashPerEra: u32 = 100;
}

impl fast_unstake::Config for Runtime {
	type Event = Event;
	type SlashPerEra = SlashPerEra;
	type ControlOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type WeightInfo = FastUnstakeWeightInfo;
}

type Block = frame_system::mocking::MockBlock<Runtime>;
type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<Runtime>},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<Runtime>, Event<Runtime>},
		Staking: pallet_staking::{Pallet, Call, Config<Runtime>, Storage, Event<Runtime>},
		Pools: pallet_nomination_pools::{Pallet, Call, Storage, Event<Runtime>},
		FastUnstake: fast_unstake::{Pallet, Call, Storage, Event<Runtime>},
	}
);

pub fn new_test_ext() -> sp_io::TestExternalities {
	sp_tracing::try_init_simple();
	let mut storage = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	let _ = pallet_nomination_pools::GenesisConfig::<Runtime> {
		min_join_bond: 2,
		min_create_bond: 2,
		max_pools: Some(3),
		max_members_per_pool: Some(5),
		max_members: Some(3 * 5),
	}
	.assimilate_storage(&mut storage)
	.unwrap();

	let _ = pallet_balances::GenesisConfig::<Runtime> {
		balances: vec![(10, 100), (20, 100), (21, 100), (22, 100)],
	}
	.assimilate_storage(&mut storage)
	.unwrap();

	let mut ext = sp_io::TestExternalities::from(storage);

	ext.execute_with(|| {
		// for events to be deposited.
		frame_system::Pallet::<Runtime>::set_block_number(1);

		// set some limit for nominations.
		assert_ok!(Staking::set_staking_configs(
			Origin::root(),
			pallet_staking::ConfigOp::Set(10), // minimum nominator bond
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
		));
	});

	ext
}

parameter_types! {
	static ObservedEventsPools: usize = 0;
	static ObservedEventsStaking: usize = 0;
	static ObservedEventsBalances: usize = 0;
}

pub(crate) fn pool_events_since_last_call() -> Vec<pallet_nomination_pools::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::Pools(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = ObservedEventsPools::get();
	ObservedEventsPools::set(events.len());
	events.into_iter().skip(already_seen).collect()
}

pub(crate) fn staking_events_since_last_call() -> Vec<pallet_staking::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::Staking(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = ObservedEventsStaking::get();
	ObservedEventsStaking::set(events.len());
	events.into_iter().skip(already_seen).collect()
}

pub struct ExtBuilder {
	members: Vec<(AccountId, Balance)>,
	max_members: Option<u32>,
	max_members_per_pool: Option<u32>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self { members: Default::default(), max_members: Some(4), max_members_per_pool: Some(3) }
	}
}

impl ExtBuilder {
	// Add members to pool 0.
	pub(crate) fn add_members(mut self, members: Vec<(AccountId, Balance)>) -> Self {
		self.members = members;
		self
	}

	pub(crate) fn ed(self, ed: Balance) -> Self {
		ExistentialDeposit::set(ed);
		self
	}

	pub(crate) fn min_bond(self, min: Balance) -> Self {
		StakingMinBond::set(min);
		self
	}

	pub(crate) fn min_join_bond(self, min: Balance) -> Self {
		MinJoinBondConfig::set(min);
		self
	}

	pub(crate) fn with_check(self, level: u8) -> Self {
		CheckLevel::set(level);
		self
	}

	pub(crate) fn max_members(mut self, max: Option<u32>) -> Self {
		self.max_members = max;
		self
	}

	pub(crate) fn max_members_per_pool(mut self, max: Option<u32>) -> Self {
		self.max_members_per_pool = max;
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = pallet_nomination_pools::GenesisConfig::<Runtime> {
			min_join_bond: MinJoinBondConfig::get(),
			min_create_bond: 2,
			max_pools: Some(2),
			max_members_per_pool: self.max_members_per_pool,
			max_members: self.max_members,
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		ext.execute_with(|| {
			// for events to be deposited.
			frame_system::Pallet::<Runtime>::set_block_number(1);

			// make a pool
			let amount_to_bond = MinJoinBondConfig::get();
			Balances::make_free_balance_be(&10, amount_to_bond * 5);
			assert_ok!(Pools::create(RawOrigin::Signed(10).into(), amount_to_bond, 900, 901, 902));

			let last_pool = LastPoolId::<Runtime>::get();
			for (account_id, bonded) in self.members {
				Balances::make_free_balance_be(&account_id, bonded * 2);
				assert_ok!(Pools::join(RawOrigin::Signed(account_id).into(), bonded, last_pool));
			}
		});
		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			Pools::sanity_checks(CheckLevel::get()).unwrap();
		})
	}
}

pub(crate) fn unsafe_set_state(pool_id: PoolId, state: PoolState) {
	BondedPools::<Runtime>::try_mutate(pool_id, |maybe_bonded_pool| {
		maybe_bonded_pool.as_mut().ok_or(()).map(|bonded_pool| {
			bonded_pool.state = state;
		})
	})
	.unwrap()
}

pub(crate) fn run_to_block(n: u64) {
	let current_block = System::block_number();
	assert!(n > current_block);
	while System::block_number() < n {
		Balances::on_finalize(System::block_number());
		Staking::on_finalize(System::block_number());
		Pools::on_finalize(System::block_number());
		FastUnstake::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		Balances::on_initialize(System::block_number());
		Staking::on_initialize(System::block_number());
		Pools::on_initialize(System::block_number());
		FastUnstake::on_initialize(System::block_number());
	}
}

parameter_types! {
	storage FastUnstakeEvents: u32 = 0;
}

pub(crate) fn fast_unstake_events_since_last_call() -> Vec<super::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::FastUnstake(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = FastUnstakeEvents::get();
	FastUnstakeEvents::set(&(events.len() as u32));
	events.into_iter().skip(already_seen as usize).collect()
}
