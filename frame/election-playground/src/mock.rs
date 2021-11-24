// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
use frame_election_provider_support::{
	data_provider, onchain, ElectionDataProvider, ExtendedBalance, SequentialPhragmen,
	SnapshotBounds,
};
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{parameter_types, traits::Hooks, weights::Weight};
use pallet_session::{PeriodicSessions, TestSessionHandler};
use pallet_staking::{ConvertCurve, EraIndex, SessionInterface};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};

use multi_phase::SolutionAccuracyOf;
use pallet_election_provider_multi_phase as multi_phase;
use sp_runtime::{
	curve::PiecewiseLinear,
	testing::Header,
	traits::{BlakeTwo256, Bounded, IdentityLookup},
	PerU16, Perbill,
};
use std::sync::Arc;

frame_support::construct_runtime!(
	pub enum TestRuntime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Config<T>, Storage, Event<T>},
		BagsList: pallet_bags_list::{Pallet, Call, Storage, Event<T>},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage,},
		Staking: pallet_staking::{Pallet, Call, Config<T>, Storage, Event<T>},
		MultiPhase: multi_phase::{Pallet, Call, Storage, Event<T>},
	}
);

pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for TestRuntime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, Call, (), ()>;

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub BlockWeights: frame_system::limits::BlockWeights = frame_system::limits::BlockWeights
		::with_sensible_defaults(2 * frame_support::weights::constants::WEIGHT_PER_SECOND, NORMAL_DISPATCH_RATIO);
}

impl frame_system::Config for TestRuntime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = BlockWeights;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

impl pallet_balances::Config for TestRuntime {
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

parameter_types! {
	pub static SignedPhase: BlockNumber = 10;
	pub static UnsignedPhase: BlockNumber = 5;
	pub static SignedMaxSubmissions: u32 = 5;
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositByte: Balance = 0;
	pub static SignedDepositWeight: Balance = 0;
	pub static SignedRewardBase: Balance = 7;
	pub static SignedMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerTxPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = 256;
	pub static MockWeightInfo: bool = false;
	pub static VoterSnapshotBounds: SnapshotBounds = SnapshotBounds::new_unbounded();
	pub static TargetSnapshotBounds: SnapshotBounds = SnapshotBounds::new_unbounded();

	pub static EpochLength: u64 = 30;
	pub static OnChianFallback: bool = true;
	pub static Balancing: Option<(usize, ExtendedBalance)> = None;
}

impl onchain::Config for TestRuntime {
	type Accuracy = sp_runtime::Perbill;
	type DataProvider = Staking;
}

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestNposSolution::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

impl pallet_election_provider_multi_phase::Config for TestRuntime {
	type Event = Event;
	type Currency = Balances;
	type EstimateCallFee = frame_support::traits::ConstU32<8>;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type OffchainRepeat = OffchainRepeat;
	type MinerMaxWeight = MinerMaxWeight;
	type MinerMaxLength = MinerMaxLength;
	type MinerTxPriority = MinerTxPriority;
	type SignedRewardBase = SignedRewardBase;
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SignedMaxWeight = SignedMaxWeight;
	type SignedMaxSubmissions = SignedMaxSubmissions;
	type SlashHandler = ();
	type RewardHandler = ();
	type DataProvider = Staking;
	type WeightInfo = ();
	type BenchmarkingConfig = ();
	type Fallback = frame_election_provider_support::onchain::OnChainSequentialPhragmen<Self>;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Solution = TestNposSolution;
	type VoterSnapshotBounds = VoterSnapshotBounds;
	type TargetSnapshotBounds = TargetSnapshotBounds;
	type Solver = SequentialPhragmen<AccountId, SolutionAccuracyOf<TestRuntime>, Balancing>;
}

parameter_types! {
	pub const MinimumPeriod: u64 = 5;
}
impl pallet_timestamp::Config for TestRuntime {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}

pallet_staking_reward_curve::build! {
	const I_NPOS: PiecewiseLinear<'static> = curve!(
		min_inflation: 0_025_000,
		max_inflation: 0_100_000,
		ideal_stake: 0_500_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}

parameter_types! {
	pub static BondingDuration: EraIndex = 5;
	pub static SessionsPerEra: u32 = 5;
	pub static SlashDeferDuration: EraIndex = 0;
	pub static MaxNominatorRewardedPerValidator: u32 = 10;
	pub static OffendingValidatorsThreshold: Perbill = Perbill::from_percent(50);
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &I_NPOS;

	pub static SessionOffset: BlockNumber = 0;
	pub static SessionPeriod: BlockNumber = 10;
}

struct TestSessionInterface;
impl SessionInterface for TestSessionInterface {
	fn disable_validator(validator_index: u32) -> bool {
		Default::default()
	}

	fn validators() -> Vec<AccountId> {
		Default::default()
	}

	fn prune_historical_up_to(up_to: SessionIndex) {}
}

impl pallet_staking::Config for TestRuntime {
	type Currency = Balances;
	type UnixTime = Timestamp;
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
	type RewardRemainder = ();
	type Event = Event;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type SlashDeferDuration = SlashDeferDuration;
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = BondingDuration;
	type SessionInterface = TestSessionInterface;
	type EraPayout = ConvertCurve<RewardCurve>;
	type NextNewSession = PeriodicSessions<SessionOffset, SessionPeriod>;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
	type ElectionProvider = MultiPhase;
	type GenesisElectionProvider = onchain::OnChainSequentialPhragmen<Self>;
	type SortedListProvider = BagsList;
	type NominationQuota = pallet_staking::FixedNominationQuota<16>;
	type WeightInfo = ();
}

const THRESHOLDS: [sp_npos_elections::VoteWeight; 9] =
	[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
}

impl pallet_bags_list::Config for TestRuntime {
	type Event = Event;
	type WeightInfo = ();
	type VoteWeightProvider = Staking;
	type BagThresholds = BagThresholds;
}

#[derive(Default)]
pub struct ExtBuilder {}

impl ExtBuilder {
	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<TestRuntime>().unwrap();

		let _ = pallet_balances::GenesisConfig::<TestRuntime> {
			balances: vec![
				// bunch of account for submitting stuff only.
				(99, 100),
				(999, 100),
				(9999, 100),
			],
		}
		.assimilate_storage(&mut storage);

		sp_io::TestExternalities::from(storage)
	}

	pub fn build_offchainify(
		self,
		iters: u32,
	) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
		let mut ext = self.build();
		let (offchain, offchain_state) = TestOffchainExt::new();
		let (pool, pool_state) = TestTransactionPoolExt::new();

		let mut seed = [0_u8; 32];
		seed[0..4].copy_from_slice(&iters.to_le_bytes());
		offchain_state.write().seed = seed;

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		(ext, pool_state)
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}
