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

// this whole crate is only for test
#![cfg(test)]

use election_provider::Phase;
use frame_election_provider_support::{
	data_provider, onchain, ElectionDataProvider, SortedListProvider,
};
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{
	parameter_types,
	sp_runtime::{testing::UintAuthorityId, traits::Bounded, Perbill},
	traits::{ConstU32, GenesisBuild, Hooks, OffchainWorker, OnInitialize},
	weights::Weight,
};
use pallet_election_provider_multi_block as election_provider;
use pallet_staking::{EraIndex, Exposure, IndividualExposure, StakerStatus};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};
use sp_npos_elections::NposSolution;
use sp_runtime::{
	curve::PiecewiseLinear,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16,
};
use std::{convert::TryFrom, sync::Arc};

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, Call, (), ()>;
pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>, Config},
		Balances: pallet_balances::{Pallet, Call, Event<T>, Config<T>},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		Staking: pallet_staking::{Pallet, Call, Event<T>, Config<T>},
		Session: pallet_session::{Pallet, Call, Event, Config<T>},
		BagsList: pallet_bags_list::{Pallet, Call, Event<T>},
		ElectionProvider: election_provider::{Pallet, Call, Event<T>, ValidateUnsigned},
	}
);

pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestNposSolution::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

impl frame_system::Config for Runtime {
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

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
parameter_types! {
	pub const ExistentialDeposit: Balance = 1;
	pub BlockWeights: frame_system::limits::BlockWeights = frame_system::limits::BlockWeights
		::with_sensible_defaults(2 * frame_support::weights::constants::WEIGHT_PER_SECOND, NORMAL_DISPATCH_RATIO);
}

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ConstU32<99>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

parameter_types! {
	pub const MinimumPeriod: u64 = 5;
}
impl pallet_timestamp::Config for Runtime {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}

parameter_types! {
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(25);
	pub static SessionLength: u32 = 10;
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys { pub dummy: UintAuthorityId, }
}

impl pallet_session::Config for Runtime {
	type Event = Event;
	type Keys = SessionKeys;
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Runtime, Staking>;
	type SessionHandler = pallet_session::TestSessionHandler;
	type ValidatorId = AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Runtime>;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type ShouldEndSession = pallet_session::PeriodicSessions<SessionLength, ()>;
	type NextSessionRotation = Self::ShouldEndSession;
	type WeightInfo = ();
}

impl pallet_session::historical::Config for Runtime {
	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Runtime>;
}

const THRESHOLDS: [sp_npos_elections::VoteWeight; 9] =
	[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
}

impl pallet_bags_list::Config for Runtime {
	type Event = Event;
	type VoteWeightProvider = Staking;
	type BagThresholds = BagThresholds;
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
	pub static SessionsPerEra: EraIndex = 3;
	pub static BondingDuration: EraIndex = 10;
	pub static SlashDeferDuration: EraIndex = 10;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &I_NPOS;
}

impl onchain::Config for Runtime {
	type AccountId = <Self as frame_system::Config>::AccountId;
	type BlockNumber = <Self as frame_system::Config>::BlockNumber;
	type BlockWeights = ();
	type Accuracy = Perbill;
	type DataProvider = Staking;
}

impl pallet_staking::Config for Runtime {
	const MAX_NOMINATIONS: u32 = <TestNposSolution as NposSolution>::LIMIT as u32;
	type Currency = Balances;
	type UnixTime = Timestamp;
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
	type RewardRemainder = ();
	type Event = Event;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type SlashDeferDuration = SlashDeferDuration;
	type BondingDuration = BondingDuration;
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type SessionInterface = Self;
	type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
	type NextNewSession = Session;
	type MaxNominatorRewardedPerValidator = ConstU32<8>;
	type ElectionProvider = MultiPhase;
	type GenesisElectionProvider = onchain::OnChainSequentialPhragmen<Self>;
	type SortedListProvider = BagsList;
	type WeightInfo = ();
}

parameter_types! {
	// multi-phase configs
	pub static SignedPhase: BlockNumber = 5;
	pub static UnsignedPhase: BlockNumber = 5;
	pub static SignedMaxSubmissions: u32 = 5;
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositByte: Balance = 0;
	pub static SignedDepositWeight: Balance = 0;
	pub static SignedRewardBase: Balance = 7;
	pub static SignedMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxIterations: u32 = 5;
	pub static MinerTxPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = Bounded::max_value();
	pub const Fallback: election_provider::FallbackStrategy = multi_block::FallbackStrategy::Nothing;

	pub static VoterSnapshotPerBlock: VoterIndex = u32::max_value();
	pub static ElectionBlocks: BlockNumber = 3;
}

impl multi_block::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type EstimateCallFee = frame_support::traits::ConstU32<8>;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type OffchainRepeat = OffchainRepeat;
	type MinerMaxIterations = MinerMaxIterations;
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
	type BenchmarkingConfig = ();
	type OnChainAccuracy = Perbill;
	type Fallback = Fallback;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type VoterSnapshotPerBlock = VoterSnapshotPerBlock;
	type Solution = TestNposSolution;
	type WeightInfo = ();
}

parameter_types! {
	pub static Validators: Vec<AccountId> = vec![101, 102, 103, 104];
	pub static Nominators: Vec<(AccountId, Vec<AccountId>)> = vec![
		(1, vec![101, 102]),
		(2, vec![101, 102]),
		(3, vec![103]),
		(4, vec![101, 102, 101, 102]),
		(5, vec![103, 101, 104, 102]),
		(6, vec![104, 102, 103, 103]),
		(7, vec![101, 101, 102, 103]),
		(8, vec![102, 103, 101, 104]),
		(9, vec![101, 104, 101, 104]),
	];
	pub static ValidatorCount: u32 = 3;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

#[derive(Default)]
struct ExtBuilder {}

impl ExtBuilder {
	fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let balance_factor = 10;
		let stash = balance_factor * ExistentialDeposit::get();
		let balance = stash * 2;

		let balances = Validators::get()
			.into_iter()
			.map(|v| (v, balance))
			.chain(Nominators::get().into_iter().map(|(n, _)| (n, balance)))
			.chain(std::iter::once((999, balance)))
			.collect::<Vec<_>>();
		let stakers = Validators::get()
			.into_iter()
			.map(|v| (v, v, stash, StakerStatus::Validator))
			.chain(
				Nominators::get()
					.into_iter()
					.map(|(n, v)| (n, n, stash, StakerStatus::Nominator(v))),
			)
			.collect::<Vec<_>>();
		let keys = Validators::get()
			.into_iter()
			.take(2)
			.map(|v| (v, v, SessionKeys { dummy: UintAuthorityId(v as u64) }))
			.collect::<Vec<_>>();

		pallet_balances::GenesisConfig::<Runtime> { balances }
			.assimilate_storage(&mut storage)
			.unwrap();
		pallet_staking::GenesisConfig::<Runtime> {
			stakers,
			validator_count: ValidatorCount::get(),
			..Default::default()
		}
		.assimilate_storage(&mut storage)
		.unwrap();
		pallet_session::GenesisConfig::<Runtime> { keys }
			.assimilate_storage(&mut storage)
			.unwrap();

		let mut ext = sp_io::TestExternalities::from(storage);
		ext.execute_with(|| roll_to(1));
		ext
	}

	fn build_offchainify(self, iters: u32) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
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

	fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}

fn balances(who: &u64) -> (u64, u64) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}

/// To from `now` to block `n`.
fn roll_to(n: u64) {
	let now = System::block_number();
	for i in now + 1..=n {
		log::trace!(target: "election-playground", "rolling to block {:?}", i);
		System::set_block_number(i);
		<System as OnInitialize<BlockNumber>>::on_initialize(i);
		<AllPallets as OnInitialize<BlockNumber>>::on_initialize(i);
	}
}

fn roll_to_with_ocw(n: u64) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		<System as OnInitialize<BlockNumber>>::on_initialize(i);
		<AllPallets as OnInitialize<BlockNumber>>::on_initialize(i);
		<AllPallets as OffchainWorker<BlockNumber>>::offchain_worker(i);
	}
}

#[test]
fn basic_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(System::block_number(), 1);

		// session.
		assert_eq!(Session::validators(), vec![101, 102, 103]);

		// staking
		assert_eq!(Staking::current_era().unwrap(), 0);
		assert_eq!(Staking::active_era().unwrap().index, 0);
		assert_eq!(
			pallet_staking::CounterForNominators::<Runtime>::get(),
			Nominators::get().len() as u32
		);
		assert_eq!(
			pallet_staking::CounterForValidators::<Runtime>::get(),
			Validators::get().len() as u32
		);
		assert_eq!(
			pallet_staking::ErasStakers::<Runtime>::iter_prefix(0).collect::<Vec<_>>(),
			vec![
				(
					101,
					Exposure {
						total: 47,
						own: 10,
						others: vec![
							IndividualExposure { who: 1, value: 5 },
							IndividualExposure { who: 2, value: 5 },
							IndividualExposure { who: 4, value: 5 },
							IndividualExposure { who: 5, value: 4 },
							IndividualExposure { who: 7, value: 4 },
							IndividualExposure { who: 8, value: 4 },
							IndividualExposure { who: 9, value: 10 }
						]
					}
				),
				(
					103,
					Exposure {
						total: 32,
						own: 10,
						others: vec![
							IndividualExposure { who: 3, value: 10 },
							IndividualExposure { who: 5, value: 3 },
							IndividualExposure { who: 6, value: 3 },
							IndividualExposure { who: 7, value: 3 },
							IndividualExposure { who: 8, value: 3 }
						]
					}
				),
				(
					102,
					Exposure {
						total: 41,
						own: 10,
						others: vec![
							IndividualExposure { who: 1, value: 5 },
							IndividualExposure { who: 2, value: 5 },
							IndividualExposure { who: 4, value: 5 },
							IndividualExposure { who: 5, value: 3 },
							IndividualExposure { who: 6, value: 7 },
							IndividualExposure { who: 7, value: 3 },
							IndividualExposure { who: 8, value: 3 }
						]
					}
				)
			]
		);

		// multi-phase
		assert_eq!(ElectionProvider::current_phase(), Phase::Off);

		// bags-list
		assert_eq!(BagsList::count(), Nominators::get().len() as u32);
		assert_ok!(BagsList::sanity_check());
	})
}

#[test]
fn simple_multiblock_scenario() {}
