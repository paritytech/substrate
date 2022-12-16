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

use frame_support::{bounded_vec, parameter_types, traits, traits::Hooks, BoundedVec};
use frame_system::EnsureRoot;
use sp_core::{ConstU32, H256};
use sp_npos_elections::{BalancingConfig, VoteWeight};
use sp_runtime::{testing, traits::IdentityLookup, transaction_validity, PerU16, Perbill};
use sp_std::prelude::*;

use frame_election_provider_support::{onchain, SequentialPhragmen, Weight};
use pallet_election_provider_multi_phase::{
	unsigned::{MinerConfig, VoterOf},
	SolutionAccuracyOf,
};

type Block = frame_system::mocking::MockBlock<Runtime>;
type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Extrinsic = testing::TestXt<RuntimeCall, ()>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system,
		ElectionProviderMultiPhase: pallet_election_provider_multi_phase,
		Staking: pallet_staking,
		Balances: pallet_balances,
		BagsList: pallet_bags_list,
		Session: pallet_session,
	}
);

pub(crate) type AccountId = u128;
pub(crate) type AccountIndex = u32;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u64;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;
pub(crate) type Moment = u64;

impl frame_system::Config for Runtime {
	type BaseCallFilter = traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = traits::ConstU32<16>;
}

parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
}

impl pallet_balances::Config for Runtime {
	type MaxLocks = traits::ConstU32<1024>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub static CapturedMoment: Option<Moment> = None;
}

// TOOD(gpestana) needed or can we set Timestamp::OnTimestampSet = ()?
pub struct MockOnTimestampSet;
impl traits::OnTimestampSet<Moment> for MockOnTimestampSet {
	fn on_timestamp_set(moment: Moment) {
		CapturedMoment::mutate(|x| *x = Some(moment));
	}
}

impl pallet_timestamp::Config for Runtime {
	type Moment = Moment;
	type OnTimestampSet = MockOnTimestampSet;
	type MinimumPeriod = traits::ConstU64<5>;
	type WeightInfo = ();
}

parameter_types! {
	pub static Period: BlockNumber = 15;
	pub static Offset: BlockNumber = 0;
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {
		pub other: OtherSessionHandler,
	}
}

impl pallet_session::Config for Runtime {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Runtime, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = (OtherSessionHandler,);
	type RuntimeEvent = RuntimeEvent;
	type ValidatorId = AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Runtime>;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type WeightInfo = ();
}
impl pallet_session::historical::Config for Runtime {
	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Runtime>;
}

frame_election_provider_support::generate_solution_type!(
	#[compact]
	pub struct MockNposSolution::<
		VoterIndex = VoterIndex,
		TargetIndex = TargetIndex,
		Accuracy = PerU16,
		MaxVoters = ConstU32::<2_000>
	>(16)
);

parameter_types! {
	pub static SignedPhase: BlockNumber = 10;
	pub static UnsignedPhase: BlockNumber = 5;
	pub static MaxElectingVoters: VoterIndex = 1000;
	pub static MaxElectableTargets: TargetIndex = 1000;
	pub static MaxActiveValidators: u32 = 1000;
	pub static Balancing: Option<BalancingConfig> = Some( BalancingConfig { iterations: 0, tolerance: 0 } );
	pub static BetterSignedThreshold: Perbill = Perbill::zero();
	pub static BetterUnsignedThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: u32 = 5;
	pub static TransactionPriority: transaction_validity::TransactionPriority = 1;
	pub static MaxWinners: u32 = 100;
	pub static MaxVotesPerVoter: u32 = 16;
	pub static MaxNominations: u32 = 16;
}

impl pallet_election_provider_multi_phase::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type EstimateCallFee = frame_support::traits::ConstU32<8>;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type BetterSignedThreshold = BetterSignedThreshold;
	type BetterUnsignedThreshold = BetterUnsignedThreshold;
	type OffchainRepeat = OffchainRepeat;
	type MinerTxPriority = TransactionPriority;
	type MinerConfig = Self;
	type SignedMaxSubmissions = ConstU32<10>;
	type SignedRewardBase = ();
	type SignedDepositBase = ();
	type SignedDepositByte = ();
	type SignedMaxRefunds = ConstU32<3>;
	type SignedDepositWeight = ();
	type SignedMaxWeight = ();
	type SlashHandler = ();
	type RewardHandler = ();
	type DataProvider = Staking;
	type Fallback = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type GovernanceFallback = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type Solver = SequentialPhragmen<AccountId, SolutionAccuracyOf<Runtime>, Balancing>;
	type ForceOrigin = EnsureRoot<AccountId>;
	type MaxElectableTargets = MaxElectableTargets;
	type MaxElectingVoters = MaxElectingVoters;
	type MaxWinners = MaxWinners;
	type BenchmarkingConfig = ElectionProviderBenchmarkConfig;
	type WeightInfo = ();
}

impl MinerConfig for Runtime {
	type AccountId = AccountId;
	type Solution = MockNposSolution;
	type MaxVotesPerVoter = MaxNominations;
	type MaxLength = ();
	type MaxWeight = ();

	fn solution_weight(_voters: u32, _targets: u32, _active_voters: u32, _degree: u32) -> Weight {
		Weight::zero()
	}
}

const THRESHOLDS: [VoteWeight; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
	pub const SessionsPerEra: sp_staking::SessionIndex = 1;
	pub const BondingDuration: sp_staking::EraIndex = 28;
	pub const SlashDeferDuration: sp_staking::EraIndex = 7; // 1/4 the bonding duration.
	pub const MaxNominatorRewardedPerValidator: u32 = 256;
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(17);
	pub HistoryDepth: u32 = 84;
}

impl pallet_bags_list::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type ScoreProvider = Staking;
	type BagThresholds = BagThresholds;
	type Score = VoteWeight;
}

impl pallet_staking::Config for Runtime {
	type MaxNominations = MaxNominations;
	type Currency = Balances;
	type CurrencyBalance = Balance;
	type UnixTime = pallet_timestamp::Pallet<Self>;
	type CurrencyToVote = traits::SaturatingCurrencyToVote;
	type RewardRemainder = ();
	type RuntimeEvent = RuntimeEvent;
	type Slash = (); // burn slashes
	type Reward = (); // rewards are minted from the void
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
	type SlashDeferDuration = SlashDeferDuration;
	type SlashCancelOrigin = EnsureRoot<AccountId>; // root can cancel slashes
	type SessionInterface = Self;
	type EraPayout = ();
	type NextNewSession = Session;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
	type ElectionProvider = ElectionProviderMultiPhase;
	type GenesisElectionProvider = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type VoterList = BagsList;
	type TargetList = pallet_staking::UseValidatorsMap<Self>;
	type MaxUnlockingChunks = ConstU32<32>;
	type HistoryDepth = HistoryDepth;
	type OnStakerSlash = ();
	type WeightInfo = pallet_staking::weights::SubstrateWeight<Runtime>;
	type BenchmarkingConfig = StakingBenchmarkingConfig;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	RuntimeCall: From<LocalCall>,
{
	type OverarchingCall = RuntimeCall;
	type Extrinsic = Extrinsic;
}

pub struct OnChainSeqPhragmen;

parameter_types! {
	pub VotersBound: u32 = 600;
	pub TargetsBound: u32 = 400;
}

impl onchain::Config for OnChainSeqPhragmen {
	type System = Runtime;
	type Solver = SequentialPhragmen<
		AccountId,
		pallet_election_provider_multi_phase::SolutionAccuracyOf<Runtime>,
	>;
	type DataProvider = Staking;
	type WeightInfo = ();
	type MaxWinners = MaxWinners;
	type VotersBound = VotersBound;
	type TargetsBound = TargetsBound;
}

pub struct StakingBenchmarkingConfig;
impl pallet_staking::BenchmarkingConfig for StakingBenchmarkingConfig {
	type MaxNominators = traits::ConstU32<1000>;
	type MaxValidators = traits::ConstU32<1000>;
}

pub struct ElectionProviderBenchmarkConfig;

impl pallet_election_provider_multi_phase::BenchmarkingConfig for ElectionProviderBenchmarkConfig {
	const VOTERS: [u32; 2] = [1000, 2000];
	const TARGETS: [u32; 2] = [500, 1000];
	const ACTIVE_VOTERS: [u32; 2] = [500, 800];
	const DESIRED_TARGETS: [u32; 2] = [200, 400];
	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 1000;
	const MINER_MAXIMUM_VOTERS: u32 = 1000;
	const MAXIMUM_TARGETS: u32 = 300;
}

pub struct OtherSessionHandler;
impl traits::OneSessionHandler<AccountId> for OtherSessionHandler {
	type Key = testing::UintAuthorityId;

	fn on_genesis_session<'a, I: 'a>(_: I)
	where
		I: Iterator<Item = (&'a AccountId, Self::Key)>,
		AccountId: 'a,
	{
	}

	fn on_new_session<'a, I: 'a>(_: bool, _: I, _: I)
	where
		I: Iterator<Item = (&'a AccountId, Self::Key)>,
		AccountId: 'a,
	{
	}

	fn on_disabled(_validator_index: u32) {}
}

impl sp_runtime::BoundToRuntimeAppPublic for OtherSessionHandler {
	type Public = testing::UintAuthorityId;
}

#[derive(Default)]
pub struct ExtBuilder;

pub mod agents {
	use super::AccountId;

	pub const ACCOUNT_0: AccountId = 0;
	pub const ACCOUNT_1: AccountId = 1;
	pub const ACCOUNT_2: AccountId = 2;
	pub const ACCOUNT_3: AccountId = 3;
	pub const ACCOUNT_4: AccountId = 4;
	pub const ACCOUNT_5: AccountId = 5;
	pub const ACCOUNT_6: AccountId = 6;
	pub const ACCOUNT_7: AccountId = 7;
	pub const ACCOUNT_8: AccountId = 8;
	pub const ACCOUNT_9: AccountId = 9;
	pub const ACCOUNT_10: AccountId = 10;
}

use agents::*;

parameter_types! {
	pub static Targets: Vec<AccountId> = vec![ACCOUNT_0, ACCOUNT_1, ACCOUNT_2, ACCOUNT_3];
	pub static Voters: Vec<VoterOf<Runtime>> = vec![
		(ACCOUNT_0, 10, bounded_vec![ACCOUNT_9, ACCOUNT_10]),
		(ACCOUNT_1, 10, bounded_vec![ACCOUNT_0, ACCOUNT_2]),
		(ACCOUNT_2, 10, bounded_vec![ACCOUNT_0]),
		(ACCOUNT_3, 10, bounded_vec![ACCOUNT_7, ACCOUNT_8, ACCOUNT_9, ACCOUNT_10]),
		// self votes.
		(ACCOUNT_10, 10, bounded_vec![ACCOUNT_10]),
		(ACCOUNT_9, 20, bounded_vec![ACCOUNT_9]),
		(ACCOUNT_8, 30, bounded_vec![ACCOUNT_8]),
		(ACCOUNT_7, 40, bounded_vec![ACCOUNT_7]),
	];
}

impl ExtBuilder {
	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![
				(ACCOUNT_0, 100),
				(ACCOUNT_1, 100),
				(ACCOUNT_2, 100),
				(ACCOUNT_3, 100),
				(ACCOUNT_4, 100),
				(ACCOUNT_5, 100),
				(ACCOUNT_6, 100),
				(ACCOUNT_7, 100),
				(ACCOUNT_8, 100),
				(ACCOUNT_9, 100),
				(ACCOUNT_10, 100),
			],
		}
		.assimilate_storage(&mut storage);

		sp_io::TestExternalities::from(storage)
	}

	pub fn phases(self, signed: BlockNumber, unsigned: BlockNumber) -> Self {
		<SignedPhase>::set(signed);
		<UnsignedPhase>::set(unsigned);
		self
	}

	pub fn add_voter(
		self,
		who: AccountId,
		stake: Balance,
		targets: BoundedVec<AccountId, MaxNominations>,
	) -> Self {
		VOTERS.with(|v| v.borrow_mut().push((who, stake, targets)));
		self
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}

// Fast forward `n` blocks.
pub fn roll_to(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		ElectionProviderMultiPhase::on_initialize(i);
		Staking::on_initialize(i);
	}
}

// Fast forward until EPM signed phase.
pub fn roll_to_signed() {
	while !matches!(
		ElectionProviderMultiPhase::current_phase(),
		pallet_election_provider_multi_phase::Phase::Signed
	) {
		roll_to(System::block_number() + 1);
	}
}

// Fast forward until EPM unsigned phase.
pub fn roll_to_unsigned() {
	while !matches!(
		ElectionProviderMultiPhase::current_phase(),
		pallet_election_provider_multi_phase::Phase::Unsigned(_)
	) {
		roll_to(System::block_number() + 1);
	}
}

parameter_types! {
	static EPMEventsIndex: usize = 0;
	static SessionEventsIndex: usize = 0;
	static StakingEventsIndex: usize = 0;
}

// TODO(gpestana): refactor to events_sinve_last_call() -> Vec<_>
pub fn epm_events_since_last_call() -> Vec<pallet_election_provider_multi_phase::Event<Runtime>> {
	let all: Vec<_> = System::events()
		.into_iter()
		.filter_map(|r| {
			if let RuntimeEvent::ElectionProviderMultiPhase(inner) = r.event {
				Some(inner)
			} else {
				None
			}
		})
		.collect();
	let seen = EPMEventsIndex::get();
	EPMEventsIndex::set(all.len());
	all.into_iter().skip(seen).collect()
}

// TODO(gpestana): refactor to events_sinve_last_call() -> Vec<_>
pub fn session_events_since_last_call() -> Vec<pallet_session::Event> {
	let all: Vec<_> = System::events()
		.into_iter()
		.filter_map(|r| if let RuntimeEvent::Session(inner) = r.event { Some(inner) } else { None })
		.collect();
	let seen = SessionEventsIndex::get();
	SessionEventsIndex::set(all.len());
	all.into_iter().skip(seen).collect()
}

// TODO(gpestana): refactor to events_sinve_last_call() -> Vec<_>
pub fn staking_events_since_last_call() -> Vec<pallet_staking::Event<Runtime>> {
	let all: Vec<_> = System::events()
		.into_iter()
		.filter_map(|r| if let RuntimeEvent::Staking(inner) = r.event { Some(inner) } else { None })
		.collect();
	let seen = StakingEventsIndex::get();
	StakingEventsIndex::set(all.len());
	all.into_iter().skip(seen).collect()
}
