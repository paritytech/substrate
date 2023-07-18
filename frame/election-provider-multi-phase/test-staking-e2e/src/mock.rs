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

#![allow(dead_code)]

use _feps::ExtendedBalance;
use frame_support::{
	dispatch::UnfilteredDispatchable, parameter_types, traits, traits::Hooks, weights::constants,
};
use frame_system::EnsureRoot;
use sp_core::{ConstU32, Get};
use sp_npos_elections::{ElectionScore, VoteWeight};
use sp_runtime::{
	offchain::{
		testing::{OffchainState, PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	testing,
	traits::Zero,
	transaction_validity, BuildStorage, PerU16, Perbill,
};
use sp_staking::{
	offence::{DisableStrategy, OffenceDetails, OnOffenceHandler},
	EraIndex, SessionIndex,
};
use sp_std::prelude::*;
use std::collections::BTreeMap;

use codec::Decode;
use frame_election_provider_support::{onchain, ElectionDataProvider, SequentialPhragmen, Weight};
use pallet_election_provider_multi_phase::{
	unsigned::MinerConfig, Call, ElectionCompute, QueuedSolution, SolutionAccuracyOf,
};
use pallet_staking::StakerStatus;
use parking_lot::RwLock;
use std::sync::Arc;

use frame_support::derive_impl;

use crate::{log, log_current_time};

pub const INIT_TIMESTAMP: BlockNumber = 30_000;
pub const BLOCK_TIME: BlockNumber = 1000;

type Block = frame_system::mocking::MockBlockU32<Runtime>;
type Extrinsic = testing::TestXt<RuntimeCall, ()>;

frame_support::construct_runtime!(
	pub enum Runtime
	{
		System: frame_system,
		ElectionProviderMultiPhase: pallet_election_provider_multi_phase,
		Staking: pallet_staking,
		Balances: pallet_balances,
		BagsList: pallet_bags_list,
		Session: pallet_session,
		Historical: pallet_session::historical,
		Timestamp: pallet_timestamp,
	}
);

pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u32;
pub(crate) type BlockNumber = u32;
pub(crate) type Balance = u64;
pub(crate) type VoterIndex = u16;
pub(crate) type TargetIndex = u16;
pub(crate) type Moment = u32;

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Runtime {
	type Block = Block;
	type BlockHashCount = ConstU32<10>;
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();

	type AccountData = pallet_balances::AccountData<Balance>;
}

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
	pub BlockWeights: frame_system::limits::BlockWeights = frame_system::limits::BlockWeights
		::with_sensible_defaults(
			Weight::from_parts(2u64 * constants::WEIGHT_REF_TIME_PER_SECOND, u64::MAX),
			NORMAL_DISPATCH_RATIO,
		);
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
	type MaxHolds = ConstU32<1>;
	type MaxFreezes = traits::ConstU32<1>;
	type RuntimeHoldReason = RuntimeHoldReason;
	type FreezeIdentifier = ();
	type WeightInfo = ();
}

impl pallet_timestamp::Config for Runtime {
	type Moment = Moment;
	type OnTimestampSet = ();
	type MinimumPeriod = traits::ConstU32<5>;
	type WeightInfo = ();
}

parameter_types! {
	pub static Period: u32 = 30;
	pub static Offset: u32 = 0;
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
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = (OtherSessionHandler,);
	type RuntimeEvent = RuntimeEvent;
	type ValidatorId = AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Runtime>;
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
	pub static UnsignedPhase: BlockNumber = 10;
	// we expect a minimum of 3 blocks in signed phase and unsigned phases before trying
	// enetering in emergency phase after the election failed.
	pub static MinBlocksBeforeEmergency: BlockNumber = 3;
	pub static MaxElectingVoters: VoterIndex = 1000;
	pub static MaxElectableTargets: TargetIndex = 1000;
	pub static MaxActiveValidators: u32 = 1000;
	pub static OffchainRepeat: u32 = 5;
	pub static MinerMaxLength: u32 = 256;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static TransactionPriority: transaction_validity::TransactionPriority = 1;
	#[derive(Debug)]
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
	type BetterSignedThreshold = ();
	type BetterUnsignedThreshold = ();
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
	type Fallback =
		frame_election_provider_support::NoElection<(AccountId, BlockNumber, Staking, MaxWinners)>;
	type GovernanceFallback = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type Solver = SequentialPhragmen<AccountId, SolutionAccuracyOf<Runtime>, ()>;
	type ForceOrigin = EnsureRoot<AccountId>;
	type MaxElectableTargets = MaxElectableTargets;
	type MaxElectingVoters = MaxElectingVoters;
	type MaxWinners = MaxWinners;
	type BenchmarkingConfig = NoopElectionProviderBenchmarkConfig;
	type WeightInfo = ();
}

impl MinerConfig for Runtime {
	type AccountId = AccountId;
	type Solution = MockNposSolution;
	type MaxVotesPerVoter =
	<<Self as pallet_election_provider_multi_phase::Config>::DataProvider as ElectionDataProvider>::MaxVotesPerVoter;
	type MaxLength = MinerMaxLength;
	type MaxWeight = MinerMaxWeight;
	type MaxWinners = MaxWinners;

	fn solution_weight(_v: u32, _t: u32, _a: u32, _d: u32) -> Weight {
		Weight::zero()
	}
}

const THRESHOLDS: [VoteWeight; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
	pub const SessionsPerEra: sp_staking::SessionIndex = 2;
	pub const BondingDuration: sp_staking::EraIndex = 28;
	pub const SlashDeferDuration: sp_staking::EraIndex = 7; // 1/4 the bonding duration.
	pub const MaxNominatorRewardedPerValidator: u32 = 256;
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(40);
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
	type UnixTime = Timestamp;
	type CurrencyToVote = ();
	type RewardRemainder = ();
	type RuntimeEvent = RuntimeEvent;
	type Slash = (); // burn slashes
	type Reward = (); // rewards are minted from the void
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
	type SlashDeferDuration = SlashDeferDuration;
	type AdminOrigin = EnsureRoot<AccountId>; // root can cancel slashes
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
	type EventListeners = ();
	type WeightInfo = pallet_staking::weights::SubstrateWeight<Runtime>;
	type BenchmarkingConfig = pallet_staking::TestBenchmarkingConfig;
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
	pub static VotersBound: u32 = 600;
	pub static TargetsBound: u32 = 400;
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

pub struct NoopElectionProviderBenchmarkConfig;

impl pallet_election_provider_multi_phase::BenchmarkingConfig
	for NoopElectionProviderBenchmarkConfig
{
	const VOTERS: [u32; 2] = [0, 0];
	const TARGETS: [u32; 2] = [0, 0];
	const ACTIVE_VOTERS: [u32; 2] = [0, 0];
	const DESIRED_TARGETS: [u32; 2] = [0, 0];
	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 0;
	const MINER_MAXIMUM_VOTERS: u32 = 0;
	const MAXIMUM_TARGETS: u32 = 0;
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

pub struct StakingExtBuilder {
	validator_count: u32,
	minimum_validator_count: u32,
	min_nominator_bond: Balance,
	min_validator_bond: Balance,
	status: BTreeMap<AccountId, StakerStatus<AccountId>>,
	stakes: BTreeMap<AccountId, Balance>,
	stakers: Vec<(AccountId, AccountId, Balance, StakerStatus<AccountId>)>,
}

impl Default for StakingExtBuilder {
	fn default() -> Self {
		let stakers = vec![
			// (stash, ctrl, stake, status)
			// these two will be elected in the default test where we elect 2.
			(11, 11, 1000, StakerStatus::<AccountId>::Validator),
			(21, 21, 1000, StakerStatus::<AccountId>::Validator),
			// loser validators if validator_count() is default.
			(31, 31, 500, StakerStatus::<AccountId>::Validator),
			(41, 41, 1500, StakerStatus::<AccountId>::Validator),
			(51, 51, 1500, StakerStatus::<AccountId>::Validator),
			(61, 61, 1500, StakerStatus::<AccountId>::Validator),
			(71, 71, 1500, StakerStatus::<AccountId>::Validator),
			(81, 81, 1500, StakerStatus::<AccountId>::Validator),
			(91, 91, 1500, StakerStatus::<AccountId>::Validator),
			(101, 101, 500, StakerStatus::<AccountId>::Validator),
			// an idle validator
			(201, 201, 1000, StakerStatus::<AccountId>::Idle),
		];

		Self {
			validator_count: 2,
			minimum_validator_count: 0,
			min_nominator_bond: ExistentialDeposit::get(),
			min_validator_bond: ExistentialDeposit::get(),
			status: Default::default(),
			stakes: Default::default(),
			stakers,
		}
	}
}

impl StakingExtBuilder {
	pub fn validator_count(mut self, n: u32) -> Self {
		self.validator_count = n;
		self
	}
}

pub struct EpmExtBuilder {}

impl Default for EpmExtBuilder {
	fn default() -> Self {
		EpmExtBuilder {}
	}
}

impl EpmExtBuilder {
	pub fn disable_emergency_throttling(self) -> Self {
		<MinBlocksBeforeEmergency>::set(0);
		self
	}

	pub fn phases(self, signed: BlockNumber, unsigned: BlockNumber) -> Self {
		<SignedPhase>::set(signed);
		<UnsignedPhase>::set(unsigned);
		self
	}
}

pub struct BalancesExtBuilder {
	balances: Vec<(AccountId, Balance)>,
}

impl Default for BalancesExtBuilder {
	fn default() -> Self {
		let balances = vec![
			// (account_id, balance)
			(1, 10),
			(2, 20),
			(3, 300),
			(4, 400),
			// controllers (still used in some tests. Soon to be deprecated).
			(10, 100),
			(20, 100),
			(30, 100),
			(40, 100),
			(50, 100),
			(60, 100),
			(70, 100),
			(80, 100),
			(90, 100),
			(100, 100),
			(200, 100),
			// stashes
			(11, 1000),
			(21, 2000),
			(31, 3000),
			(41, 4000),
			(51, 5000),
			(61, 6000),
			(71, 7000),
			(81, 8000),
			(91, 9000),
			(101, 10000),
			(201, 20000),
			// This allows us to have a total_payout different from 0.
			(999, 1_000_000_000_000),
		];
		Self { balances }
	}
}

pub struct ExtBuilder {
	staking_builder: StakingExtBuilder,
	epm_builder: EpmExtBuilder,
	balances_builder: BalancesExtBuilder,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			staking_builder: StakingExtBuilder::default(),
			epm_builder: EpmExtBuilder::default(),
			balances_builder: BalancesExtBuilder::default(),
		}
	}
}

impl ExtBuilder {
	pub fn build(&self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::<Runtime>::default().build_storage().unwrap();

		let _ = pallet_balances::GenesisConfig::<Runtime> {
			balances: self.balances_builder.balances.clone(),
		}
		.assimilate_storage(&mut storage);

		let mut stakers = self.staking_builder.stakers.clone();
		self.staking_builder.status.clone().into_iter().for_each(|(stash, status)| {
			let (_, _, _, ref mut prev_status) = stakers
				.iter_mut()
				.find(|s| s.0 == stash)
				.expect("set_status staker should exist; qed");
			*prev_status = status;
		});
		// replaced any of the stakes if needed.
		self.staking_builder.stakes.clone().into_iter().for_each(|(stash, stake)| {
			let (_, _, ref mut prev_stake, _) = stakers
				.iter_mut()
				.find(|s| s.0 == stash)
				.expect("set_stake staker should exits; qed.");
			*prev_stake = stake;
		});

		let _ = pallet_staking::GenesisConfig::<Runtime> {
			stakers: stakers.clone(),
			validator_count: self.staking_builder.validator_count,
			minimum_validator_count: self.staking_builder.minimum_validator_count,
			slash_reward_fraction: Perbill::from_percent(10),
			min_nominator_bond: self.staking_builder.min_nominator_bond,
			min_validator_bond: self.staking_builder.min_validator_bond,
			..Default::default()
		}
		.assimilate_storage(&mut storage);

		let _ = pallet_session::GenesisConfig::<Runtime> {
			// set the keys for the first session.
			keys: stakers
				.into_iter()
				.map(|(id, ..)| (id, id, SessionKeys { other: (id as u64).into() }))
				.collect(),
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		// We consider all test to start after timestamp is initialized This must be ensured by
		// having `timestamp::on_initialize` called before `staking::on_initialize`.
		ext.execute_with(|| {
			System::set_block_number(1);
			Session::on_initialize(1);
			<Staking as Hooks<u32>>::on_initialize(1);
			Timestamp::set_timestamp(INIT_TIMESTAMP);
		});

		ext
	}

	pub fn staking(mut self, builder: StakingExtBuilder) -> Self {
		self.staking_builder = builder;
		self
	}

	pub fn epm(mut self, builder: EpmExtBuilder) -> Self {
		self.epm_builder = builder;
		self
	}

	pub fn balances(mut self, builder: BalancesExtBuilder) -> Self {
		self.balances_builder = builder;
		self
	}

	pub fn build_offchainify(
		self,
	) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>, Arc<RwLock<OffchainState>>) {
		// add offchain and pool externality extensions.
		let mut ext = self.build();
		let (offchain, offchain_state) = TestOffchainExt::new();
		let (pool, pool_state) = TestTransactionPoolExt::new();

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		(ext, pool_state, offchain_state)
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		let mut ext = self.build();
		ext.execute_with(test);

		#[cfg(feature = "try-runtime")]
		ext.execute_with(|| {
			let bn = System::block_number();

			assert_ok!(<MultiPhase as Hooks<u64>>::try_state(bn));
			assert_ok!(<Staking as Hooks<u64>>::try_state(bn));
			assert_ok!(<Session as Hooks<u64>>::try_state(bn));
		});
	}
}

// Progress to given block, triggering session and era changes as we progress and ensuring that
// there is a solution queued when expected.
pub fn roll_to(n: BlockNumber, delay_solution: bool) {
	for b in (System::block_number()) + 1..=n {
		System::set_block_number(b);
		Session::on_initialize(b);
		Timestamp::set_timestamp(System::block_number() * BLOCK_TIME + INIT_TIMESTAMP);

		// TODO(gpestana): implement a realistic OCW worker insted of simulating it
		// https://github.com/paritytech/substrate/issues/13589
		// if there's no solution queued and the solution should not be delayed, try mining and
		// queue a solution.
		if ElectionProviderMultiPhase::current_phase().is_signed() && !delay_solution {
			let _ = try_queue_solution(ElectionCompute::Signed).map_err(|e| {
				log!(info, "failed to mine/queue solution: {:?}", e);
			});
		}
		ElectionProviderMultiPhase::on_initialize(b);

		Staking::on_initialize(b);
		if b != n {
			Staking::on_finalize(System::block_number());
		}

		log_current_time();
	}
}

// Progress to given block, triggering session and era changes as we progress and ensuring that
// there is a solution queued when expected.
pub fn roll_to_with_ocw(n: BlockNumber, pool: Arc<RwLock<PoolState>>, delay_solution: bool) {
	for b in (System::block_number()) + 1..=n {
		System::set_block_number(b);
		Session::on_initialize(b);
		Timestamp::set_timestamp(System::block_number() * BLOCK_TIME + INIT_TIMESTAMP);

		ElectionProviderMultiPhase::on_initialize(b);
		ElectionProviderMultiPhase::offchain_worker(b);

		if !delay_solution && pool.read().transactions.len() > 0 {
			// decode submit_unsigned callable that may be queued in the pool by ocw. skip all
			// other extrinsics in the pool.
			for encoded in &pool.read().transactions {
				let extrinsic = Extrinsic::decode(&mut &encoded[..]).unwrap();

				let _ = match extrinsic.call {
					RuntimeCall::ElectionProviderMultiPhase(
						call @ Call::submit_unsigned { .. },
					) => {
						// call submit_unsigned callable in OCW pool.
						crate::assert_ok!(call.dispatch_bypass_filter(RuntimeOrigin::none()));
					},
					_ => (),
				};
			}

			pool.try_write().unwrap().transactions.clear();
		}

		Staking::on_initialize(b);
		if b != n {
			Staking::on_finalize(System::block_number());
		}

		log_current_time();
	}
}
// helper to progress one block ahead.
pub fn roll_one(pool: Arc<RwLock<PoolState>>, delay_solution: bool) {
	let bn = System::block_number().saturating_add(1);
	roll_to_with_ocw(bn, pool, delay_solution);
}

/// Progresses from the current block number (whatever that may be) to the block where the session
/// `session_index` starts.
pub(crate) fn start_session(
	session_index: SessionIndex,
	pool: Arc<RwLock<PoolState>>,
	delay_solution: bool,
) {
	let end = if Offset::get().is_zero() {
		Period::get() * session_index
	} else {
		Offset::get() * session_index + Period::get() * session_index
	};

	assert!(end >= System::block_number());

	roll_to_with_ocw(end, pool, delay_solution);

	// session must have progressed properly.
	assert_eq!(
		Session::current_index(),
		session_index,
		"current session index = {}, expected = {}",
		Session::current_index(),
		session_index,
	);
}

/// Go one session forward.
pub(crate) fn advance_session(pool: Arc<RwLock<PoolState>>) {
	let current_index = Session::current_index();
	start_session(current_index + 1, pool, false);
}

pub(crate) fn advance_session_delayed_solution(pool: Arc<RwLock<PoolState>>) {
	let current_index = Session::current_index();
	start_session(current_index + 1, pool, true);
}

pub(crate) fn start_next_active_era(pool: Arc<RwLock<PoolState>>) -> Result<(), ()> {
	start_active_era(active_era() + 1, pool, false)
}

pub(crate) fn start_next_active_era_delayed_solution(
	pool: Arc<RwLock<PoolState>>,
) -> Result<(), ()> {
	start_active_era(active_era() + 1, pool, true)
}

/// Progress until the given era.
pub(crate) fn start_active_era(
	era_index: EraIndex,
	pool: Arc<RwLock<PoolState>>,
	delay_solution: bool,
) -> Result<(), ()> {
	let era_before = current_era();

	start_session((era_index * <SessionsPerEra as Get<u32>>::get()).into(), pool, delay_solution);

	log!(
		info,
		"start_active_era - era_before: {}, current era: {} -> progress to: {} -> after era: {}",
		era_before,
		active_era(),
		era_index,
		current_era(),
	);

	// if the solution was not delayed, era should have progressed.
	if !delay_solution && (active_era() != era_index || current_era() != active_era()) {
		Err(())
	} else {
		Ok(())
	}
}

pub(crate) fn active_era() -> EraIndex {
	Staking::active_era().unwrap().index
}

pub(crate) fn current_era() -> EraIndex {
	Staking::current_era().unwrap()
}

// Fast forward until EPM signed phase.
pub fn roll_to_epm_signed() {
	while !matches!(
		ElectionProviderMultiPhase::current_phase(),
		pallet_election_provider_multi_phase::Phase::Signed
	) {
		roll_to(System::block_number() + 1, false);
	}
}

// Fast forward until EPM unsigned phase.
pub fn roll_to_epm_unsigned() {
	while !matches!(
		ElectionProviderMultiPhase::current_phase(),
		pallet_election_provider_multi_phase::Phase::Unsigned(_)
	) {
		roll_to(System::block_number() + 1, false);
	}
}

// Fast forward until EPM off.
pub fn roll_to_epm_off() {
	while !matches!(
		ElectionProviderMultiPhase::current_phase(),
		pallet_election_provider_multi_phase::Phase::Off
	) {
		roll_to(System::block_number() + 1, false);
	}
}

// Queue a solution based on the current snapshot.
pub(crate) fn try_queue_solution(when: ElectionCompute) -> Result<(), String> {
	let raw_solution = ElectionProviderMultiPhase::mine_solution()
		.map_err(|e| format!("error mining solution: {:?}", e))?;

	ElectionProviderMultiPhase::feasibility_check(raw_solution.0, when)
		.map(|ready| {
			QueuedSolution::<Runtime>::put(ready);
		})
		.map_err(|e| format!("error in solution feasibility: {:?}", e))
}

pub(crate) fn on_offence_now(
	offenders: &[OffenceDetails<
		AccountId,
		pallet_session::historical::IdentificationTuple<Runtime>,
	>],
	slash_fraction: &[Perbill],
) {
	let now = Staking::active_era().unwrap().index;
	let _ = Staking::on_offence(
		offenders,
		slash_fraction,
		Staking::eras_start_session_index(now).unwrap(),
		DisableStrategy::WhenSlashed,
	);
}

// Add offence to validator, slash it.
pub(crate) fn add_slash(who: &AccountId) {
	on_offence_now(
		&[OffenceDetails {
			offender: (*who, Staking::eras_stakers(active_era(), *who)),
			reporters: vec![],
		}],
		&[Perbill::from_percent(10)],
	);
}

// Slashes enough validators to cross the `Staking::OffendingValidatorsThreshold`.
pub(crate) fn slash_through_offending_threshold() {
	let validators = Session::validators();
	let mut remaining_slashes =
		<Runtime as pallet_staking::Config>::OffendingValidatorsThreshold::get() *
			validators.len() as u32;

	for v in validators.into_iter() {
		if remaining_slashes != 0 {
			add_slash(&v);
			remaining_slashes -= 1;
		}
	}
}

// Slashes a percentage of the active nominators that haven't been slashed yet, with
// a minimum of 1 validator slash.
pub(crate) fn slash_percentage(percentage: Perbill) -> Vec<AccountId> {
	let validators = Session::validators();
	let mut remaining_slashes = (percentage * validators.len() as u32).max(1);
	let mut slashed = vec![];

	for v in validators.into_iter() {
		if remaining_slashes != 0 {
			add_slash(&v);
			slashed.push(v);
			remaining_slashes -= 1;
		}
	}
	slashed
}

pub(crate) fn set_minimum_election_score(
	minimal_stake: ExtendedBalance,
	sum_stake: ExtendedBalance,
	sum_stake_squared: ExtendedBalance,
) -> Result<(), ()> {
	let election_score = ElectionScore { minimal_stake, sum_stake, sum_stake_squared };
	ElectionProviderMultiPhase::set_minimum_untrusted_score(
		RuntimeOrigin::root(),
		Some(election_score),
	)
	.map(|_| ())
	.map_err(|_| ())
}

pub(crate) fn staking_events() -> Vec<pallet_staking::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::Staking(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

pub(crate) fn epm_events() -> Vec<pallet_election_provider_multi_phase::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let RuntimeEvent::ElectionProviderMultiPhase(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect::<Vec<_>>()
}
