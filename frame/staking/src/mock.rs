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

//! Test utilities

use crate::{self as pallet_staking, *};
use frame_election_provider_support::{onchain, SequentialPhragmen, VoteWeight};
use frame_support::{
	assert_ok, ord_parameter_types, parameter_types,
	traits::{
		ConstU32, ConstU64, Currency, EitherOfDiverse, FindAuthor, Get, Hooks, Imbalance,
		OnUnbalanced, OneSessionHandler,
	},
	weights::constants::RocksDbWeight,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_io;
use sp_runtime::{
	curve::PiecewiseLinear,
	testing::{Header, UintAuthorityId},
	traits::{IdentityLookup, Zero},
	BuildStorage,
};
use sp_staking::offence::{DisableStrategy, OffenceDetails, OnOffenceHandler};

pub const INIT_TIMESTAMP: u64 = 30_000;
pub const BLOCK_TIME: u64 = 1000;

/// The AccountId alias in this test module.
pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u128;

/// Another session handler struct to test on_disabled.
pub struct OtherSessionHandler;
impl OneSessionHandler<AccountId> for OtherSessionHandler {
	type Key = UintAuthorityId;

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
	type Public = UintAuthorityId;
}

pub fn is_disabled(controller: AccountId) -> bool {
	let stash = Staking::ledger(&controller).unwrap().stash;
	let validator_index = match Session::validators().iter().position(|v| *v == stash) {
		Some(index) => index as u32,
		None => return false,
	};

	Session::disabled_validators().contains(&validator_index)
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Authorship: pallet_authorship,
		Timestamp: pallet_timestamp,
		Balances: pallet_balances,
		Staking: pallet_staking,
		Session: pallet_session,
		Historical: pallet_session::historical,
		VoterBagsList: pallet_bags_list::<Instance1>,
	}
);

/// Author of block is always 11
pub struct Author11;
impl FindAuthor<AccountId> for Author11 {
	fn find_author<'a, I>(_digests: I) -> Option<AccountId>
	where
		I: 'a + IntoIterator<Item = (frame_support::ConsensusEngineId, &'a [u8])>,
	{
		Some(11)
	}
}

parameter_types! {
	pub static SessionsPerEra: SessionIndex = 3;
	pub static ExistentialDeposit: Balance = 1;
	pub static SlashDeferDuration: EraIndex = 0;
	pub static Period: BlockNumber = 5;
	pub static Offset: BlockNumber = 0;
}

impl frame_system::Config for Test {
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
impl pallet_balances::Config for Test {
	type MaxLocks = frame_support::traits::ConstU32<1024>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {
		pub other: OtherSessionHandler,
	}
}
impl pallet_session::Config for Test {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = (OtherSessionHandler,);
	type RuntimeEvent = RuntimeEvent;
	type ValidatorId = AccountId;
	type ValidatorIdOf = crate::StashOf<Test>;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type WeightInfo = ();
}

impl pallet_session::historical::Config for Test {
	type FullIdentification = crate::Exposure<AccountId, Balance>;
	type FullIdentificationOf = crate::ExposureOf<Test>;
}
impl pallet_authorship::Config for Test {
	type FindAuthor = Author11;
	type EventHandler = Pallet<Test>;
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<5>;
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
	pub const BondingDuration: EraIndex = 3;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &I_NPOS;
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(75);
}

parameter_types! {
	pub static RewardRemainderUnbalanced: u128 = 0;
}

pub struct RewardRemainderMock;

impl OnUnbalanced<NegativeImbalanceOf<Test>> for RewardRemainderMock {
	fn on_nonzero_unbalanced(amount: NegativeImbalanceOf<Test>) {
		RewardRemainderUnbalanced::mutate(|v| {
			*v += amount.peek();
		});
		drop(amount);
	}
}

const THRESHOLDS: [sp_npos_elections::VoteWeight; 9] =
	[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [sp_npos_elections::VoteWeight] = &THRESHOLDS;
	pub static MaxNominations: u32 = 16;
	pub static HistoryDepth: u32 = 80;
	pub static MaxUnlockingChunks: u32 = 32;
	pub static RewardOnUnbalanceWasCalled: bool = false;
	pub static MaxWinners: u32 = 100;
}

type VoterBagsListInstance = pallet_bags_list::Instance1;
impl pallet_bags_list::Config<VoterBagsListInstance> for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	// Staking is the source of truth for voter bags list, since they are not kept up to date.
	type ScoreProvider = Staking;
	type BagThresholds = BagThresholds;
	type Score = VoteWeight;
}

pub struct OnChainSeqPhragmen;
impl onchain::Config for OnChainSeqPhragmen {
	type System = Test;
	type Solver = SequentialPhragmen<AccountId, Perbill>;
	type DataProvider = Staking;
	type WeightInfo = ();
	type MaxWinners = MaxWinners;
	type VotersBound = ConstU32<{ u32::MAX }>;
	type TargetsBound = ConstU32<{ u32::MAX }>;
}

pub struct MockReward {}
impl OnUnbalanced<PositiveImbalanceOf<Test>> for MockReward {
	fn on_unbalanced(_: PositiveImbalanceOf<Test>) {
		RewardOnUnbalanceWasCalled::set(true);
	}
}

parameter_types! {
	pub static LedgerSlashPerEra:
		(BalanceOf<Test>, BTreeMap<EraIndex, BalanceOf<Test>>) =
		(Zero::zero(), BTreeMap::new());
}

pub struct EventListenerMock;
impl OnStakingUpdate<AccountId, Balance> for EventListenerMock {
	fn on_slash(
		_pool_account: &AccountId,
		slashed_bonded: Balance,
		slashed_chunks: &BTreeMap<EraIndex, Balance>,
	) {
		LedgerSlashPerEra::set((slashed_bonded, slashed_chunks.clone()));
	}
}

impl crate::pallet::pallet::Config for Test {
	type MaxNominations = MaxNominations;
	type Currency = Balances;
	type CurrencyBalance = <Self as pallet_balances::Config>::Balance;
	type UnixTime = Timestamp;
	type CurrencyToVote = ();
	type RewardRemainder = RewardRemainderMock;
	type RuntimeEvent = RuntimeEvent;
	type Slash = ();
	type Reward = MockReward;
	type SessionsPerEra = SessionsPerEra;
	type SlashDeferDuration = SlashDeferDuration;
	type AdminOrigin = EnsureOneOrRoot;
	type BondingDuration = BondingDuration;
	type SessionInterface = Self;
	type EraPayout = ConvertCurve<RewardCurve>;
	type NextNewSession = Session;
	type MaxNominatorRewardedPerValidator = ConstU32<64>;
	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
	type ElectionProvider = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type GenesisElectionProvider = Self::ElectionProvider;
	// NOTE: consider a macro and use `UseNominatorsAndValidatorsMap<Self>` as well.
	type VoterList = VoterBagsList;
	type TargetList = UseValidatorsMap<Self>;
	type MaxUnlockingChunks = MaxUnlockingChunks;
	type HistoryDepth = HistoryDepth;
	type EventListeners = EventListenerMock;
	type BenchmarkingConfig = TestBenchmarkingConfig;
	type WeightInfo = ();
}

pub(crate) type StakingCall = crate::Call<Test>;
pub(crate) type TestCall = <Test as frame_system::Config>::RuntimeCall;

pub struct ExtBuilder {
	nominate: bool,
	validator_count: u32,
	minimum_validator_count: u32,
	invulnerables: Vec<AccountId>,
	has_stakers: bool,
	initialize_first_session: bool,
	pub min_nominator_bond: Balance,
	min_validator_bond: Balance,
	balance_factor: Balance,
	status: BTreeMap<AccountId, StakerStatus<AccountId>>,
	stakes: BTreeMap<AccountId, Balance>,
	stakers: Vec<(AccountId, AccountId, Balance, StakerStatus<AccountId>)>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			nominate: true,
			validator_count: 2,
			minimum_validator_count: 0,
			balance_factor: 1,
			invulnerables: vec![],
			has_stakers: true,
			initialize_first_session: true,
			min_nominator_bond: ExistentialDeposit::get(),
			min_validator_bond: ExistentialDeposit::get(),
			status: Default::default(),
			stakes: Default::default(),
			stakers: Default::default(),
		}
	}
}

impl ExtBuilder {
	pub fn existential_deposit(self, existential_deposit: Balance) -> Self {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = existential_deposit);
		self
	}
	pub fn nominate(mut self, nominate: bool) -> Self {
		self.nominate = nominate;
		self
	}
	pub fn validator_count(mut self, count: u32) -> Self {
		self.validator_count = count;
		self
	}
	pub fn minimum_validator_count(mut self, count: u32) -> Self {
		self.minimum_validator_count = count;
		self
	}
	pub fn slash_defer_duration(self, eras: EraIndex) -> Self {
		SLASH_DEFER_DURATION.with(|v| *v.borrow_mut() = eras);
		self
	}
	pub fn invulnerables(mut self, invulnerables: Vec<AccountId>) -> Self {
		self.invulnerables = invulnerables;
		self
	}
	pub fn session_per_era(self, length: SessionIndex) -> Self {
		SESSIONS_PER_ERA.with(|v| *v.borrow_mut() = length);
		self
	}
	pub fn period(self, length: BlockNumber) -> Self {
		PERIOD.with(|v| *v.borrow_mut() = length);
		self
	}
	pub fn has_stakers(mut self, has: bool) -> Self {
		self.has_stakers = has;
		self
	}
	pub fn initialize_first_session(mut self, init: bool) -> Self {
		self.initialize_first_session = init;
		self
	}
	pub fn offset(self, offset: BlockNumber) -> Self {
		OFFSET.with(|v| *v.borrow_mut() = offset);
		self
	}
	pub fn min_nominator_bond(mut self, amount: Balance) -> Self {
		self.min_nominator_bond = amount;
		self
	}
	pub fn min_validator_bond(mut self, amount: Balance) -> Self {
		self.min_validator_bond = amount;
		self
	}
	pub fn set_status(mut self, who: AccountId, status: StakerStatus<AccountId>) -> Self {
		self.status.insert(who, status);
		self
	}
	pub fn set_stake(mut self, who: AccountId, stake: Balance) -> Self {
		self.stakes.insert(who, stake);
		self
	}
	pub fn add_staker(
		mut self,
		stash: AccountId,
		ctrl: AccountId,
		stake: Balance,
		status: StakerStatus<AccountId>,
	) -> Self {
		self.stakers.push((stash, ctrl, stake, status));
		self
	}
	pub fn balance_factor(mut self, factor: Balance) -> Self {
		self.balance_factor = factor;
		self
	}
	fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();

		let _ = pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10 * self.balance_factor),
				(2, 20 * self.balance_factor),
				(3, 300 * self.balance_factor),
				(4, 400 * self.balance_factor),
				// controllers (still used in some tests. Soon to be deprecated).
				(10, self.balance_factor),
				(20, self.balance_factor),
				(30, self.balance_factor),
				(40, self.balance_factor),
				(50, self.balance_factor),
				// stashes
				(11, self.balance_factor * 1000),
				(21, self.balance_factor * 2000),
				(31, self.balance_factor * 2000),
				(41, self.balance_factor * 2000),
				(51, self.balance_factor * 2000),
				// optional nominator
				(100, self.balance_factor * 2000),
				(101, self.balance_factor * 2000),
				// aux accounts
				(60, self.balance_factor),
				(61, self.balance_factor * 2000),
				(70, self.balance_factor),
				(71, self.balance_factor * 2000),
				(80, self.balance_factor),
				(81, self.balance_factor * 2000),
				// This allows us to have a total_payout different from 0.
				(999, 1_000_000_000_000),
			],
		}
		.assimilate_storage(&mut storage);

		let mut stakers = vec![];
		if self.has_stakers {
			stakers = vec![
				// (stash, ctrl, stake, status)
				// these two will be elected in the default test where we elect 2.
				(11, 11, self.balance_factor * 1000, StakerStatus::<AccountId>::Validator),
				(21, 21, self.balance_factor * 1000, StakerStatus::<AccountId>::Validator),
				// a loser validator
				(31, 31, self.balance_factor * 500, StakerStatus::<AccountId>::Validator),
				// an idle validator
				(41, 41, self.balance_factor * 1000, StakerStatus::<AccountId>::Idle),
			];
			// optionally add a nominator
			if self.nominate {
				stakers.push((
					101,
					101,
					self.balance_factor * 500,
					StakerStatus::<AccountId>::Nominator(vec![11, 21]),
				))
			}
			// replace any of the status if needed.
			self.status.into_iter().for_each(|(stash, status)| {
				let (_, _, _, ref mut prev_status) = stakers
					.iter_mut()
					.find(|s| s.0 == stash)
					.expect("set_status staker should exist; qed");
				*prev_status = status;
			});
			// replaced any of the stakes if needed.
			self.stakes.into_iter().for_each(|(stash, stake)| {
				let (_, _, ref mut prev_stake, _) = stakers
					.iter_mut()
					.find(|s| s.0 == stash)
					.expect("set_stake staker should exits; qed.");
				*prev_stake = stake;
			});
			// extend stakers if needed.
			stakers.extend(self.stakers)
		}

		let _ = pallet_staking::GenesisConfig::<Test> {
			stakers: stakers.clone(),
			validator_count: self.validator_count,
			minimum_validator_count: self.minimum_validator_count,
			invulnerables: self.invulnerables,
			slash_reward_fraction: Perbill::from_percent(10),
			min_nominator_bond: self.min_nominator_bond,
			min_validator_bond: self.min_validator_bond,
			..Default::default()
		}
		.assimilate_storage(&mut storage);

		let _ = pallet_session::GenesisConfig::<Test> {
			keys: if self.has_stakers {
				// set the keys for the first session.
				stakers
					.into_iter()
					.map(|(id, ..)| (id, id, SessionKeys { other: id.into() }))
					.collect()
			} else {
				// set some dummy validators in genesis.
				(0..self.validator_count as u64)
					.map(|id| (id, id, SessionKeys { other: id.into() }))
					.collect()
			},
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		if self.initialize_first_session {
			// We consider all test to start after timestamp is initialized This must be ensured by
			// having `timestamp::on_initialize` called before `staking::on_initialize`. Also, if
			// session length is 1, then it is already triggered.
			ext.execute_with(|| {
				System::set_block_number(1);
				Session::on_initialize(1);
				<Staking as Hooks<u64>>::on_initialize(1);
				Timestamp::set_timestamp(INIT_TIMESTAMP);
			});
		}

		ext
	}
	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		sp_tracing::try_init_simple();
		let mut ext = self.build();
		ext.execute_with(test);
		ext.execute_with(|| {
			Staking::do_try_state(System::block_number()).unwrap();
		});
	}
}

pub(crate) fn active_era() -> EraIndex {
	Staking::active_era().unwrap().index
}

pub(crate) fn current_era() -> EraIndex {
	Staking::current_era().unwrap()
}

pub(crate) fn bond(who: AccountId, val: Balance) {
	let _ = Balances::make_free_balance_be(&who, val);
	assert_ok!(Staking::bond(RuntimeOrigin::signed(who), val, RewardDestination::Controller));
}

pub(crate) fn bond_validator(who: AccountId, val: Balance) {
	bond(who, val);
	assert_ok!(Staking::validate(RuntimeOrigin::signed(who), ValidatorPrefs::default()));
	assert_ok!(Session::set_keys(
		RuntimeOrigin::signed(who),
		SessionKeys { other: who.into() },
		vec![]
	));
}

pub(crate) fn bond_nominator(who: AccountId, val: Balance, target: Vec<AccountId>) {
	bond(who, val);
	assert_ok!(Staking::nominate(RuntimeOrigin::signed(who), target));
}

/// Progress to the given block, triggering session and era changes as we progress.
///
/// This will finalize the previous block, initialize up to the given block, essentially simulating
/// a block import/propose process where we first initialize the block, then execute some stuff (not
/// in the function), and then finalize the block.
pub(crate) fn run_to_block(n: BlockNumber) {
	Staking::on_finalize(System::block_number());
	for b in (System::block_number() + 1)..=n {
		System::set_block_number(b);
		Session::on_initialize(b);
		<Staking as Hooks<u64>>::on_initialize(b);
		Timestamp::set_timestamp(System::block_number() * BLOCK_TIME + INIT_TIMESTAMP);
		if b != n {
			Staking::on_finalize(System::block_number());
		}
	}
}

/// Progresses from the current block number (whatever that may be) to the `P * session_index + 1`.
pub(crate) fn start_session(session_index: SessionIndex) {
	let end: u64 = if Offset::get().is_zero() {
		(session_index as u64) * Period::get()
	} else {
		Offset::get() + (session_index.saturating_sub(1) as u64) * Period::get()
	};
	run_to_block(end);
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
pub(crate) fn advance_session() {
	let current_index = Session::current_index();
	start_session(current_index + 1);
}

/// Progress until the given era.
pub(crate) fn start_active_era(era_index: EraIndex) {
	start_session((era_index * <SessionsPerEra as Get<u32>>::get()).into());
	assert_eq!(active_era(), era_index);
	// One way or another, current_era must have changed before the active era, so they must match
	// at this point.
	assert_eq!(current_era(), active_era());
}

pub(crate) fn current_total_payout_for_duration(duration: u64) -> Balance {
	let (payout, _rest) = <Test as Config>::EraPayout::era_payout(
		Staking::eras_total_stake(active_era()),
		Balances::total_issuance(),
		duration,
	);
	assert!(payout > 0);
	payout
}

pub(crate) fn maximum_payout_for_duration(duration: u64) -> Balance {
	let (payout, rest) = <Test as Config>::EraPayout::era_payout(
		Staking::eras_total_stake(active_era()),
		Balances::total_issuance(),
		duration,
	);
	payout + rest
}

/// Time it takes to finish a session.
///
/// Note, if you see `time_per_session() - BLOCK_TIME`, it is fine. This is because we set the
/// timestamp after on_initialize, so the timestamp is always one block old.
pub(crate) fn time_per_session() -> u64 {
	Period::get() * BLOCK_TIME
}

/// Time it takes to finish an era.
///
/// Note, if you see `time_per_era() - BLOCK_TIME`, it is fine. This is because we set the
/// timestamp after on_initialize, so the timestamp is always one block old.
pub(crate) fn time_per_era() -> u64 {
	time_per_session() * SessionsPerEra::get() as u64
}

/// Time that will be calculated for the reward per era.
pub(crate) fn reward_time_per_era() -> u64 {
	time_per_era() - BLOCK_TIME
}

pub(crate) fn reward_all_elected() {
	let rewards = <Test as Config>::SessionInterface::validators().into_iter().map(|v| (v, 1));

	<Pallet<Test>>::reward_by_ids(rewards)
}

pub(crate) fn validator_controllers() -> Vec<AccountId> {
	Session::validators()
		.into_iter()
		.map(|s| Staking::bonded(&s).expect("no controller for validator"))
		.collect()
}

pub(crate) fn on_offence_in_era(
	offenders: &[OffenceDetails<
		AccountId,
		pallet_session::historical::IdentificationTuple<Test>,
	>],
	slash_fraction: &[Perbill],
	era: EraIndex,
	disable_strategy: DisableStrategy,
) {
	let bonded_eras = crate::BondedEras::<Test>::get();
	for &(bonded_era, start_session) in bonded_eras.iter() {
		if bonded_era == era {
			let _ = Staking::on_offence(offenders, slash_fraction, start_session, disable_strategy);
			return
		} else if bonded_era > era {
			break
		}
	}

	if Staking::active_era().unwrap().index == era {
		let _ = Staking::on_offence(
			offenders,
			slash_fraction,
			Staking::eras_start_session_index(era).unwrap(),
			disable_strategy,
		);
	} else {
		panic!("cannot slash in era {}", era);
	}
}

pub(crate) fn on_offence_now(
	offenders: &[OffenceDetails<
		AccountId,
		pallet_session::historical::IdentificationTuple<Test>,
	>],
	slash_fraction: &[Perbill],
) {
	let now = Staking::active_era().unwrap().index;
	on_offence_in_era(offenders, slash_fraction, now, DisableStrategy::WhenSlashed)
}

pub(crate) fn add_slash(who: &AccountId) {
	on_offence_now(
		&[OffenceDetails {
			offender: (*who, Staking::eras_stakers(active_era(), *who)),
			reporters: vec![],
		}],
		&[Perbill::from_percent(10)],
	);
}

/// Make all validator and nominator request their payment
pub(crate) fn make_all_reward_payment(era: EraIndex) {
	let validators_with_reward = ErasRewardPoints::<Test>::get(era)
		.individual
		.keys()
		.cloned()
		.collect::<Vec<_>>();

	// reward validators
	for validator_controller in validators_with_reward.iter().filter_map(Staking::bonded) {
		let ledger = <Ledger<Test>>::get(&validator_controller).unwrap();
		assert_ok!(Staking::payout_stakers(RuntimeOrigin::signed(1337), ledger.stash, era));
	}
}

#[macro_export]
macro_rules! assert_session_era {
	($session:expr, $era:expr) => {
		assert_eq!(
			Session::current_index(),
			$session,
			"wrong session {} != {}",
			Session::current_index(),
			$session,
		);
		assert_eq!(
			Staking::current_era().unwrap(),
			$era,
			"wrong current era {} != {}",
			Staking::current_era().unwrap(),
			$era,
		);
	};
}

pub(crate) fn staking_events() -> Vec<crate::Event<Test>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::Staking(inner) = e { Some(inner) } else { None })
		.collect()
}

parameter_types! {
	static StakingEventsIndex: usize = 0;
}
ord_parameter_types! {
	pub const One: u64 = 1;
}

type EnsureOneOrRoot = EitherOfDiverse<EnsureRoot<AccountId>, EnsureSignedBy<One, AccountId>>;

pub(crate) fn staking_events_since_last_call() -> Vec<crate::Event<Test>> {
	let all: Vec<_> = System::events()
		.into_iter()
		.filter_map(|r| if let RuntimeEvent::Staking(inner) = r.event { Some(inner) } else { None })
		.collect();
	let seen = StakingEventsIndex::get();
	StakingEventsIndex::set(all.len());
	all.into_iter().skip(seen).collect()
}

pub(crate) fn balances(who: &AccountId) -> (Balance, Balance) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}
