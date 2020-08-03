// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use std::{collections::HashSet, cell::RefCell};
use sp_runtime::Perbill;
use sp_runtime::curve::PiecewiseLinear;
use sp_runtime::traits::{IdentityLookup, Convert, SaturatedConversion, Zero};
use sp_runtime::testing::{Header, UintAuthorityId, TestXt};
use sp_staking::{SessionIndex, offence::{OffenceDetails, OnOffenceHandler}};
use sp_core::H256;
use frame_support::{
	assert_ok, impl_outer_origin, parameter_types, impl_outer_dispatch, impl_outer_event,
	StorageValue, StorageMap, StorageDoubleMap, IterableStorageMap,
	traits::{Currency, Get, FindAuthor, OnFinalize, OnInitialize},
	weights::{Weight, constants::RocksDbWeight},
};
use sp_io;
use sp_npos_elections::{
	build_support_map, evaluate_support, reduce, ExtendedBalance, StakedAssignment, ElectionScore,
	VoteWeight,
};
use crate::*;

pub const INIT_TIMESTAMP: u64 = 30_000;

/// The AccountId alias in this test module.
pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u128;

/// Simple structure that exposes how u64 currency can be represented as... u64.
pub struct CurrencyToVoteHandler;
impl Convert<Balance, u64> for CurrencyToVoteHandler {
	fn convert(x: Balance) -> u64 {
		x.saturated_into()
	}
}
impl Convert<u128, Balance> for CurrencyToVoteHandler {
	fn convert(x: u128) -> Balance {
		x
	}
}

thread_local! {
	static SESSION: RefCell<(Vec<AccountId>, HashSet<AccountId>)> = RefCell::new(Default::default());
	static SESSION_PER_ERA: RefCell<SessionIndex> = RefCell::new(3);
	static EXISTENTIAL_DEPOSIT: RefCell<Balance> = RefCell::new(0);
	static SLASH_DEFER_DURATION: RefCell<EraIndex> = RefCell::new(0);
	static ELECTION_LOOKAHEAD: RefCell<BlockNumber> = RefCell::new(0);
	static PERIOD: RefCell<BlockNumber> = RefCell::new(1);
	static MAX_ITERATIONS: RefCell<u32> = RefCell::new(0);
}

/// Another session handler struct to test on_disabled.
pub struct OtherSessionHandler;
impl pallet_session::OneSessionHandler<AccountId> for OtherSessionHandler {
	type Key = UintAuthorityId;

	fn on_genesis_session<'a, I: 'a>(_: I)
		where I: Iterator<Item=(&'a AccountId, Self::Key)>, AccountId: 'a {}

	fn on_new_session<'a, I: 'a>(_: bool, validators: I, _: I,)
		where I: Iterator<Item=(&'a AccountId, Self::Key)>, AccountId: 'a
	{
		SESSION.with(|x| {
			*x.borrow_mut() = (
				validators.map(|x| x.0.clone()).collect(),
				HashSet::new(),
			)
		});
	}

	fn on_disabled(validator_index: usize) {
		SESSION.with(|d| {
			let mut d = d.borrow_mut();
			let value = d.0[validator_index];
			d.1.insert(value);
		})
	}
}

impl sp_runtime::BoundToRuntimeAppPublic for OtherSessionHandler {
	type Public = UintAuthorityId;
}

pub fn is_disabled(controller: AccountId) -> bool {
	let stash = Staking::ledger(&controller).unwrap().stash;
	SESSION.with(|d| d.borrow().1.contains(&stash))
}

pub struct ExistentialDeposit;
impl Get<Balance> for ExistentialDeposit {
	fn get() -> Balance {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow())
	}
}

pub struct SessionsPerEra;
impl Get<SessionIndex> for SessionsPerEra {
	fn get() -> SessionIndex {
		SESSION_PER_ERA.with(|v| *v.borrow())
	}
}
impl Get<BlockNumber> for SessionsPerEra {
	fn get() -> BlockNumber {
		SESSION_PER_ERA.with(|v| *v.borrow() as BlockNumber)
	}
}

pub struct ElectionLookahead;
impl Get<BlockNumber> for ElectionLookahead {
	fn get() -> BlockNumber {
		ELECTION_LOOKAHEAD.with(|v| *v.borrow())
	}
}

pub struct Period;
impl Get<BlockNumber> for Period {
	fn get() -> BlockNumber {
		PERIOD.with(|v| *v.borrow())
	}
}

pub struct SlashDeferDuration;
impl Get<EraIndex> for SlashDeferDuration {
	fn get() -> EraIndex {
		SLASH_DEFER_DURATION.with(|v| *v.borrow())
	}
}

pub struct MaxIterations;
impl Get<u32> for MaxIterations {
	fn get() -> u32 {
		MAX_ITERATIONS.with(|v| *v.borrow())
	}
}

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		staking::Staking,
	}
}

mod staking {
	// Re-export needed for `impl_outer_event!`.
	pub use super::super::*;
}
use frame_system as system;
use pallet_balances as balances;
use pallet_session as session;

impl_outer_event! {
	pub enum MetaEvent for Test {
		system<T>,
		balances<T>,
		session,
		staking<T>,
	}
}

/// Author of block is always 11
pub struct Author11;
impl FindAuthor<AccountId> for Author11 {
	fn find_author<'a, I>(_digests: I) -> Option<AccountId>
		where I: 'a + IntoIterator<Item = (frame_support::ConsensusEngineId, &'a [u8])>,
	{
		Some(11)
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = MetaEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = RocksDbWeight;
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}
impl pallet_balances::Trait for Test {
	type Balance = Balance;
	type Event = MetaEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub const Offset: BlockNumber = 0;
	pub const UncleGenerations: u64 = 0;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(25);
}
sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {
		pub other: OtherSessionHandler,
	}
}
impl pallet_session::Trait for Test {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = (OtherSessionHandler,);
	type Event = MetaEvent;
	type ValidatorId = AccountId;
	type ValidatorIdOf = crate::StashOf<Test>;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type WeightInfo = ();
}

impl pallet_session::historical::Trait for Test {
	type FullIdentification = crate::Exposure<AccountId, Balance>;
	type FullIdentificationOf = crate::ExposureOf<Test>;
}
impl pallet_authorship::Trait for Test {
	type FindAuthor = Author11;
	type UncleGenerations = UncleGenerations;
	type FilterUncle = ();
	type EventHandler = Module<Test>;
}
parameter_types! {
	pub const MinimumPeriod: u64 = 5;
}
impl pallet_timestamp::Trait for Test {
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
	pub const BondingDuration: EraIndex = 3;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &I_NPOS;
	pub const MaxNominatorRewardedPerValidator: u32 = 64;
	pub const UnsignedPriority: u64 = 1 << 20;
	pub const MinSolutionScoreBump: Perbill = Perbill::zero();
}

thread_local! {
	pub static REWARD_REMAINDER_UNBALANCED: RefCell<u128> = RefCell::new(0);
}

pub struct RewardRemainderMock;

impl OnUnbalanced<NegativeImbalanceOf<Test>> for RewardRemainderMock {
	fn on_nonzero_unbalanced(amount: NegativeImbalanceOf<Test>) {
		REWARD_REMAINDER_UNBALANCED.with(|v| {
			*v.borrow_mut() += amount.peek();
		});
		drop(amount);
	}
}

impl Trait for Test {
	type Currency = Balances;
	type UnixTime = Timestamp;
	type CurrencyToVote = CurrencyToVoteHandler;
	type RewardRemainder = RewardRemainderMock;
	type Event = MetaEvent;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type SlashDeferDuration = SlashDeferDuration;
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = BondingDuration;
	type SessionInterface = Self;
	type RewardCurve = RewardCurve;
	type NextNewSession = Session;
	type ElectionLookahead = ElectionLookahead;
	type Call = Call;
	type MaxIterations = MaxIterations;
	type MinSolutionScoreBump = MinSolutionScoreBump;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type UnsignedPriority = UnsignedPriority;
	type WeightInfo = ();
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = TestXt<Call, ()>;

pub struct ExtBuilder {
	session_length: BlockNumber,
	election_lookahead: BlockNumber,
	session_per_era: SessionIndex,
	existential_deposit: Balance,
	validator_pool: bool,
	nominate: bool,
	validator_count: u32,
	minimum_validator_count: u32,
	slash_defer_duration: EraIndex,
	fair: bool,
	num_validators: Option<u32>,
	invulnerables: Vec<AccountId>,
	has_stakers: bool,
	max_offchain_iterations: u32,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			session_length: 1,
			election_lookahead: 0,
			session_per_era: 3,
			existential_deposit: 1,
			validator_pool: false,
			nominate: true,
			validator_count: 2,
			minimum_validator_count: 0,
			slash_defer_duration: 0,
			fair: true,
			num_validators: None,
			invulnerables: vec![],
			has_stakers: true,
			max_offchain_iterations: 0,
		}
	}
}

impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: Balance) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn validator_pool(mut self, validator_pool: bool) -> Self {
		self.validator_pool = validator_pool;
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
	pub fn slash_defer_duration(mut self, eras: EraIndex) -> Self {
		self.slash_defer_duration = eras;
		self
	}
	pub fn fair(mut self, is_fair: bool) -> Self {
		self.fair = is_fair;
		self
	}
	pub fn num_validators(mut self, num_validators: u32) -> Self {
		self.num_validators = Some(num_validators);
		self
	}
	pub fn invulnerables(mut self, invulnerables: Vec<AccountId>) -> Self {
		self.invulnerables = invulnerables;
		self
	}
	pub fn session_per_era(mut self, length: SessionIndex) -> Self {
		self.session_per_era = length;
		self
	}
	pub fn election_lookahead(mut self, look: BlockNumber) -> Self {
		self.election_lookahead = look;
		self
	}
	pub fn session_length(mut self, length: BlockNumber) -> Self {
		self.session_length = length;
		self
	}
	pub fn has_stakers(mut self, has: bool) -> Self {
		self.has_stakers = has;
		self
	}
	pub fn max_offchain_iterations(mut self, iterations: u32) -> Self {
		self.max_offchain_iterations = iterations;
		self
	}
	pub fn offchain_phragmen_ext(self) -> Self {
		self.session_per_era(4)
			.session_length(5)
			.election_lookahead(3)
	}
	pub fn set_associated_constants(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
		SLASH_DEFER_DURATION.with(|v| *v.borrow_mut() = self.slash_defer_duration);
		SESSION_PER_ERA.with(|v| *v.borrow_mut() = self.session_per_era);
		ELECTION_LOOKAHEAD.with(|v| *v.borrow_mut() = self.election_lookahead);
		PERIOD.with(|v| *v.borrow_mut() = self.session_length);
		MAX_ITERATIONS.with(|v| *v.borrow_mut() = self.max_offchain_iterations);
	}
	pub fn build(self) -> sp_io::TestExternalities {
		let _ = env_logger::try_init();
		self.set_associated_constants();
		let mut storage = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();
		let balance_factor = if self.existential_deposit > 1 {
			256
		} else {
			1
		};

		let num_validators = self.num_validators.unwrap_or(self.validator_count);
		let validators = (0..num_validators)
			.map(|x| ((x + 1) * 10 + 1) as AccountId)
			.collect::<Vec<_>>();

		let _ = pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10 * balance_factor),
				(2, 20 * balance_factor),
				(3, 300 * balance_factor),
				(4, 400 * balance_factor),
				(10, balance_factor),
				(11, balance_factor * 1000),
				(20, balance_factor),
				(21, balance_factor * 2000),
				(30, balance_factor),
				(31, balance_factor * 2000),
				(40, balance_factor),
				(41, balance_factor * 2000),
				(100, 2000 * balance_factor),
				(101, 2000 * balance_factor),
				// This allows us to have a total_payout different from 0.
				(999, 1_000_000_000_000),
			],
		}.assimilate_storage(&mut storage);

		let mut stakers = vec![];
		if self.has_stakers {
			let stake_21 = if self.fair { 1000 } else { 2000 };
			let stake_31 = if self.validator_pool { balance_factor * 1000 } else { 1 };
			let status_41 = if self.validator_pool {
				StakerStatus::<AccountId>::Validator
			} else {
				StakerStatus::<AccountId>::Idle
			};
			let nominated = if self.nominate { vec![11, 21] } else { vec![] };
			stakers = vec![
				// (stash, controller, staked_amount, status)
				(11, 10, balance_factor * 1000, StakerStatus::<AccountId>::Validator),
				(21, 20, stake_21, StakerStatus::<AccountId>::Validator),
				(31, 30, stake_31, StakerStatus::<AccountId>::Validator),
				(41, 40, balance_factor * 1000, status_41),
				// nominator
				(101, 100, balance_factor * 500, StakerStatus::<AccountId>::Nominator(nominated))
			];
		}
		let _ = GenesisConfig::<Test>{
			stakers: stakers,
			validator_count: self.validator_count,
			minimum_validator_count: self.minimum_validator_count,
			invulnerables: self.invulnerables,
			slash_reward_fraction: Perbill::from_percent(10),
			..Default::default()
		}
		.assimilate_storage(&mut storage);

		let _ = pallet_session::GenesisConfig::<Test> {
			keys: validators.iter().map(|x| (
				*x,
				*x,
				SessionKeys { other: UintAuthorityId(*x as u64) }
			)).collect(),
		}.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);
		ext.execute_with(|| {
			let validators = Session::validators();
			SESSION.with(|x| *x.borrow_mut() = (validators.clone(), HashSet::new()));
		});

		// We consider all test to start after timestamp is initialized
		// This must be ensured by having `timestamp::on_initialize` called before
		// `staking::on_initialize`
		ext.execute_with(|| {
			System::set_block_number(1);
			Timestamp::set_timestamp(INIT_TIMESTAMP);
		});

		ext
	}
	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		let mut ext = self.build();
		ext.execute_with(test);
		ext.execute_with(post_conditions);
	}
}

pub type System = frame_system::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;
pub type Session = pallet_session::Module<Test>;
pub type Timestamp = pallet_timestamp::Module<Test>;
pub type Staking = Module<Test>;

pub(crate) fn current_era() -> EraIndex {
	Staking::current_era().unwrap()
}

fn post_conditions() {
	check_nominators();
	check_exposures();
	check_ledgers();
}

pub(crate) fn active_era() -> EraIndex {
	Staking::active_era().unwrap().index
}

fn check_ledgers() {
	// check the ledger of all stakers.
	Bonded::<Test>::iter().for_each(|(_, ctrl)| assert_ledger_consistent(ctrl))
}

fn check_exposures() {
	// a check per validator to ensure the exposure struct is always sane.
	let era = active_era();
	ErasStakers::<Test>::iter_prefix_values(era).for_each(|expo| {
		assert_eq!(
			expo.total as u128,
			expo.own as u128 + expo.others.iter().map(|e| e.value as u128).sum::<u128>(),
			"wrong total exposure.",
		);
	})
}

fn check_nominators() {
	// a check per nominator to ensure their entire stake is correctly distributed. Will only kick-
	// in if the nomination was submitted before the current era.
	let era = active_era();
	<Nominators<Test>>::iter()
		.filter_map(|(nominator, nomination)|
			if nomination.submitted_in > era {
				Some(nominator)
			} else {
				None
		})
		.for_each(|nominator| {
		// must be bonded.
		assert_is_stash(nominator);
		let mut sum = 0;
		Session::validators()
			.iter()
			.map(|v| Staking::eras_stakers(era, v))
			.for_each(|e| {
				let individual = e.others.iter().filter(|e| e.who == nominator).collect::<Vec<_>>();
				let len = individual.len();
				match len {
					0 => { /* not supporting this validator at all. */ },
					1 => sum += individual[0].value,
					_ => panic!("nominator cannot back a validator more than once."),
				};
			});

		let nominator_stake = Staking::slashable_balance_of(&nominator);
		// a nominator cannot over-spend.
		assert!(
			nominator_stake >= sum,
			"failed: Nominator({}) stake({}) >= sum divided({})",
			nominator,
			nominator_stake,
			sum,
		);

		let diff = nominator_stake - sum;
		assert!(diff < 100);
	});
}

fn assert_is_stash(acc: AccountId) {
	assert!(Staking::bonded(&acc).is_some(), "Not a stash.");
}

fn assert_ledger_consistent(ctrl: AccountId) {
	// ensures ledger.total == ledger.active + sum(ledger.unlocking).
	let ledger = Staking::ledger(ctrl).expect("Not a controller.");
	let real_total: Balance = ledger.unlocking.iter().fold(ledger.active, |a, c| a + c.value);
	assert_eq!(real_total, ledger.total);
}

pub(crate) fn bond_validator(stash: AccountId, ctrl: AccountId, val: Balance) {
	let _ = Balances::make_free_balance_be(&stash, val);
	let _ = Balances::make_free_balance_be(&ctrl, val);
	assert_ok!(Staking::bond(
		Origin::signed(stash),
		ctrl,
		val,
		RewardDestination::Controller,
	));
	assert_ok!(Staking::validate(
		Origin::signed(ctrl),
		ValidatorPrefs::default()
	));
}

pub(crate) fn bond_nominator(
	stash: AccountId,
	ctrl: AccountId,
	val: Balance,
	target: Vec<AccountId>,
) {
	let _ = Balances::make_free_balance_be(&stash, val);
	let _ = Balances::make_free_balance_be(&ctrl, val);
	assert_ok!(Staking::bond(
		Origin::signed(stash),
		ctrl,
		val,
		RewardDestination::Controller,
	));
	assert_ok!(Staking::nominate(Origin::signed(ctrl), target));
}

pub(crate) fn run_to_block(n: BlockNumber) {
	Staking::on_finalize(System::block_number());
	for b in System::block_number() + 1..=n {
		System::set_block_number(b);
		Session::on_initialize(b);
		Staking::on_initialize(b);
		if b != n {
			Staking::on_finalize(System::block_number());
		}
	}
}

pub(crate) fn advance_session() {
	let current_index = Session::current_index();
	start_session(current_index + 1);
}

pub(crate) fn start_session(session_index: SessionIndex) {
	assert_eq!(<Period as Get<BlockNumber>>::get(), 1, "start_session can only be used with session length 1.");
	for i in Session::current_index()..session_index {
		Staking::on_finalize(System::block_number());
		System::set_block_number((i + 1).into());
		Timestamp::set_timestamp(System::block_number() * 1000 + INIT_TIMESTAMP);
		Session::on_initialize(System::block_number());
		Staking::on_initialize(System::block_number());
	}

	assert_eq!(Session::current_index(), session_index);
}

// This start and activate the era given.
// Because the mock use pallet-session which delays session by one, this will be one session after
// the election happened, not the first session after the election has happened.
pub(crate) fn start_era(era_index: EraIndex) {
	start_session((era_index * <SessionsPerEra as Get<u32>>::get()).into());
	assert_eq!(Staking::current_era().unwrap(), era_index);
	assert_eq!(Staking::active_era().unwrap().index, era_index);
}

pub(crate) fn current_total_payout_for_duration(duration: u64) -> Balance {
	inflation::compute_total_payout(
		<Test as Trait>::RewardCurve::get(),
		Staking::eras_total_stake(Staking::active_era().unwrap().index),
		Balances::total_issuance(),
		duration,
	).0
}

pub(crate) fn reward_all_elected() {
	let rewards = <Test as Trait>::SessionInterface::validators()
		.into_iter()
		.map(|v| (v, 1));

	<Module<Test>>::reward_by_ids(rewards)
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
) {
	let bonded_eras = crate::BondedEras::get();
	for &(bonded_era, start_session) in bonded_eras.iter() {
		if bonded_era == era {
			let _ = Staking::on_offence(offenders, slash_fraction, start_session).unwrap();
			return;
		} else if bonded_era > era {
			break;
		}
	}

	if Staking::active_era().unwrap().index == era {
		let _ =
			Staking::on_offence(
				offenders,
				slash_fraction,
				Staking::eras_start_session_index(era).unwrap()
			).unwrap();
	} else {
		panic!("cannot slash in era {}", era);
	}
}

pub(crate) fn on_offence_now(
	offenders: &[OffenceDetails<AccountId, pallet_session::historical::IdentificationTuple<Test>>],
	slash_fraction: &[Perbill],
) {
	let now = Staking::active_era().unwrap().index;
	on_offence_in_era(offenders, slash_fraction, now)
}

pub(crate) fn add_slash(who: &AccountId) {
	on_offence_now(
		&[
			OffenceDetails {
				offender: (who.clone(), Staking::eras_stakers(Staking::active_era().unwrap().index, who.clone())),
				reporters: vec![],
			},
		],
		&[Perbill::from_percent(10)],
	);
}

// winners will be chosen by simply their unweighted total backing stake. Nominator stake is
// distributed evenly.
pub(crate) fn horrible_phragmen_with_post_processing(
	do_reduce: bool,
) -> (CompactAssignments, Vec<ValidatorIndex>, ElectionScore) {
	let mut backing_stake_of: BTreeMap<AccountId, Balance> = BTreeMap::new();

	// self stake
	<Validators<Test>>::iter().for_each(|(who, _p)| {
		*backing_stake_of.entry(who).or_insert(Zero::zero()) += Staking::slashable_balance_of(&who)
	});

	// add nominator stuff
	<Nominators<Test>>::iter().for_each(|(who, nomination)| {
		nomination.targets.iter().for_each(|v| {
			*backing_stake_of.entry(*v).or_insert(Zero::zero()) +=
				Staking::slashable_balance_of(&who)
		})
	});

	// elect winners
	let mut sorted: Vec<AccountId> = backing_stake_of.keys().cloned().collect();
	sorted.sort_by_key(|x| backing_stake_of.get(x).unwrap());
	let winners: Vec<AccountId> = sorted
		.iter()
		.cloned()
		.take(Staking::validator_count() as usize)
		.collect();

	// create assignments
	let mut staked_assignment: Vec<StakedAssignment<AccountId>> = Vec::new();
	<Nominators<Test>>::iter().for_each(|(who, nomination)| {
		let mut dist: Vec<(AccountId, ExtendedBalance)> = Vec::new();
		nomination.targets.iter().for_each(|v| {
			if winners.iter().find(|w| *w == v).is_some() {
				dist.push((*v, ExtendedBalance::zero()));
			}
		});

		if dist.len() == 0 {
			return;
		}

		// assign real stakes. just split the stake.
		let stake = Staking::slashable_balance_of(&who) as ExtendedBalance;
		let mut sum: ExtendedBalance = Zero::zero();
		let dist_len = dist.len();
		{
			dist.iter_mut().for_each(|(_, w)| {
				let partial = stake / (dist_len as ExtendedBalance);
				*w = partial;
				sum += partial;
			});
		}

		// assign the leftover to last.
		{
			let leftover = stake - sum;
			let last = dist.last_mut().unwrap();
			last.1 += leftover;
		}

		staked_assignment.push(StakedAssignment {
			who,
			distribution: dist,
		});
	});

	// Ensure that this result is worse than seq-phragmen. Otherwise, it should not have been used
	// for testing.
	let score = {
		let (_, _, better_score) = prepare_submission_with(true, 0, |_| {});

		let support = build_support_map::<AccountId>(&winners, &staked_assignment).0;
		let score = evaluate_support(&support);

		assert!(sp_npos_elections::is_score_better::<Perbill>(
			better_score,
			score,
			MinSolutionScoreBump::get(),
		));

		score
	};

	if do_reduce {
		reduce(&mut staked_assignment);
	}

	let snapshot_validators = Staking::snapshot_validators().unwrap();
	let snapshot_nominators = Staking::snapshot_nominators().unwrap();
	let nominator_index = |a: &AccountId| -> Option<NominatorIndex> {
		snapshot_nominators.iter().position(|x| x == a).map(|i| i as NominatorIndex)
	};
	let validator_index = |a: &AccountId| -> Option<ValidatorIndex> {
		snapshot_validators.iter().position(|x| x == a).map(|i| i as ValidatorIndex)
	};

	// convert back to ratio assignment. This takes less space.
	let assignments_reduced =
		sp_npos_elections::assignment_staked_to_ratio::<AccountId, OffchainAccuracy>(staked_assignment);

	let compact =
		CompactAssignments::from_assignment(assignments_reduced, nominator_index, validator_index)
			.unwrap();

	// winner ids to index
	let winners = winners.into_iter().map(|w| validator_index(&w).unwrap()).collect::<Vec<_>>();

	(compact, winners, score)
}

// Note: this should always logically reproduce [`offchain_election::prepare_submission`], yet we
// cannot do it since we want to have `tweak` injected into the process.
pub(crate) fn prepare_submission_with(
	do_reduce: bool,
	iterations: usize,
	tweak: impl FnOnce(&mut Vec<StakedAssignment<AccountId>>),
) -> (CompactAssignments, Vec<ValidatorIndex>, ElectionScore) {
	// run election on the default stuff.
	let sp_npos_elections::ElectionResult {
		winners,
		assignments,
	} = Staking::do_phragmen::<OffchainAccuracy>().unwrap();
	let winners = sp_npos_elections::to_without_backing(winners);

	let stake_of = |who: &AccountId| -> VoteWeight {
		<CurrencyToVoteHandler as Convert<Balance, VoteWeight>>::convert(
			Staking::slashable_balance_of(&who)
		)
	};

	let mut staked = sp_npos_elections::assignment_ratio_to_staked(assignments, stake_of);
	let (mut support_map, _) = build_support_map::<AccountId>(&winners, &staked);

	if iterations > 0 {
		sp_npos_elections::balance_solution(
			&mut staked,
			&mut support_map,
			Zero::zero(),
			iterations,
		);
	}

	// apply custom tweaks. awesome for testing.
	tweak(&mut staked);

	if do_reduce {
		reduce(&mut staked);
	}

	// convert back to ratio assignment. This takes less space.
	let snapshot_validators = Staking::snapshot_validators().expect("snapshot not created.");
	let snapshot_nominators = Staking::snapshot_nominators().expect("snapshot not created.");
	let nominator_index = |a: &AccountId| -> Option<NominatorIndex> {
		snapshot_nominators
			.iter()
			.position(|x| x == a)
			.map_or_else(
				|| { println!("unable to find nominator index for {:?}", a); None },
				|i| Some(i as NominatorIndex),
			)
	};
	let validator_index = |a: &AccountId| -> Option<ValidatorIndex> {
		snapshot_validators
			.iter()
			.position(|x| x == a)
			.map_or_else(
				|| { println!("unable to find validator index for {:?}", a); None },
				|i| Some(i as ValidatorIndex),
			)
	};

	let assignments_reduced = sp_npos_elections::assignment_staked_to_ratio(staked);

	// re-compute score by converting, yet again, into staked type
	let score = {
		let staked = sp_npos_elections::assignment_ratio_to_staked(
			assignments_reduced.clone(),
			Staking::slashable_balance_of_vote_weight,
		);

		let (support_map, _) = build_support_map::<AccountId>(
			winners.as_slice(),
			staked.as_slice(),
		);
		evaluate_support::<AccountId>(&support_map)
	};

	let compact =
		CompactAssignments::from_assignment(assignments_reduced, nominator_index, validator_index)
			.map_err(|e| { println!("error in compact: {:?}", e); e })
			.expect("Failed to create compact");


	// winner ids to index
	let winners = winners.into_iter().map(|w| validator_index(&w).unwrap()).collect::<Vec<_>>();

	(compact, winners, score)
}

/// Make all validator and nominator request their payment
pub(crate) fn make_all_reward_payment(era: EraIndex) {
	let validators_with_reward = ErasRewardPoints::<Test>::get(era).individual.keys()
		.cloned()
		.collect::<Vec<_>>();

	// reward validators
	for validator_controller in validators_with_reward.iter().filter_map(Staking::bonded) {
		let ledger = <Ledger<Test>>::get(&validator_controller).unwrap();

		assert_ok!(Staking::payout_stakers(Origin::signed(1337), ledger.stash, era));
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
			Staking::active_era().unwrap().index,
			$era,
			"wrong active era {} != {}",
			Staking::active_era().unwrap().index,
			$era,
		);
	};
}

pub(crate) fn staking_events() -> Vec<Event<Test>> {
	System::events().into_iter().map(|r| r.event).filter_map(|e| {
		if let MetaEvent::staking(inner) = e {
			Some(inner)
		} else {
			None
		}
	}).collect()
}

pub(crate) fn balances(who: &AccountId) -> (Balance, Balance) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}
