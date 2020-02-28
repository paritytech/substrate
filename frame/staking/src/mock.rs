// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Test utilities

use crate::*;
use frame_support::{
	assert_ok, impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
	traits::{Currency, FindAuthor, Get, EstimateNextSessionChange},
	weights::Weight,
	StorageLinkedMap, StorageValue,
};
use frame_system::offchain::{CreateTransaction, Signer, TransactionSubmitter};
use sp_core::H256;
use sp_io;
use sp_phragmen::{
	build_support_map, evaluate_support, reduce, ExtendedBalance, StakedAssignment, PhragmenScore,
};
use sp_runtime::curve::PiecewiseLinear;
use sp_runtime::testing::{Header, TestXt, UintAuthorityId};
use sp_runtime::traits::{
	Convert, Extrinsic as ExtrinsicT, IdentityLookup, OnInitialize, SaturatedConversion, Zero,
};
use sp_runtime::Perbill;
use sp_staking::{
	offence::{OffenceDetails, OnOffenceHandler},
	SessionIndex,
};
use std::{cell::RefCell, collections::HashSet};

/// The AccountId alias in this test module.
pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u64;

pub const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";

/// Simple structure that exposes how u64 currency can be represented as... u64.
pub struct CurrencyToVoteHandler;
impl Convert<u64, u64> for CurrencyToVoteHandler {
	fn convert(x: u64) -> u64 {
		x
	}
}
impl Convert<u128, u64> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u64 {
		x.saturated_into()
	}
}

thread_local! {
	static SESSION: RefCell<(Vec<AccountId>, HashSet<AccountId>)> = RefCell::new(Default::default());
	static SESSION_PER_ERA: RefCell<SessionIndex> = RefCell::new(3);
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
	static SLASH_DEFER_DURATION: RefCell<EraIndex> = RefCell::new(0);
	static ELECTION_LOOKAHEAD: RefCell<BlockNumber> = RefCell::new(0);
	static PERIOD: RefCell<BlockNumber> = RefCell::new(1);
	pub(crate) static LOCAL_KEY_ACCOUNT: RefCell<AccountId> = RefCell::new(10);
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
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 {
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

impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system {}
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

pub struct PeriodicSessionChange<P>(sp_std::marker::PhantomData<P>);
impl<P> EstimateNextSessionChange<BlockNumber> for PeriodicSessionChange<P>
where
	P: Get<BlockNumber>,
{
	fn estimate_next_session_change(now: BlockNumber) -> BlockNumber {
		let period = P::get();
		let excess = now % period;
		now - excess + period
	}
}

/// Author of block is always 11
pub struct Author11;
impl FindAuthor<u64> for Author11 {
	fn find_author<'a, I>(_digests: I) -> Option<u64>
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
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
impl pallet_balances::Trait for Test {
	type Balance = Balance;
	type Event = MetaEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}
parameter_types! {
	pub const Offset: BlockNumber = 0;
	pub const UncleGenerations: u64 = 0;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(25);
}

/// We prefer using the dummy key defined in `mock::dummy_sr25519`, not `crate::sr25519`, since the
/// dummy one gives us some nice helpers and a fake `IdentifyAccount`.
pub struct TestStaking;
impl sp_runtime::BoundToRuntimeAppPublic for TestStaking {
	type Public = dummy_sr25519::AuthorityId;
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {
		pub staking: TestStaking,
		pub other: OtherSessionHandler,
	}
}

impl pallet_session::Trait for Test {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = (Staking, OtherSessionHandler,);
	type Event = MetaEvent;
	type ValidatorId = AccountId;
	type ValidatorIdOf = crate::StashOf<Test>;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
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
}

impl Trait for Test {
	type Currency = pallet_balances::Module<Self>;
	type Time = pallet_timestamp::Module<Self>;
	type CurrencyToVote = CurrencyToVoteHandler;
	type RewardRemainder = ();
	type Event = MetaEvent;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type SlashDeferDuration = SlashDeferDuration;
	type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BondingDuration = BondingDuration;
	type SessionInterface = Self;
	type RewardCurve = RewardCurve;
	type NextSessionChange = PeriodicSessionChange<Period>;
	type ElectionLookahead = ElectionLookahead;
	type Call = Call;
	type SubmitTransaction = SubmitTransaction;
	type KeyType = dummy_sr25519::AuthorityId;
}

pub(crate) mod dummy_sr25519 {
	use super::{LOCAL_KEY_ACCOUNT, AccountId};

	mod app_sr25519 {
		use sp_application_crypto::{app_crypto, KeyTypeId, sr25519};
		app_crypto!(sr25519, KeyTypeId(*b"vali"));
	}

	pub type AuthoritySignature = app_sr25519::Signature;
	pub type AuthorityId = app_sr25519::Public;

	impl sp_runtime::traits::IdentifyAccount for AuthorityId {
		type AccountId = u64;
		fn into_account(self) -> Self::AccountId {
			LOCAL_KEY_ACCOUNT.with(|v| *v.borrow())
		}
	}

	pub fn dummy_key_for(x: AccountId) -> AuthorityId {
		use sp_core::Pair;
		let mut raw_key = [0u8; 32];
		raw_key[0] = x as u8;
		let generic_key = sp_core::sr25519::Pair::from_string(
			&format!("{}/staking{}", super::PHRASE, x),
			None,
		).unwrap().public();
		generic_key.into()
	}
}

impl CreateTransaction<Test, Extrinsic> for Test {
	type Signature = dummy_sr25519::AuthoritySignature;
	type Public = dummy_sr25519::AuthorityId;
	fn create_transaction<F: Signer<Self::Public, Self::Signature>>(
		call: Call,
		_public: Self::Public,
		account: AccountId,
		_index: AccountIndex,
	) -> Option<(
		<Extrinsic as ExtrinsicT>::Call,
		<Extrinsic as ExtrinsicT>::SignaturePayload,
	)> {
		let extra = ();
		Some((call, (account, extra)))
	}
}

pub type Extrinsic = TestXt<Call, ()>;
type SubmitTransaction = TransactionSubmitter<dummy_sr25519::AuthorityId, Test, Extrinsic>;

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
	local_key_account: AccountId,
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
			local_key_account: 10,
		}
	}
}

impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
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
	pub fn invulnerables(mut self, invulnerables: Vec<u64>) -> Self {
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
	pub fn local_key_account(mut self, key: AccountId) -> Self {
		self.local_key_account = key;
		self
	}
	pub fn offchain_phragmen_ext(self) -> Self {
		self
			.session_per_era(3)
			.session_length(5)
			.election_lookahead(3)
			.local_key_account(11)
	}
	pub fn set_associated_constants(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
		SLASH_DEFER_DURATION.with(|v| *v.borrow_mut() = self.slash_defer_duration);
		SESSION_PER_ERA.with(|v| *v.borrow_mut() = self.session_per_era);
		ELECTION_LOOKAHEAD.with(|v| *v.borrow_mut() = self.election_lookahead);
		PERIOD.with(|v| *v.borrow_mut() = self.session_length);
		LOCAL_KEY_ACCOUNT.with(|v| *v.borrow_mut() = self.local_key_account);
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
			.map(|x| ((x + 1) * 10 + 1) as u64)
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
				// This allow us to have a total_payout different from 0.
				(999, 1_000_000_000_000),
			],
		}.assimilate_storage(&mut storage);

		let stake_21 = if self.fair { 1000 } else { 2000 };
		let stake_31 = if self.validator_pool {
			balance_factor * 1000
		} else {
			1
		};
		let status_41 = if self.validator_pool {
			StakerStatus::<AccountId>::Validator
		} else {
			StakerStatus::<AccountId>::Idle
		};
		let nominated = if self.nominate { vec![11, 21] } else { vec![] };
		let _ = GenesisConfig::<Test> {
			current_era: 0,
			stakers: if self.has_stakers {
				vec![
					// (stash, controller, staked_amount, status)
					(11, 10, balance_factor * 1000, StakerStatus::<AccountId>::Validator),
					(21, 20, stake_21, StakerStatus::<AccountId>::Validator),
					(31, 30, stake_31, StakerStatus::<AccountId>::Validator),
					(41, 40, balance_factor * 1000, status_41),
					// nominator
					(101, 100, balance_factor * 500, StakerStatus::<AccountId>::Nominator(nominated)),
				]
			} else {
				vec![]
			},
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
				SessionKeys {
					staking: dummy_sr25519::dummy_key_for(*x),
					other: UintAuthorityId(*x),
				}
			)).collect(),
		}.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);
		ext.execute_with(|| {
			let validators = Session::validators();
			SESSION.with(|x| *x.borrow_mut() = (validators.clone(), HashSet::new()));
		});
		ext
	}
}

pub type System = frame_system::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;
pub type Session = pallet_session::Module<Test>;
pub type Timestamp = pallet_timestamp::Module<Test>;
pub type Staking = Module<Test>;

pub fn check_exposure_all() {
	Staking::current_elected().into_iter().for_each(|acc| check_exposure(acc));
}

pub fn check_nominator_all() {
	<Nominators<Test>>::enumerate().for_each(|(acc, _)| check_nominator_exposure(acc));
}

/// Check for each selected validator: expo.total = Sum(expo.other) + expo.own
pub fn check_exposure(stash: u64) {
	assert_is_stash(stash);
	let expo = Staking::stakers(&stash);
	assert_eq!(
		expo.total as u128,
		expo.own as u128 + expo.others.iter().map(|e| e.value as u128).sum::<u128>(),
		"wrong total exposure for {:?}: {:?}",
		stash,
		expo,
	);
}

/// Check that for each nominator: slashable_balance > sum(used_balance)
/// Note: we might not consume all of a nominator's balance, but we MUST NOT over spend it.
pub fn check_nominator_exposure(stash: u64) {
	assert_is_stash(stash);
	let mut sum = 0;
	Staking::current_elected()
		.iter()
		.map(|v| Staking::stakers(v))
		.for_each(|e| e.others.iter().filter(|i| i.who == stash).for_each(|i| sum += i.value));
	let nominator_stake = Staking::slashable_balance_of(&stash);
	// a nominator cannot over-spend.
	assert!(
		nominator_stake >= sum,
		"failed: Nominator({}) stake({}) >= sum divided({})",
		stash,
		nominator_stake,
		sum,
	);
}

pub fn assert_is_stash(acc: u64) {
	assert!(Staking::bonded(&acc).is_some(), "Not a stash.");
}

pub fn assert_ledger_consistent(stash: u64) {
	assert_is_stash(stash);
	let ledger = Staking::ledger(stash - 1).unwrap();

	let real_total: Balance = ledger.unlocking.iter().fold(ledger.active, |a, c| a + c.value);
	assert_eq!(real_total, ledger.total);
}

pub fn bond_validator(stash: u64, ctrl: u64, val: u64) {
	let _ = Balances::make_free_balance_be(&stash, val);
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

pub fn bond_nominator(stash: u64, ctrl: u64, val: u64, target: Vec<u64>) {
	let _ = Balances::make_free_balance_be(&stash, val);
	assert_ok!(Staking::bond(
		Origin::signed(stash),
		ctrl,
		val,
		RewardDestination::Controller,
	));
	assert_ok!(Staking::nominate(Origin::signed(ctrl), target));
}

pub fn run_to_block(n: BlockNumber) {
	for b in System::block_number() + 1..=n {
		System::set_block_number(b);
		Session::on_initialize(b);
		Staking::on_initialize(b);
	}
}

pub fn advance_session() {
	let current_index = Session::current_index();
	start_session(current_index + 1);
}

pub fn start_session(session_index: SessionIndex) {
	// Compensate for session delay.
	let session_index = session_index + 1;
	for i in Session::current_index()..session_index {
		System::set_block_number((i + 1).into());
		Timestamp::set_timestamp(System::block_number() * 1000);
		Session::on_initialize(System::block_number());
		Staking::on_initialize(System::block_number());
	}

	assert_eq!(Session::current_index(), session_index);
}

pub fn start_era(era_index: EraIndex) {
	start_session((era_index * <SessionsPerEra as Get<u32>>::get()).into());
	assert_eq!(Staking::current_era(), era_index);
}

pub fn current_total_payout_for_duration(duration: u64) -> u64 {
	inflation::compute_total_payout(
		<Test as Trait>::RewardCurve::get(),
		<Module<Test>>::slot_stake() * 2,
		Balances::total_issuance(),
		duration,
	).0
}

pub fn reward_all_elected() {
	let rewards = <Module<Test>>::current_elected()
		.iter()
		.map(|v| (*v, 1))
		.collect::<Vec<_>>();

	<Module<Test>>::reward_by_ids(rewards)
}

pub fn validator_controllers() -> Vec<AccountId> {
	Session::validators()
		.into_iter()
		.map(|s| Staking::bonded(&s).expect("no controller for validator"))
		.collect()
}

pub fn on_offence_in_era(
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
			Staking::on_offence(offenders, slash_fraction, start_session);
			return;
		} else if bonded_era > era {
			break;
		}
	}

	if Staking::current_era() == era {
		Staking::on_offence(offenders, slash_fraction, Staking::current_era_start_session_index());
	} else {
		panic!("cannot slash in era {}", era);
	}
}

pub fn on_offence_now(
	offenders: &[OffenceDetails<AccountId, pallet_session::historical::IdentificationTuple<Test>>],
	slash_fraction: &[Perbill],
) {
	let now = Staking::current_era();
	on_offence_in_era(offenders, slash_fraction, now)
}

// winners will be chosen by simply their unweighted total backing stake. Nominator stake is
// distributed evenly.
pub fn horrible_phragmen_with_post_processing(
	do_reduce: bool,
) -> (
	Compact,
	Vec<ValidatorIndex>,
	PhragmenScore,
) {
	use std::collections::BTreeMap;

	let mut backing_stake_of: BTreeMap<AccountId, Balance> = BTreeMap::new();

	// self stake
	<Validators<Test>>::enumerate().for_each(|(who, _p)| {
		*backing_stake_of.entry(who).or_insert(Zero::zero()) += Staking::slashable_balance_of(&who)
	});

	// add nominator stuff
	<Nominators<Test>>::enumerate().for_each(|(who, nomination)| {
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
	<Nominators<Test>>::enumerate().for_each(|(who, nomination)| {
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
		let (_, _, better_score) = do_phragmen_with_post_processing(true, |_| {});

		let support = build_support_map::<AccountId>(&winners, &staked_assignment).0;
		let score = evaluate_support(&support);

		assert!(sp_phragmen::is_score_better(score, better_score));

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
	let assignments_reduced = sp_phragmen::assignment_staked_to_ratio::<
		AccountId,
		OffchainAccuracy,
	>(staked_assignment);

	let compact = Compact::from_assignment(
		assignments_reduced,
		nominator_index,
		validator_index,
	).unwrap();

	// winner ids to index
	let winners = winners.into_iter().map(|w| validator_index(&w).unwrap()).collect::<Vec<_>>();

	(compact, winners, score)
}

// Note: this should always logically reproduce [`offchain_election::prepare_submission`], yet we
// cannot do it since we want to have `tweak` injected into the process.
pub fn do_phragmen_with_post_processing(
	do_reduce: bool,
	tweak: impl FnOnce(&mut Vec<StakedAssignment<AccountId>>),
) -> (
	Compact,
	Vec<ValidatorIndex>,
	PhragmenScore,
) {
	// run phragmen on the default stuff.
	let sp_phragmen::PhragmenResult {
		winners,
		assignments,
	} = Staking::do_phragmen::<OffchainAccuracy>().unwrap();
	let winners = winners.into_iter().map(|(w, _)| w).collect::<Vec<AccountId>>();

	let stake_of = |who: &AccountId| -> ExtendedBalance {
		<CurrencyToVoteHandler as Convert<Balance, u64>>::convert(
			Staking::slashable_balance_of(&who)
		) as ExtendedBalance
	};
	let mut staked = sp_phragmen::assignment_ratio_to_staked(assignments, stake_of);

	// apply custom tweaks. awesome for testing.
	tweak(&mut staked);

	if do_reduce {
		reduce(&mut staked);
	}

	// convert back to ratio assignment. This takes less space.
	let snapshot_validators = Staking::snapshot_validators().unwrap();
	let snapshot_nominators = Staking::snapshot_nominators().unwrap();
	let nominator_index = |a: &AccountId| -> Option<NominatorIndex> {
		snapshot_nominators.iter().position(|x| x == a).map(|i| i as NominatorIndex)
	};
	let validator_index = |a: &AccountId| -> Option<ValidatorIndex> {
		snapshot_validators.iter().position(|x| x == a).map(|i| i as ValidatorIndex)
	};

	let assignments_reduced = sp_phragmen::assignment_staked_to_ratio(staked);

	// re-compute score by converting, yet again, into staked type
	let score = {
		let staked = sp_phragmen::assignment_ratio_to_staked(
			assignments_reduced.clone(),
			Staking::slashable_balance_of_extended,
		);

		let (support_map, _) = build_support_map::<AccountId>(
			winners.as_slice(),
			staked.as_slice(),
		);
		evaluate_support::<AccountId>(&support_map)
	};

	let compact = Compact::from_assignment(
		assignments_reduced,
		nominator_index,
		validator_index,
	).unwrap();


	// winner ids to index
	let winners = winners.into_iter().map(|w| validator_index(&w).unwrap()).collect::<Vec<_>>();

	(compact, winners, score)
}

#[macro_export]
macro_rules! assert_session_era {
	($session:expr, $era:expr) => {
		assert_eq!(Session::current_index(), $session);
		assert_eq!(Staking::current_era(), $era);
	};
}
