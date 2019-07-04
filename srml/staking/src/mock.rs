// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use std::{collections::HashSet, cell::RefCell};
use primitives::Perbill;
use primitives::traits::{IdentityLookup, Convert, OpaqueKeys, OnInitialize};
use primitives::testing::{Header, UintAuthorityId};
use substrate_primitives::{H256, Blake2Hasher};
use runtime_io;
use srml_support::{assert_ok, impl_outer_origin, parameter_types, EnumerableStorageMap};
use srml_support::traits::{Currency, Get};
use crate::{EraIndex, GenesisConfig, Module, Trait, StakerStatus,
	ValidatorPrefs, RewardDestination, Nominators
};

/// The AccountId alias in this test module.
pub type AccountId = u64;
pub type BlockNumber = u64;
pub type Balance = u64;

/// Simple structure that exposes how u64 currency can be represented as... u64.
pub struct CurrencyToVoteHandler;
impl Convert<u64, u64> for CurrencyToVoteHandler {
	fn convert(x: u64) -> u64 { x }
}
impl Convert<u128, u64> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u64 {
		x as u64
	}
}

thread_local! {
	static SESSION: RefCell<(Vec<AccountId>, HashSet<AccountId>)> = RefCell::new(Default::default());
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
}

pub struct TestSessionHandler;
impl session::SessionHandler<AccountId> for TestSessionHandler {
	fn on_new_session<Ks: OpaqueKeys>(_changed: bool, validators: &[(AccountId, Ks)]) {
		SESSION.with(|x|
			*x.borrow_mut() = (validators.iter().map(|x| x.0.clone()).collect(), HashSet::new())
		);
	}

	fn on_disabled(validator_index: usize) {
		SESSION.with(|d| {
			let mut d = d.borrow_mut();
			let value = d.0[validator_index];
			println!("on_disabled {} -> {}", validator_index, value);
			d.1.insert(value);
		})
	}
}

pub fn is_disabled(validator: AccountId) -> bool {
	SESSION.with(|d| d.borrow().1.contains(&validator))
}

pub struct ExistentialDeposit;
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow())
	}
}

impl_outer_origin!{
	pub enum Origin for Test {}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
}
parameter_types! {
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
	pub const TransactionBaseFee: u64 = 0;
	pub const TransactionByteFee: u64 = 0;
}
impl balances::Trait for Test {
	type Balance = u64;
	type OnFreeBalanceZero = Staking;
	type OnNewAccount = ();
	type Event = ();
	type TransactionPayment = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
	type TransactionBaseFee = TransactionBaseFee;
	type TransactionByteFee = TransactionByteFee;
}
parameter_types! {
	pub const Period: BlockNumber = 1;
	pub const Offset: BlockNumber = 0;
}
impl session::Trait for Test {
	type OnSessionEnding = Staking;
	type Keys = UintAuthorityId;
	type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
	type SessionHandler = TestSessionHandler;
	type Event = ();
	type SelectInitialValidators = Staking;
}
impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
}
parameter_types! {
	pub const SessionsPerEra: session::SessionIndex = 3;
	pub const BondingDuration: EraIndex = 3;
}
impl Trait for Test {
	type Currency = balances::Module<Self>;
	type CurrencyToVote = CurrencyToVoteHandler;
	type OnRewardMinted = ();
	type Event = ();
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
}

pub struct ExtBuilder {
	existential_deposit: u64,
	reward: u64,
	validator_pool: bool,
	nominate: bool,
	validator_count: u32,
	minimum_validator_count: u32,
	fair: bool,
	num_validators: Option<u32>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 0,
			reward: 10,
			validator_pool: false,
			nominate: true,
			validator_count: 2,
			minimum_validator_count: 0,
			fair: true,
			num_validators: None,
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
	pub fn fair(mut self, is_fair: bool) -> Self {
		self.fair = is_fair;
		self
	}
	pub fn num_validators(mut self, num_validators: u32) -> Self {
		self.num_validators = Some(num_validators);
		self
	}
	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
	}
	pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
		self.set_associated_consts();
		let (mut t, mut c) = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		let balance_factor = if self.existential_deposit > 0 {
			256
		} else {
			1
		};

		let num_validators = self.num_validators.unwrap_or(self.validator_count);
		let validators = (0..num_validators)
			.map(|x| ((x + 1) * 10) as u64)
			.collect::<Vec<_>>();

		let _ = balances::GenesisConfig::<Test>{
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
			],
			vesting: vec![],
		}.assimilate_storage(&mut t, &mut c);

		let stake_21 = if self.fair { 1000 } else { 2000 };
		let stake_31 = if self.validator_pool { balance_factor * 1000 } else { 1 };
		let status_41 = if self.validator_pool {
			StakerStatus::<AccountId>::Validator
		} else {
			StakerStatus::<AccountId>::Idle
		};
		let nominated = if self.nominate { vec![11, 21] } else { vec![] };
		let _ = GenesisConfig::<Test>{
			current_era: 0,
			stakers: vec![
				(11, 10, balance_factor * 1000, StakerStatus::<AccountId>::Validator),
				(21, 20, stake_21, StakerStatus::<AccountId>::Validator),
				(31, 30, stake_31, StakerStatus::<AccountId>::Validator),
				(41, 40, balance_factor * 1000, status_41),
				// nominator
				(101, 100, balance_factor * 500, StakerStatus::<AccountId>::Nominator(nominated))
			],
			validator_count: self.validator_count,
			minimum_validator_count: self.minimum_validator_count,
			session_reward: Perbill::from_millionths((1000000 * self.reward / balance_factor) as u32),
			offline_slash: Perbill::from_percent(5),
			current_session_reward: self.reward,
			offline_slash_grace: 0,
			invulnerables: vec![],
		}.assimilate_storage(&mut t, &mut c);

		let _ = timestamp::GenesisConfig::<Test>{
			minimum_period: 5,
		}.assimilate_storage(&mut t, &mut c);

		let _ = session::GenesisConfig::<Test> {
			keys: validators.iter().map(|x| (*x, UintAuthorityId(*x))).collect(),
		}.assimilate_storage(&mut t, &mut c);

		let mut ext = t.into();
		runtime_io::with_externalities(&mut ext, || {
			let validators = Session::validators();
			SESSION.with(|x|
				*x.borrow_mut() = (validators.clone(), HashSet::new())
			);
		});
		ext
	}
}

pub type System = system::Module<Test>;
pub type Balances = balances::Module<Test>;
pub type Session = session::Module<Test>;
pub type Timestamp = timestamp::Module<Test>;
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
		expo.total as u128, expo.own as u128 + expo.others.iter().map(|e| e.value as u128).sum::<u128>(),
		"wrong total exposure for {:?}: {:?}", stash, expo,
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
		.for_each(|e| e.others.iter()
			.filter(|i| i.who == stash)
			.for_each(|i| sum += i.value));
	let nominator_stake = Staking::slashable_balance_of(&stash);
	// a nominator cannot over-spend.
	assert!(
		nominator_stake >= sum,
		"failed: Nominator({}) stake({}) >= sum divided({})", stash, nominator_stake, sum,
	);
}

pub fn assert_total_expo(stash: u64, val: u64) {
	let expo = Staking::stakers(&stash);
	assert_eq!(expo.total, val);
}

pub fn assert_is_stash(acc: u64) {
	assert!(Staking::bonded(&acc).is_some(), "Not a stash.");
}

pub fn bond_validator(acc: u64, val: u64) {
	// a = controller
	// a + 1 = stash
	let _ = Balances::make_free_balance_be(&(acc+1), val);
	assert_ok!(Staking::bond(Origin::signed(acc+1), acc, val, RewardDestination::Controller));
	assert_ok!(Staking::validate(Origin::signed(acc), ValidatorPrefs::default()));
}

pub fn bond_nominator(acc: u64, val: u64, target: Vec<u64>) {
	// a = controller
	// a + 1 = stash
	let _ = Balances::make_free_balance_be(&(acc+1), val);
	assert_ok!(Staking::bond(Origin::signed(acc+1), acc, val, RewardDestination::Controller));
	assert_ok!(Staking::nominate(Origin::signed(acc), target));
}

pub fn start_session(session_index: session::SessionIndex) {
	// Compensate for session delay
	let session_index = session_index + 1;
	for i in 0..(session_index - Session::current_index()) {
		System::set_block_number((i + 1).into());
		Session::on_initialize(System::block_number());
	}
	assert_eq!(Session::current_index(), session_index);
}

pub fn start_era(era_index: EraIndex) {
	start_session((era_index * 3).into());
	assert_eq!(Staking::current_era(), era_index);
}
