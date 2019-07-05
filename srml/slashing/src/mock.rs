// Copyright 2019 Parity Technologies (UK) Ltd.
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

#![allow(unused)]

use super::*;
use primitives::{Perbill, traits::{IdentityLookup, Convert}, testing::{Header, UintAuthorityId}};
use substrate_primitives::{Blake2Hasher, H256};
use srml_staking::{GenesisConfig, StakerStatus, Exposure, IndividualExposure};
use srml_support::{impl_outer_origin, parameter_types, traits::{Currency, Get}};
use rstd::{marker::PhantomData, cell::RefCell};
use std::collections::HashSet;

pub type AccountId = u64;
pub type BlockNumber = u64;
pub type Balance = u64;
pub type Balances = balances::Module<Test>;
pub type Session = session::Module<Test>;
pub type Staking = srml_staking::Module<Test>;
pub type BalanceOf<T> = <<T as srml_staking::Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
pub type ExtendedBalance = u128;

pub struct CurrencyToVoteHandler;

thread_local! {
	static SESSION: RefCell<(Vec<AccountId>, HashSet<AccountId>)> = RefCell::new(Default::default());
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
}

impl Convert<u64, u64> for CurrencyToVoteHandler {
	fn convert(x: u64) -> u64 { x }
}
impl Convert<u128, u64> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u64 {
		x as u64
	}
}

pub struct ExistentialDeposit;
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 {
		0
	}
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

impl_outer_origin!{
	pub enum Origin for Test {}
}

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

impl balances::Trait for Test {
	type Balance = Balance;
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

impl srml_staking::Trait for Test {
	type Currency = balances::Module<Self>;
	type CurrencyToVote = CurrencyToVoteHandler;
	type OnRewardMinted = ();
	type Event = ();
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
}

impl session::Trait for Test {
	type SelectInitialValidators = Staking;
	type OnSessionEnding = Staking;
	type Keys = UintAuthorityId;
	type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
	type SessionHandler = ();
	type Event = ();
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
}

parameter_types! {
	pub const SessionsPerEra: session::SessionIndex = 3;
	pub const BondingDuration: srml_staking::EraIndex = 3;
}

parameter_types! {
	pub const Period: BlockNumber = 1;
	pub const Offset: BlockNumber = 0;
}

parameter_types! {
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
	pub const TransactionBaseFee: u64 = 0;
	pub const TransactionByteFee: u64 = 0;
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

impl Misconduct<Exposure<u64, u64>> for Test {
	type Severity = u64;

	fn as_misconduct_level(&self, _severity: Fraction<Self::Severity>) -> u8 {
		1
	}

	fn on_misconduct<SR>(&mut self, _misbehaved: &[SR]) -> Fraction<Self::Severity>
	where
		SR: SlashRecipient<Self::AccountId, Exposure<u64, u64>>,
	{
		Fraction::new(1, 10)
	}
}

pub struct StakingSlasher<T, SR, Exposure> {
	t: PhantomData<T>,
	sr: PhantomData<SR>,
	e: PhantomData<Exposure>,
}

impl<T, SR, Exposure> OnSlashing<T, SR, Exposure> for StakingSlasher<T, SR, Exposure>
where
	T: srml_staking::Trait + Misconduct<Exposure>,
	SR: SlashRecipient<T::AccountId, Exposure>,
	// Balance: Into<u128> + Clone,
{
	fn slash(to_punish: &[SR], severity: Fraction<T::Severity>) {
		// hack to convert both to `u128` and calculate the amount to slash
		// then convert it back `BalanceOf<T>`

		let to_u128 = |b: BalanceOf<T>|
			<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;
		let to_balance = |b: ExtendedBalance|
			<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
		let slash = |balance: u128, severity: Fraction<T::Severity>| {
			let d = balance.saturating_mul(severity.denominator().into());
			let n = severity.numerator().into();
			let res = d.checked_div(n).unwrap_or(0);
			println!("slash: {}", res);
			to_balance(res)
		};

		if severity.is_zero() {
			return;
		}

		for who in to_punish {
			let account_id = who.account_id();
			println!("slash from account: {}", account_id);
			let balance = to_u128(T::Currency::free_balance(account_id));
			let slash_amount = slash(balance, severity);

			// slash the validator
			T::Currency::slash(account_id, slash_amount);

			let exposure = <srml_staking::Module<T>>::stakers(account_id);
			// slash nominators for the same severity
			for nominator in &exposure.others {
				println!("slash from nominator: {}", nominator.who);
				let balance: u128 = to_u128(nominator.value);
				let slash_amount = slash(balance, severity);
				T::Currency::slash(&nominator.who, slash_amount);
			}
		}
	}
}

pub struct MockSlashRecipient(pub u64);

impl SlashRecipient<u64, Exposure<u64, u64>> for MockSlashRecipient {
	fn account_id(&self) -> &u64 {
		&self.0
	}
}
