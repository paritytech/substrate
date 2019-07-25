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

use super::*;
use serde::{Serialize, Deserialize};
use sr_primitives::{Perbill, traits::{BlakeTwo256, IdentityLookup, Convert}, testing::{Header, UintAuthorityId}};
use substrate_primitives::{Blake2Hasher, H256};
use srml_support::{impl_outer_origin, parameter_types, traits::{Get, WindowLength}};
use std::{collections::HashSet, cell::RefCell};
use parity_codec::{Encode, Decode};

pub type AccountId = u64;
pub type Balance = u64;
pub type BlockNumber = u64;
pub type Staking = srml_staking::Module<Test>;

pub struct CurrencyToVoteHandler;

thread_local! {
	static NEXT_VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
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

#[derive(Debug, Copy, Clone, Encode, Decode, Serialize, Deserialize, PartialEq)]
pub enum Kind {
	One,
	Two,
	Three,
	Four,
}

impl WindowLength<u32> for Kind {
	fn window_length(&self) -> &u32 {
		match self {
			Kind::One => &4,
			Kind::Two => &3,
			Kind::Three => &2,
			Kind::Four => &u32::max_value(),
		}
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
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type WeightMultiplierUpdate = ();
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
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
	type WeightToFee = ();
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
	type SessionInterface = Self;
	type Time = timestamp::Module<Self>;
}

impl srml_session::Trait for Test {
	type SelectInitialValidators = Staking;
	type OnSessionEnding = Staking;
	type Keys = UintAuthorityId;
	type ShouldEndSession = srml_session::PeriodicSessions<Period, Offset>;
	type SessionHandler = ();
	type Event = ();
	type ValidatorId = AccountId;
	type ValidatorIdOf = srml_staking::StashOf<Test>;
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
}

impl Trait for Test {
	type MisbehaviorKind = Kind;
	type SessionKey = UintAuthorityId;
}

impl srml_session::historical::Trait for Test {
	type FullIdentification = srml_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = srml_staking::ExposureOf<Test>;
}

parameter_types! {
	pub const MinimumPeriod: u64 = 5;
	pub const SessionsPerEra: srml_session::SessionIndex = 3;
	pub const BondingDuration: srml_staking::EraIndex = 3;
	pub const Period: BlockNumber = 1;
	pub const Offset: BlockNumber = 0;
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
	pub const TransactionBaseFee: u64 = 0;
	pub const TransactionByteFee: u64 = 0;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();

	srml_session::GenesisConfig::<Test> {
		keys: NEXT_VALIDATORS.with(|l|
			l.borrow().iter().cloned().map(|i| (i, UintAuthorityId(i))).collect()
		),
	}.assimilate_storage(&mut t.0, &mut t.1).unwrap();
	runtime_io::TestExternalities::new_with_children(t)
}
