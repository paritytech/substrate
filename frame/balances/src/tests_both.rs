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

#![cfg(test)]

use sp_runtime::{
	Perbill,
	traits::IdentityLookup,
	testing::Header,
};
use sp_core::H256;
use sp_io;
use frame_support::{impl_outer_origin, impl_outer_event, parameter_types};
use frame_support::traits::{Get, StorageMapShim};
use frame_support::weights::Weight;
use std::cell::RefCell;
use crate::{GenesisConfig, Trait, tests::CallWithDispatchInfo};
use frame_support::{
	assert_noop, assert_ok,
	traits::{
		LockableCurrency, LockIdentifier, WithdrawReasons,
		Currency, ExistenceRequirement::AllowDeath,
	}
};

use frame_system as system;
impl_outer_origin!{
	pub enum Origin for Test {}
}

mod balances {
	pub use crate::Event;
}
mod balances0 {
	pub type Event<T> = crate::Event<T, crate::Instance0>;
}

impl_outer_event! {
	pub enum Event for Test {
		system<T>,
		balances<T>,
		balances0<T>,
	}
}

thread_local! {
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
}

pub struct ExistentialDeposit;
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 { EXISTENTIAL_DEPOSIT.with(|v| *v.borrow()) }
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
type AccountId = u64;
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = CallWithDispatchInfo;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = super::AccountData<AccountId>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
impl Trait for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = system::Module<Test>;
}
impl Trait<crate::Instance0> for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = StorageMapShim<
		super::Account<Test, crate::Instance0>,
		crate::CallOnCreatedAccount<Test, crate::Instance0>,
		crate::CallKillAccount<Test, crate::Instance0>,
		AccountId,
		super::AccountData<AccountId>
	>;
}

type System = system::Module<Test>;
type Balances = crate::Module<Test>;
type Balances0 = crate::Module<Test, crate::Instance0>;
const ID_1: LockIdentifier = *b"1       ";

pub struct ExtBuilder {
	existential_deposit: u64,
	monied: bool,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 1,
			monied: false,
		}
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn monied(mut self, monied: bool) -> Self {
		self.monied = monied;
		self
	}
	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
	}
	pub fn build(self) -> sp_io::TestExternalities {
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		GenesisConfig::<Test> {
			balances: if self.monied {
				vec![
					(1, 10 * self.existential_deposit),
					(2, 20 * self.existential_deposit),
					(3, 30 * self.existential_deposit),
					(4, 40 * self.existential_deposit),
					(5, 50 * self.existential_deposit),
					(12, 10 * self.existential_deposit),
				]
			} else {
				vec![]
			},
		}.assimilate_storage(&mut t).unwrap();

		GenesisConfig::<Test, crate::Instance0> {
			balances: if self.monied {
				vec![
					(1, 10 * self.existential_deposit),
					(2, 20 * self.existential_deposit),
					(3, 30 * self.existential_deposit),
					(4, 40 * self.existential_deposit),
					(12, 10 * self.existential_deposit),
				]
			} else {
				vec![]
			},
		}.assimilate_storage(&mut t).unwrap();

		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

#[test]
fn two_instance_are_independent_to_lock() {
	ExtBuilder::default().monied(true).existential_deposit(1).build().execute_with(|| {
		assert_eq!(System::refs(&1), 1);
		assert_eq!(Balances::free_balance(1), 10);
		Balances::set_lock(ID_1, &1, 9, WithdrawReasons::all());
		assert_eq!(System::refs(&1), 2);
		assert_noop!(
			<Balances as Currency<_>>::transfer(&1, &2, 5, AllowDeath),
			crate::Error::<Test, crate::DefaultInstance>::LiquidityRestrictions
		);

		assert_eq!(Balances0::locks(&1).len(), 0);
		assert_ok!(Balances0::transfer(Origin::signed(1), 2, 5));
		assert_eq!(Balances0::total_balance(&1), 5);
		Balances0::set_lock(ID_1, &1, 9, WithdrawReasons::all());
		Balances0::set_lock(ID_1, &1, 9, WithdrawReasons::all());
		assert_eq!(Balances0::locks(&1).len(), 1);
		assert_eq!(System::refs(&1), 2);
		assert_noop!(
			<Balances0 as Currency<_>>::transfer(&1, &2, 5, AllowDeath),
			crate::Error::<Test, crate::Instance0>::LiquidityRestrictions
		);
		Balances0::remove_lock(ID_1, &1);
		assert_ok!(<Balances0 as Currency<_>>::transfer(&1, &2, 5, AllowDeath));
		assert_eq!(System::refs(&1), 1);
		assert_eq!(Balances0::free_balance(1), 0);

		Balances::remove_lock(ID_1, &1);
		assert_eq!(System::refs(&1), 0);
		assert_ok!(<Balances as Currency<_>>::transfer(&1, &2, 5, AllowDeath));

		let expect_events = vec![
			Event::balances0(crate::RawEvent::Transfer(1, 2, 5)),
			Event::balances0(crate::RawEvent::KilledAccount(1)),
			Event::balances0(crate::RawEvent::Transfer(1, 2, 5)),
			Event::balances(crate::RawEvent::Transfer(1, 2, 5)),
		];
		assert_eq!(System::events().len(), expect_events.len());
		assert!(!System::events().iter().zip(expect_events).any(|(a, b)| a.event != b));
	});
}

#[test]
fn test_keep_alive_error() {
	ExtBuilder::default().monied(true).existential_deposit(1).build().execute_with(|| {
		assert_ok!(Balances::transfer(Origin::signed(12), 13, 5));
		assert_ok!(Balances0::transfer(Origin::signed(12), 13, 5));
		assert_eq!(System::refs(&13), 1);
		assert_eq!(Balances0::locks(&1).len(), 0);
		assert_eq!(Balances::total_balance(&13), 5);
		assert_eq!(Balances::total_balance(&12), 5);
		assert_eq!(Balances0::total_balance(&13), 5);
		assert_eq!(Balances0::total_balance(&12), 5);
		assert_noop!(
			Balances::transfer(Origin::signed(13), 12, 5),
			crate::Error::<Test, crate::DefaultInstance>::KeepAlive,
		);
		let expect_events = vec![
			Event::system(system::RawEvent::NewAccount(13)),
			Event::balances(crate::RawEvent::Endowed(13, 5)),
			Event::balances(crate::RawEvent::Transfer(12, 13, 5)),
			Event::balances0(crate::RawEvent::NewAccount(13)),
			Event::balances0(crate::RawEvent::Endowed(13, 5)),
			Event::balances0(crate::RawEvent::Transfer(12, 13, 5)),
		];
		assert_eq!(System::events().len(), expect_events.len());
		assert!(!System::events().iter().zip(expect_events).any(|(a, b)| a.event != b));
	});
}

#[test]
fn cannot_create_account_with_dead_main_account() {
	ExtBuilder::default().monied(true).existential_deposit(1).build().execute_with(|| {
		assert_noop!(
			Balances0::transfer(Origin::signed(1), 100, 5),
			crate::Error::<Test, crate::Instance0>::DeadMainAccount,
		);
		let _ = Balances0::deposit_creating(&100, 100);
		assert_eq!(Balances::total_balance(&100), 0);

		assert_eq!(System::refs(&5), 0);
		assert_eq!(Balances0::locks(&5).len(), 0);
		assert_ok!(Balances0::transfer(Origin::signed(1), 5, 3));
		assert_eq!(System::refs(&5), 1);
		assert_eq!(Balances0::locks(&5).len(), 0);

		let expect_events = vec![
			Event::balances0(crate::RawEvent::NewAccount(5)),
			Event::balances0(crate::RawEvent::Endowed(5, 3)),
			Event::balances0(crate::RawEvent::Transfer(1, 5, 3)),
		];
		assert_eq!(System::events().len(), expect_events.len());
		assert!(!System::events().iter().zip(expect_events).any(|(a, b)| a.event != b));
	});
}
