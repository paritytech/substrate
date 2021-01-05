// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
	traits::IdentityLookup,
	testing::Header,
};
use sp_core::H256;
use sp_io;
use frame_support::{impl_outer_origin, impl_outer_event, parameter_types};
use frame_support::traits::StorageMapShim;
use frame_support::weights::{Weight, DispatchInfo, IdentityFee};
use crate::{GenesisConfig, Module, Config, decl_tests, tests::CallWithDispatchInfo};
use pallet_transaction_payment::CurrencyAdapter;

use frame_system as system;
impl_outer_origin!{
	pub enum Origin for Test {}
}

mod balances {
	pub use crate::Event;
}

impl_outer_event! {
	pub enum Event for Test {
		system<T>,
		balances<T>,
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
	pub static ExistentialDeposit: u64 = 0;
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = CallWithDispatchInfo;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = ();
	type AccountData = super::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = Module<Test>;
	type SystemWeightInfo = ();
	type SS58Prefix = ();
}
parameter_types! {
	pub const TransactionByteFee: u64 = 1;
}
impl pallet_transaction_payment::Config for Test {
	type OnChargeTransaction = CurrencyAdapter<Module<Test>, ()>;
	type TransactionByteFee = TransactionByteFee;
	type WeightToFee = IdentityFee<u64>;
	type FeeMultiplierUpdate = ();
}
parameter_types! {
	pub const MaxLocks: u32 = 50;
}
impl Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = StorageMapShim<
		super::Account<Test>,
		system::CallOnCreatedAccount<Test>,
		system::CallKillAccount<Test>,
		u64, super::AccountData<u64>
	>;
	type MaxLocks = MaxLocks;
	type WeightInfo = ();
}

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
		if self.existential_deposit == 0 {
			self.existential_deposit = 1;
		}
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
					(12, 10 * self.existential_deposit)
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

decl_tests!{ Test, ExtBuilder, EXISTENTIAL_DEPOSIT }

#[test]
fn emit_events_with_no_existential_deposit_suicide_with_dust() {
	<ExtBuilder>::default()
		.existential_deposit(0)
		.build()
		.execute_with(|| {
			assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 100, 0));

			assert_eq!(
				events(),
				[
					Event::system(system::RawEvent::NewAccount(1)),
					Event::balances(RawEvent::Endowed(1, 100)),
					Event::balances(RawEvent::BalanceSet(1, 100, 0)),
				]
			);

			let _ = Balances::slash(&1, 99);

			// no events
			assert_eq!(events(), []);

			assert_ok!(System::suicide(Origin::signed(1)));

			assert_eq!(
				events(),
				[
					Event::balances(RawEvent::DustLost(1, 1)),
					Event::system(system::RawEvent::KilledAccount(1))
				]
			);
		});
}
