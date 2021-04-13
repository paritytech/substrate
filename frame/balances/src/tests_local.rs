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
use frame_support::parameter_types;
use frame_support::traits::StorageMapShim;
use frame_support::weights::{Weight, DispatchInfo, IdentityFee};
use crate::{
	self as pallet_balances,
	Pallet, Config, decl_tests,
};
use pallet_transaction_payment::CurrencyAdapter;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
);

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
	type Call = Call;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
parameter_types! {
	pub const TransactionByteFee: u64 = 1;
}
impl pallet_transaction_payment::Config for Test {
	type OnChargeTransaction = CurrencyAdapter<Pallet<Test>, ()>;
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
		system::Provider<Test>,
		u64,
		super::AccountData<u64>,
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
		pallet_balances::GenesisConfig::<Test> {
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
		.existential_deposit(2)
		.build()
		.execute_with(|| {
			assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 100, 0));

			assert_eq!(
				events(),
				[
					Event::frame_system(system::Event::NewAccount(1)),
					Event::pallet_balances(crate::Event::Endowed(1, 100)),
					Event::pallet_balances(crate::Event::BalanceSet(1, 100, 0)),
				]
			);

			let res = Balances::slash(&1, 98);
			assert_eq!(res, (NegativeImbalance::new(98), 0));

			// no events
			assert_eq!(events(), []);

			let res = Balances::slash(&1, 1);
			assert_eq!(res, (NegativeImbalance::new(1), 0));

			assert_eq!(
				events(),
				[
					Event::frame_system(system::Event::KilledAccount(1)),
					Event::pallet_balances(crate::Event::DustLost(1, 1)),
				]
			);
		});
}
