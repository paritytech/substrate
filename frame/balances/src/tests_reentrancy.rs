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

//! Test setup for potential reentracy and lost updates of nested mutations.

#![cfg(test)]

use crate::{self as pallet_balances, Config, Pallet};
use frame_support::{parameter_types, traits::StorageMapShim, weights::IdentityFee};
use pallet_transaction_payment::CurrencyAdapter;
use sp_core::H256;
use sp_io;
use sp_runtime::{testing::Header, traits::IdentityLookup};

use crate::*;
use frame_support::{
	assert_ok,
	traits::{Currency, ReservableCurrency},
};
use frame_system::RawOrigin;

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
	type BaseCallFilter = frame_support::traits::Everything;
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
	pub const OperationalFeeMultiplier: u8 = 5;
}
impl pallet_transaction_payment::Config for Test {
	type OnChargeTransaction = CurrencyAdapter<Pallet<Test>, ()>;
	type TransactionByteFee = TransactionByteFee;
	type OperationalFeeMultiplier = OperationalFeeMultiplier;
	type WeightToFee = IdentityFee<u64>;
	type FeeMultiplierUpdate = ();
}

pub struct OnDustRemoval;
impl OnUnbalanced<NegativeImbalance<Test>> for OnDustRemoval {
	fn on_nonzero_unbalanced(amount: NegativeImbalance<Test>) {
		assert_ok!(Balances::resolve_into_existing(&1, amount));
	}
}
parameter_types! {
	pub const MaxLocks: u32 = 50;
	pub const MaxReserves: u32 = 2;
}
impl Config for Test {
	type Balance = u64;
	type DustRemoval = OnDustRemoval;
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore =
		StorageMapShim<super::Account<Test>, system::Provider<Test>, u64, super::AccountData<u64>>;
	type MaxLocks = MaxLocks;
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

pub struct ExtBuilder {
	existential_deposit: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self { existential_deposit: 1 }
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}

	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
	}

	pub fn build(self) -> sp_io::TestExternalities {
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> { balances: vec![] }
			.assimilate_storage(&mut t)
			.unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

#[test]
fn transfer_dust_removal_tst1_should_work() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// Verification of reentrancy in dust removal
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 1000, 0));
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 2, 500, 0));

		// In this transaction, account 2 free balance
		// drops below existential balance
		// and dust balance is removed from account 2
		assert_ok!(Balances::transfer(RawOrigin::Signed(2).into(), 3, 450));

		// As expected dust balance is removed.
		assert_eq!(Balances::free_balance(&2), 0);

		// As expected beneficiary account 3
		// received the transfered fund.
		assert_eq!(Balances::free_balance(&3), 450);

		// Dust balance is deposited to account 1
		// during the process of dust removal.
		assert_eq!(Balances::free_balance(&1), 1050);

		// Verify the events
		// Number of events expected is 8
		assert_eq!(System::events().len(), 11);

		System::assert_has_event(Event::Balances(crate::Event::Transfer(2, 3, 450)));
		System::assert_has_event(Event::Balances(crate::Event::DustLost(2, 50)));
	});
}

#[test]
fn transfer_dust_removal_tst2_should_work() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// Verification of reentrancy in dust removal
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 1000, 0));
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 2, 500, 0));

		// In this transaction, account 2 free balance
		// drops below existential balance
		// and dust balance is removed from account 2
		assert_ok!(Balances::transfer(RawOrigin::Signed(2).into(), 1, 450));

		// As expected dust balance is removed.
		assert_eq!(Balances::free_balance(&2), 0);

		// Dust balance is deposited to account 1
		// during the process of dust removal.
		assert_eq!(Balances::free_balance(&1), 1500);

		// Verify the events
		// Number of events expected is 8
		assert_eq!(System::events().len(), 9);

		System::assert_has_event(Event::Balances(crate::Event::Transfer(2, 1, 450)));
		System::assert_has_event(Event::Balances(crate::Event::DustLost(2, 50)));
	});
}

#[test]
fn repatriating_reserved_balance_dust_removal_should_work() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// Verification of reentrancy in dust removal
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 1, 1000, 0));
		assert_ok!(Balances::set_balance(RawOrigin::Root.into(), 2, 500, 0));

		// Reserve a value on account 2,
		// Such that free balance is lower than
		// Exestintial deposit.
		assert_ok!(Balances::reserve(&2, 450));

		// Transfer of reserved fund from slashed account 2 to
		// beneficiary account 1
		assert_ok!(Balances::repatriate_reserved(&2, &1, 450, Status::Free), 0);

		// Since free balance of account 2 is lower than
		// existential deposit, dust amount is
		// removed from the account 2
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 0);

		// account 1 is credited with reserved amount
		// together with dust balance during dust
		// removal.
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(1), 1500);

		// Verify the events
		// Number of events expected is 10
		assert_eq!(System::events().len(), 10);

		System::assert_has_event(Event::Balances(crate::Event::ReserveRepatriated(
			2,
			1,
			450,
			Status::Free,
		)));

		System::assert_last_event(Event::Balances(crate::Event::DustLost(2, 50)));
	});
}
