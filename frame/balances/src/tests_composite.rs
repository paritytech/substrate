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

#![cfg(test)]

use sp_runtime::{
	Perbill,
	traits::{ConvertInto, IdentityLookup},
	testing::Header,
};
use sp_core::H256;
use sp_io;
use frame_support::{impl_outer_origin, parameter_types};
use frame_support::traits::Get;
use frame_support::weights::{Weight, DispatchInfo};
use std::cell::RefCell;
use crate::{GenesisConfig, Module, Trait, decl_tests, tests::CallWithDispatchInfo};

use frame_system as system;
impl_outer_origin!{
	pub enum Origin for Test {}
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
impl frame_system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = CallWithDispatchInfo;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = super::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
parameter_types! {
	pub const TransactionByteFee: u64 = 1;
}
impl pallet_transaction_payment::Trait for Test {
	type Currency = Module<Test>;
	type OnTransactionPayment = ();
	type TransactionByteFee = TransactionByteFee;
	type WeightToFee = ConvertInto;
	type FeeMultiplierUpdate = ();
}
impl Trait for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = system::Module<Test>;
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
		t.into()
	}
}

decl_tests!{ Test, ExtBuilder, EXISTENTIAL_DEPOSIT }
