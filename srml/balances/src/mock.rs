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

#![cfg(test)]

use primitives::{traits::{IdentityLookup}, testing::Header};
use substrate_primitives::{H256, Blake2Hasher};
use runtime_io;
use srml_support::{impl_outer_origin, traits::Get};
use std::cell::RefCell;
use crate::{GenesisConfig, Module, Trait};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

thread_local! {
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
	static TRANSFER_FEE: RefCell<u64> = RefCell::new(0);
	static CREATION_FEE: RefCell<u64> = RefCell::new(0);
	static TRANSACTION_BASE_FEE: RefCell<u64> = RefCell::new(0);
	static TRANSACTION_BYTE_FEE: RefCell<u64> = RefCell::new(0);
}

pub struct ExistentialDeposit;
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 { EXISTENTIAL_DEPOSIT.with(|v| *v.borrow()) }
}

pub struct TransferFee;
impl Get<u64> for TransferFee {
	fn get() -> u64 { TRANSFER_FEE.with(|v| *v.borrow()) }
}

pub struct CreationFee;
impl Get<u64> for CreationFee {
	fn get() -> u64 { CREATION_FEE.with(|v| *v.borrow()) }
}

pub struct TransactionBaseFee;
impl Get<u64> for TransactionBaseFee {
	fn get() -> u64 { TRANSACTION_BASE_FEE.with(|v| *v.borrow()) }
}

pub struct TransactionByteFee;
impl Get<u64> for TransactionByteFee {
	fn get() -> u64 { TRANSACTION_BYTE_FEE.with(|v| *v.borrow()) }
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Runtime;
impl system::Trait for Runtime {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
}
impl Trait for Runtime {
	type Balance = u64;
	type OnFreeBalanceZero = ();
	type OnNewAccount = ();
	type Event = ();
	type TransactionPayment = ();
	type DustRemoval = ();
	type TransferPayment = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
	type TransactionBaseFee = TransactionBaseFee;
	type TransactionByteFee = TransactionByteFee;
}

pub struct ExtBuilder {
	transaction_base_fee: u64,
	transaction_byte_fee: u64,
	existential_deposit: u64,
	transfer_fee: u64,
	creation_fee: u64,
	monied: bool,
	vesting: bool,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			existential_deposit: 0,
			transfer_fee: 0,
			creation_fee: 0,
			monied: false,
			vesting: false,
		}
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	#[allow(dead_code)]
	pub fn transfer_fee(mut self, transfer_fee: u64) -> Self {
		self.transfer_fee = transfer_fee;
		self
	}
	pub fn creation_fee(mut self, creation_fee: u64) -> Self {
		self.creation_fee = creation_fee;
		self
	}
	pub fn transaction_fees(mut self, base_fee: u64, byte_fee: u64) -> Self {
		self.transaction_base_fee = base_fee;
		self.transaction_byte_fee = byte_fee;
		self
	}
	pub fn monied(mut self, monied: bool) -> Self {
		self.monied = monied;
		if self.existential_deposit == 0 {
			self.existential_deposit = 1;
		}
		self
	}
	pub fn vesting(mut self, vesting: bool) -> Self {
		self.vesting = vesting;
		self
	}
	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
		TRANSFER_FEE.with(|v| *v.borrow_mut() = self.transfer_fee);
		CREATION_FEE.with(|v| *v.borrow_mut() = self.creation_fee);
		TRANSACTION_BASE_FEE.with(|v| *v.borrow_mut() = self.transaction_base_fee);
		TRANSACTION_BYTE_FEE.with(|v| *v.borrow_mut() = self.transaction_byte_fee);
	}
	pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
		self.set_associated_consts();
		let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
		t.extend(GenesisConfig::<Runtime> {
			balances: if self.monied {
				vec![(1, 10 * self.existential_deposit), (2, 20 * self.existential_deposit), (3, 30 * self.existential_deposit), (4, 40 * self.existential_deposit)]
			} else {
				vec![]
			},
			vesting: if self.vesting && self.monied {
				vec![(1, 0, 10), (2, 10, 20)]
			} else {
				vec![]
			},
		}.build_storage().unwrap().0);
		t.into()
	}
}

pub type System = system::Module<Runtime>;
pub type Balances = Module<Runtime>;
