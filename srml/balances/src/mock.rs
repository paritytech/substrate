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

use primitives::BuildStorage;
use primitives::{
	weights::{MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT, Weight},
	traits::{IdentityLookup, Convert},
	testing::{Digest, DigestItem, Header},
	Perbill,
};
use substrate_primitives::{H256, Blake2Hasher};
use runtime_io;
use srml_support::impl_outer_origin;
use crate::{GenesisConfig, Module, Trait};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

pub struct DummyFeeHandler;

impl Convert<Weight, u64> for DummyFeeHandler {
	fn convert(weight: Weight) -> u64 {
		let billion = 1_000_000_000_u128;
		let from_max_to_per_bill = |x: u128| { x * billion /  MAX_TRANSACTIONS_WEIGHT as u128 };
		// temporary: weight < ideal
		let ideal = IDEAL_TRANSACTIONS_WEIGHT as u128; // aka IDEAL_TRANSACTION_WEIGHT/MAX_TRANSACTIONS_WEIGHT
		let mut positive = false;
		// for testing reasons, we set `all_extrinsics_weight()` equal to 0
		// - still tests the range of values allowed; all_extrinsics_weight() is tested in `srml/executive
		let all = weight as u128;
		let diff = match ideal.checked_sub(all) {
			Some(d) => d,
			None => { positive = true; all - ideal }
		};

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = 40_000;
		// 0.00004^2 = 16/10^10 ~= 2/10^9
		let v_squared = 2;

		let mut first_term = v * from_max_to_per_bill(diff as u128);
		first_term = first_term / billion;

		let mut second_term = v_squared * from_max_to_per_bill(diff as u128) * from_max_to_per_bill(diff as u128) / 2;
		second_term = second_term / billion;
		second_term = second_term / billion;

		let mut fee_multiplier = billion + second_term;
		fee_multiplier = if positive { fee_multiplier + first_term } else { fee_multiplier - first_term};

		let p = Perbill::from_parts(fee_multiplier.min(billion) as u32);
		let transaction_fee: u32 = p * weight;
		transaction_fee.into()
	}
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
	type Digest = Digest;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type Log = DigestItem;
}
impl Trait for Runtime {
	type Balance = u64;
	type WeightToFee = DummyFeeHandler;
	type OnFreeBalanceZero = ();
	type OnNewAccount = ();
	type Event = ();
	type TransactionPayment = ();
	type DustRemoval = ();
	type TransferPayment = ();
}

pub struct ExtBuilder {
	existential_deposit: u64,
	transfer_fee: u64,
	creation_fee: u64,
	monied: bool,
	vesting: bool,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
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
	pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
		t.extend(GenesisConfig::<Runtime> {
			balances: if self.monied {
				vec![(1, 10 * self.existential_deposit), (2, 20 * self.existential_deposit), (3, 30 * self.existential_deposit), (4, 40 * self.existential_deposit)]
			} else {
				vec![]
			},
			existential_deposit: self.existential_deposit,
			transfer_fee: self.transfer_fee,
			creation_fee: self.creation_fee,
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
