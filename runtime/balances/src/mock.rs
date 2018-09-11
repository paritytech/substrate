// Copyright 2018 Parity Technologies (UK) Ltd.
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
use primitives::testing::{Digest, Header};
use substrate_primitives::{H256, Blake2Hasher};
use runtime_io;
use {GenesisConfig, Module, Trait, system};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Runtime;
impl system::Trait for Runtime {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
	type Event = ();
}
impl Trait for Runtime {
	type Balance = u64;
	type AccountIndex = u64;
	type OnFreeBalanceZero = ();
	type EnsureAccountLiquid = ();
	type Event = ();
}

pub fn new_test_ext(ext_deposit: u64, monied: bool) -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap();
	let balance_factor = if ext_deposit > 0 {
		256
	} else {
		1
	};
	t.extend(GenesisConfig::<Runtime>{
		balances: if monied {
			vec![(1, 10 * balance_factor), (2, 20 * balance_factor), (3, 30 * balance_factor), (4, 40 * balance_factor)]
		} else {
			vec![(10, balance_factor), (20, balance_factor)]
		},
		transaction_base_fee: 0,
		transaction_byte_fee: 0,
		existential_deposit: ext_deposit,
		transfer_fee: 0,
		creation_fee: 0,
		reclaim_rebate: 0,
	}.build_storage().unwrap());
	t.into()
}

pub type System = system::Module<Runtime>;
pub type Balances = Module<Runtime>;
