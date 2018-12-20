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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use double_map::StorageDoubleMap;
use runtime_io::with_externalities;
use runtime_primitives::testing::{Digest, DigestItem, H256, Header};
use runtime_primitives::traits::{BlakeTwo256};
use runtime_primitives::BuildStorage;
use runtime_support::StorageMap;
use substrate_primitives::{Blake2Hasher};
use system::{Phase, EventRecord};
use wabt;
use {
	runtime_io, balances, system, ContractAddressFor,
	GenesisConfig, Module, StorageOf, Trait, RawEvent,
};

impl_outer_origin! {
	pub enum Origin for Test {}
}

mod contract {
	pub use super::super::*;
}
impl_outer_event! {
	pub enum MetaEvent for Test {
		balances<T>, contract<T>,
	}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
	type Event = MetaEvent;
	type Log = DigestItem;
}
impl balances::Trait for Test {
	type Balance = u64;
	type AccountIndex = u64;
	type OnFreeBalanceZero = Contract;
	type EnsureAccountLiquid = ();
	type Event = MetaEvent;
}
impl Trait for Test {
	type Gas = u64;
	type DetermineContractAddress = DummyContractAddressFor;
	type Event = MetaEvent;
}

type Balances = balances::Module<Test>;
type Contract = Module<Test>;
type System = system::Module<Test>;

pub struct DummyContractAddressFor;
impl ContractAddressFor<H256, u64> for DummyContractAddressFor {
	fn contract_address_for(code_hash: &H256, data: &[u8], origin: &u64) -> u64 {
		panic!()
	}
}
