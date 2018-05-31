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


use primitives::BuildExternalities;
use primitives::traits::{HasPublicAux, Identity};
use primitives::testing::{Digest, Header};
use substrate_primitives::H256;
use runtime_io;
use {DummyContractAddressFor, GenesisConfig, Module, Trait, consensus, session, system};

pub struct Test;
impl HasPublicAux for Test {
	type PublicAux = u64;
}
impl consensus::Trait for Test {
	type PublicAux = <Self as HasPublicAux>::PublicAux;
	type SessionKey = u64;
}
impl system::Trait for Test {
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = runtime_io::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
}
impl session::Trait for Test {
	type ConvertAccountIdToSessionKey = Identity;
}
impl Trait for Test {
	type Balance = u64;
	type DetermineContractAddress = DummyContractAddressFor;
}

pub fn new_test_ext(session_length: u64, sessions_per_era: u64, current_era: u64, monied: bool) -> runtime_io::TestExternalities {
	let mut t = system::GenesisConfig::<Test>::default().build_externalities();
	t.extend(consensus::GenesisConfig::<Test>{
		code: vec![],
		authorities: vec![],
	}.build_externalities());
	t.extend(session::GenesisConfig::<Test>{
		session_length,
		validators: vec![10, 20],
	}.build_externalities());
	t.extend(GenesisConfig::<Test>{
		sessions_per_era,
		current_era,
		balances: if monied { vec![(1, 10), (2, 20), (3, 30), (4, 40)] } else { vec![] },
		intentions: vec![],
		validator_count: 2,
		bonding_duration: 3,
		transaction_base_fee: 0,
		transaction_byte_fee: 0,
	}.build_externalities());
	t
}

pub type System = system::Module<Test>;
pub type Session = session::Module<Test>;
pub type Staking = Module<Test>;
