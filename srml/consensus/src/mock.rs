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

use primitives::{BuildStorage, testing::{Digest, DigestItem, Header}};
use runtime_io;
use substrate_primitives::{H256, Blake2Hasher};
use {GenesisConfig, Trait, Module, system};

impl_outer_origin!{
	pub enum Origin for Test {}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;
impl Trait for Test {
	const NOTE_OFFLINE_POSITION: u32 = 1;
	type Log = DigestItem;
	type SessionKey = u64;
	type OnOfflineValidator = ();
}
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
	type Event = ();
	type Log = DigestItem;
}

pub fn new_test_ext(authorities: Vec<u64>) -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
	t.extend(GenesisConfig::<Test>{
		code: vec![],
		authorities,
	}.build_storage().unwrap().0);
	t.into()
}

pub type System = system::Module<Test>;
pub type Consensus = Module<Test>;
