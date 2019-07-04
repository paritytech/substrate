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

use primitives::{
	BuildStorage, DigestItem, traits::IdentityLookup, testing::{Header, UintAuthorityId}
};
use runtime_io;
use srml_support::{impl_outer_origin, impl_outer_event};
use substrate_primitives::{H256, Blake2Hasher};
use parity_codec::{Encode, Decode};
use crate::{AuthorityId, GenesisConfig, Trait, Module, Signal};
use substrate_finality_grandpa_primitives::GRANDPA_ENGINE_ID;

impl_outer_origin!{
	pub enum Origin for Test {}
}

impl From<Signal<u64>> for DigestItem<H256> {
	fn from(log: Signal<u64>) -> DigestItem<H256> {
		DigestItem::Consensus(GRANDPA_ENGINE_ID, log.encode())
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug, Decode, Encode)]
pub struct Test;
impl Trait for Test {
	type Event = TestEvent;

}
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
}

mod grandpa {
	pub use crate::Event;
}

impl_outer_event!{
	pub enum TestEvent for Test {
		grandpa,
	}
}

pub fn to_authorities(vec: Vec<(u64, u64)>) -> Vec<(AuthorityId, u64)> {
	vec.into_iter().map(|(id, weight)| (UintAuthorityId(id).into(), weight)).collect()
}

pub fn new_test_ext(authorities: Vec<(u64, u64)>) -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
	t.extend(GenesisConfig::<Test> {
		_genesis_phantom_data: Default::default(),
		authorities: to_authorities(authorities),
	}.build_storage().unwrap().0);
	t.into()
}

pub type System = system::Module<Test>;
pub type Grandpa = Module<Test>;
