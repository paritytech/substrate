// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Test utilities

#![cfg(test)]

use primitives::{BuildStorage, traits::IdentityLookup, testing::{Digest, DigestItem, Header}};
use primitives::generic::DigestItem as GenDigestItem;
use runtime_io;
use srml_support::{impl_outer_origin, impl_outer_event};
use substrate_primitives::{H256, Blake2Hasher};
use parity_codec::{Encode, Decode};
use crate::{GenesisConfig, Trait, Module, RawLog};

impl_outer_origin!{
	pub enum Origin for Test {}
}

impl From<RawLog<u64, u64>> for DigestItem {
	fn from(log: RawLog<u64, u64>) -> DigestItem {
		GenDigestItem::Other(log.encode())
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug, Decode, Encode)]
pub struct Test;
impl Trait for Test {
	type Log = DigestItem;
	type SessionKey = u64;
	type Event = TestEvent;
}
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type Log = DigestItem;
}

mod grandpa {
	pub use crate::Event;
}

impl_outer_event!{
	pub enum TestEvent for Test {
		grandpa<T>,
	}
}

pub fn new_test_ext(authorities: Vec<(u64, u64)>) -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
	t.extend(GenesisConfig::<Test> {
		authorities,
	}.build_storage().unwrap().0);
	t.into()
}

pub type System = system::Module<Test>;
pub type Grandpa = Module<Test>;
