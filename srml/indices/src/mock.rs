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

use std::collections::HashSet;
use ref_thread_local::{ref_thread_local, RefThreadLocal};
use primitives::BuildStorage;
use primitives::testing::{Digest, DigestItem, Header};
use substrate_primitives::{H256, Blake2Hasher};
use srml_support::impl_outer_origin;
use {runtime_io, system};
use crate::{GenesisConfig, Module, Trait, IsDeadAccount, OnNewAccount, ResolveHint};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

ref_thread_local! {
	static managed ALIVE: HashSet<u64> = HashSet::new();
}

pub fn make_account(who: u64) {
	ALIVE.borrow_mut().insert(who);
	Indices::on_new_account(&who);
}

pub fn kill_account(who: u64) {
	ALIVE.borrow_mut().remove(&who);
}

pub struct TestIsDeadAccount {}
impl IsDeadAccount<u64> for TestIsDeadAccount {
	fn is_dead_account(who: &u64) -> bool {
		!ALIVE.borrow_mut().contains(who)
	}
}

pub struct TestResolveHint;
impl ResolveHint<u64, u64> for TestResolveHint {
	fn resolve_hint(who: &u64) -> Option<u64> {
		if *who < 256 {
			None
		} else {
			Some(*who - 256)
		}
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
	type Lookup = Indices;
	type Header = Header;
	type Event = ();
	type Log = DigestItem;
}
impl Trait for Runtime {
	type AccountIndex = u64;
	type IsDeadAccount = TestIsDeadAccount;
	type ResolveHint = TestResolveHint;
	type Event = ();
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	{
		let mut h = ALIVE.borrow_mut();
		h.clear();
		for i in 1..5 { h.insert(i); }
	}

	let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
	t.extend(GenesisConfig::<Runtime> {
		ids: vec![1, 2, 3, 4]
	}.build_storage().unwrap().0);
	t.into()
}

pub type Indices = Module<Runtime>;
