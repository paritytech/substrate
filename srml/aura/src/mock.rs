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

use std::cell::RefCell;
use core::marker::PhantomData;

use primitives::{
	KeyTypeId, BuildStorage, key_types,
	traits::{IdentityLookup, BlakeTwo256, ConvertInto, OpaqueKeys, Verify, Lazy},
	testing::{UINT_DUMMY_KEY, Header, UintAuthorityId}
};
use substrate_primitives::{H256, Blake2Hasher, sr25519};
use runtime_io;
use parity_codec::{Encode, Decode};
use srml_support::{impl_outer_origin, parameter_types};
use session::{ShouldEndSession, SessionHandler, OnSessionEnding, SessionIndex};
use crate::{Trait, Module, GenesisConfig};

#[derive(Encode, Decode, Clone, Eq, PartialEq, Debug)]
struct UintSignature(u64);

impl Verify for UintSignature {
	type Signer = UintAuthorityId;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		true
	}
}

impl_outer_origin!{
	pub enum Origin for Test {}
}

thread_local! {
	pub static NEXT_VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
	pub static AUTHORITIES: RefCell<Vec<UintAuthorityId>> =
		RefCell::new(vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
	pub static FORCE_SESSION_END: RefCell<bool> = RefCell::new(false);
	pub static SESSION_LENGTH: RefCell<u64> = RefCell::new(2);
	pub static SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
	pub static TEST_SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MinimumPeriod: u64 = 1;
}

pub struct TestShouldEndSession;
impl ShouldEndSession<u64> for TestShouldEndSession {
	fn should_end_session(now: u64) -> bool {
		let l = SESSION_LENGTH.with(|l| *l.borrow());
		now % l == 0 || FORCE_SESSION_END.with(|l| { let r = *l.borrow(); *l.borrow_mut() = false; r })
	}
}

pub struct TestSessionHandler;
impl SessionHandler<u64> for TestSessionHandler {
	fn on_new_session<T: OpaqueKeys>(changed: bool, validators: &[(u64, T)]) {
		SESSION_CHANGED.with(|l| *l.borrow_mut() = changed);
		AUTHORITIES.with(|l|
			*l.borrow_mut() = validators.iter().map(|(_, id)| id.get::<UintAuthorityId>(0).unwrap_or_default()).collect()
		);
	}
	fn on_disabled(_validator_index: usize) {}
}

pub struct TestOnSessionEnding;
impl OnSessionEnding<u64> for TestOnSessionEnding {
	fn on_session_ending(_: SessionIndex, _: SessionIndex) -> Option<Vec<u64>> {
		if !TEST_SESSION_CHANGED.with(|l| *l.borrow()) {
			Some(NEXT_VALIDATORS.with(|l| l.borrow().clone()))
		} else {
			None
		}
	}
}

impl crate::historical::OnSessionEnding<u64, u64> for TestOnSessionEnding {
	fn on_session_ending(_: SessionIndex, _: SessionIndex)
		-> Option<(Vec<u64>, Vec<(u64, u64)>)>
	{
		if !TEST_SESSION_CHANGED.with(|l| *l.borrow()) {
			let last_validators = Session::validators();
			let last_identifications = last_validators.into_iter().map(|v| (v, v)).collect();
			Some((NEXT_VALIDATORS.with(|l| l.borrow().clone()), last_identifications))
		} else {
			None
		}
	}
}

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = ();
	type BlockHashCount = BlockHashCount;
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = Aura;
	type MinimumPeriod = MinimumPeriod;
}

impl session::Trait for Test {
	type ShouldEndSession = TestShouldEndSession;
	type OnSessionEnding = session::historical::NoteHistoricalRoot<Test, TestOnSessionEnding>;
	type SessionHandler = TestSessionHandler;
	type ValidatorId = u64;
	type ValidatorIdOf = ConvertInto;
	type Keys = UintAuthorityId;
	type Event = ();
	type SelectInitialValidators = ();
}

impl session::historical::Trait for Test {
	type FullIdentification = u64;
	type FullIdentificationOf = primitives::traits::ConvertInto;
}

impl Trait for Test {
	type HandleReport = ();
	type AuthorityId = UintAuthorityId;
	type Signature = UintSignature;
	type KeyOwnerSystem = Historical;
}

pub fn new_test_ext(authorities: Vec<u64>) -> runtime_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap().0;
	t.extend(GenesisConfig::<Test>{
		authorities: authorities.into_iter().map(|a| UintAuthorityId(a)).collect(),
	}.build_storage().unwrap().0);
	t.into()
}

pub type System = system::Module<Test>;
pub type Aura = Module<Test>;
pub type Staking = staking::Module<Test>;
pub type Session = session::Module<Test>;
pub type Historical = session::historical::Module<Test>;