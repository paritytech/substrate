// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Mock helpers for Session.

use super::*;
use std::cell::RefCell;
use support::{impl_outer_origin, parameter_types};
use primitives::{crypto::key_types::DUMMY, H256};
use sr_primitives::{
	Perbill, impl_opaque_keys, traits::{BlakeTwo256, IdentityLookup, ConvertInto},
	testing::{Header, UintAuthorityId}
};
use sr_staking_primitives::SessionIndex;

impl_opaque_keys! {
	pub struct MockSessionKeys {
		#[id(DUMMY)]
		pub dummy: UintAuthorityId,
	}
}

impl From<UintAuthorityId> for MockSessionKeys {
	fn from(dummy: UintAuthorityId) -> Self {
		Self { dummy }
	}
}

impl_outer_origin! {
	pub enum Origin for Test {}
}

thread_local! {
	pub static VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
	pub static NEXT_VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
	pub static AUTHORITIES: RefCell<Vec<UintAuthorityId>> =
		RefCell::new(vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
	pub static FORCE_SESSION_END: RefCell<bool> = RefCell::new(false);
	pub static SESSION_LENGTH: RefCell<u64> = RefCell::new(2);
	pub static SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
	pub static TEST_SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
	pub static DISABLED: RefCell<bool> = RefCell::new(false);
	// Stores if `on_before_session_end` was called
	pub static BEFORE_SESSION_END_CALLED: RefCell<bool> = RefCell::new(false);
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
	fn on_genesis_session<T: OpaqueKeys>(_validators: &[(u64, T)]) {}
	fn on_new_session<T: OpaqueKeys>(
		changed: bool,
		validators: &[(u64, T)],
		_queued_validators: &[(u64, T)],
	) {
		SESSION_CHANGED.with(|l| *l.borrow_mut() = changed);
		AUTHORITIES.with(|l|
			*l.borrow_mut() = validators.iter()
				.map(|(_, id)| id.get::<UintAuthorityId>(DUMMY).unwrap_or_default())
				.collect()
		);
	}
	fn on_disabled(_validator_index: usize) {
		DISABLED.with(|l| *l.borrow_mut() = true)
	}
	fn on_before_session_ending() {
		BEFORE_SESSION_END_CALLED.with(|b| *b.borrow_mut() = true);
	}
}

pub struct TestOnSessionEnding;
impl OnSessionEnding<u64> for TestOnSessionEnding {
	fn on_session_ending(_: SessionIndex, _: SessionIndex) -> Option<Vec<u64>> {
		if !TEST_SESSION_CHANGED.with(|l| *l.borrow()) {
			VALIDATORS.with(|v| {
				let mut v = v.borrow_mut();
				*v = NEXT_VALIDATORS.with(|l| l.borrow().clone());
				Some(v.clone())
			})
		} else if DISABLED.with(|l| std::mem::replace(&mut *l.borrow_mut(), false)) {
			// If there was a disabled validator, underlying conditions have changed
			// so we return `Some`.
			Some(VALIDATORS.with(|v| v.borrow().clone()))
		} else {
			None
		}
	}
}

#[cfg(feature = "historical")]
impl crate::historical::OnSessionEnding<u64, u64> for TestOnSessionEnding {
	fn on_session_ending(ending_index: SessionIndex, will_apply_at: SessionIndex)
		-> Option<(Vec<u64>, Vec<(u64, u64)>)>
	{
		let pair_with_ids = |vals: &[u64]| vals.iter().map(|&v| (v, v)).collect::<Vec<_>>();
		<Self as OnSessionEnding<_>>::on_session_ending(ending_index, will_apply_at)
			.map(|vals| (pair_with_ids(&vals), vals))
			.map(|(ids, vals)| (vals, ids))
	}
}

pub fn authorities() -> Vec<UintAuthorityId> {
	AUTHORITIES.with(|l| l.borrow().to_vec())
}

pub fn force_new_session() {
	FORCE_SESSION_END.with(|l| *l.borrow_mut() = true )
}

pub fn set_session_length(x: u64) {
	SESSION_LENGTH.with(|l| *l.borrow_mut() = x )
}

pub fn session_changed() -> bool {
	SESSION_CHANGED.with(|l| *l.borrow())
}

pub fn set_next_validators(next: Vec<u64>) {
	NEXT_VALIDATORS.with(|v| *v.borrow_mut() = next);
}

pub fn before_session_end_called() -> bool {
	BEFORE_SESSION_END_CALLED.with(|b| *b.borrow())
}

pub fn reset_before_session_end_called() {
	BEFORE_SESSION_END_CALLED.with(|b| *b.borrow_mut() = false);
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const MinimumPeriod: u64 = 5;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
}

parameter_types! {
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(33);
}

impl Trait for Test {
	type ShouldEndSession = TestShouldEndSession;
	#[cfg(feature = "historical")]
	type OnSessionEnding = crate::historical::NoteHistoricalRoot<Test, TestOnSessionEnding>;
	#[cfg(not(feature = "historical"))]
	type OnSessionEnding = TestOnSessionEnding;
	type SessionHandler = TestSessionHandler;
	type ValidatorId = u64;
	type ValidatorIdOf = ConvertInto;
	type Keys = MockSessionKeys;
	type Event = ();
	type SelectInitialValidators = ();
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
}

#[cfg(feature = "historical")]
impl crate::historical::Trait for Test {
	type FullIdentification = u64;
	type FullIdentificationOf = sr_primitives::traits::ConvertInto;
}

pub type System = system::Module<Test>;
pub type Session = Module<Test>;
