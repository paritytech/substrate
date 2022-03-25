// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Mock helpers for Session.

use super::*;
use crate as pallet_session;
#[cfg(feature = "historical")]
use crate::historical as pallet_session_historical;

use std::{cell::RefCell, collections::BTreeMap};

use sp_core::{crypto::key_types::DUMMY, H256};
use sp_runtime::{
	impl_opaque_keys,
	testing::{Header, UintAuthorityId},
	traits::{BlakeTwo256, IdentityLookup},
};
use sp_staking::SessionIndex;

use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64, GenesisBuild},
	BasicExternalities,
};

impl_opaque_keys! {
	pub struct MockSessionKeys {
		pub dummy: UintAuthorityId,
	}
}

impl From<UintAuthorityId> for MockSessionKeys {
	fn from(dummy: UintAuthorityId) -> Self {
		Self { dummy }
	}
}

pub const KEY_ID_A: KeyTypeId = KeyTypeId([4; 4]);
pub const KEY_ID_B: KeyTypeId = KeyTypeId([9; 4]);

#[derive(Debug, Clone, codec::Encode, codec::Decode, PartialEq, Eq)]
pub struct PreUpgradeMockSessionKeys {
	pub a: [u8; 32],
	pub b: [u8; 64],
}

impl OpaqueKeys for PreUpgradeMockSessionKeys {
	type KeyTypeIdProviders = ();

	fn key_ids() -> &'static [KeyTypeId] {
		&[KEY_ID_A, KEY_ID_B]
	}

	fn get_raw(&self, i: KeyTypeId) -> &[u8] {
		match i {
			i if i == KEY_ID_A => &self.a[..],
			i if i == KEY_ID_B => &self.b[..],
			_ => &[],
		}
	}
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

#[cfg(feature = "historical")]
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
		Historical: pallet_session_historical::{Pallet},
	}
);

#[cfg(not(feature = "historical"))]
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
	}
);

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
	pub static VALIDATOR_ACCOUNTS: RefCell<BTreeMap<u64, u64>> = RefCell::new(BTreeMap::new());
}

pub struct TestShouldEndSession;
impl ShouldEndSession<u64> for TestShouldEndSession {
	fn should_end_session(now: u64) -> bool {
		let l = SESSION_LENGTH.with(|l| *l.borrow());
		now % l == 0 ||
			FORCE_SESSION_END.with(|l| {
				let r = *l.borrow();
				*l.borrow_mut() = false;
				r
			})
	}
}

pub struct TestSessionHandler;
impl SessionHandler<u64> for TestSessionHandler {
	const KEY_TYPE_IDS: &'static [sp_runtime::KeyTypeId] = &[UintAuthorityId::ID];
	fn on_genesis_session<T: OpaqueKeys>(_validators: &[(u64, T)]) {}
	fn on_new_session<T: OpaqueKeys>(
		changed: bool,
		validators: &[(u64, T)],
		_queued_validators: &[(u64, T)],
	) {
		SESSION_CHANGED.with(|l| *l.borrow_mut() = changed);
		AUTHORITIES.with(|l| {
			*l.borrow_mut() = validators
				.iter()
				.map(|(_, id)| id.get::<UintAuthorityId>(DUMMY).unwrap_or_default())
				.collect()
		});
	}
	fn on_disabled(_validator_index: u32) {
		DISABLED.with(|l| *l.borrow_mut() = true)
	}
	fn on_before_session_ending() {
		BEFORE_SESSION_END_CALLED.with(|b| *b.borrow_mut() = true);
	}
}

pub struct TestSessionManager;
impl SessionManager<u64> for TestSessionManager {
	fn end_session(_: SessionIndex) {}
	fn start_session(_: SessionIndex) {}
	fn new_session(_: SessionIndex) -> Option<Vec<u64>> {
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
impl crate::historical::SessionManager<u64, u64> for TestSessionManager {
	fn end_session(_: SessionIndex) {}
	fn start_session(_: SessionIndex) {}
	fn new_session(new_index: SessionIndex) -> Option<Vec<(u64, u64)>> {
		<Self as SessionManager<_>>::new_session(new_index)
			.map(|vals| vals.into_iter().map(|val| (val, val)).collect())
	}
}

pub fn authorities() -> Vec<UintAuthorityId> {
	AUTHORITIES.with(|l| l.borrow().to_vec())
}

pub fn force_new_session() {
	FORCE_SESSION_END.with(|l| *l.borrow_mut() = true)
}

pub fn set_session_length(x: u64) {
	SESSION_LENGTH.with(|l| *l.borrow_mut() = x)
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

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let keys: Vec<_> = NEXT_VALIDATORS
		.with(|l| l.borrow().iter().cloned().map(|i| (i, i, UintAuthorityId(i).into())).collect());
	BasicExternalities::execute_with_storage(&mut t, || {
		for (ref k, ..) in &keys {
			frame_system::Pallet::<Test>::inc_providers(k);
		}
		frame_system::Pallet::<Test>::inc_providers(&4);
		// An additional identity that we use.
		frame_system::Pallet::<Test>::inc_providers(&69);
	});
	pallet_session::GenesisConfig::<Test> { keys }
		.assimilate_storage(&mut t)
		.unwrap();
	NEXT_VALIDATORS.with(|l| {
		let v = l.borrow().iter().map(|&i| (i, i)).collect();
		VALIDATOR_ACCOUNTS.with(|m| *m.borrow_mut() = v);
	});
	sp_io::TestExternalities::new(t)
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<5>;
	type WeightInfo = ();
}

pub struct TestValidatorIdOf;
impl TestValidatorIdOf {
	pub fn set(v: BTreeMap<u64, u64>) {
		VALIDATOR_ACCOUNTS.with(|m| *m.borrow_mut() = v);
	}
}
impl Convert<u64, Option<u64>> for TestValidatorIdOf {
	fn convert(x: u64) -> Option<u64> {
		VALIDATOR_ACCOUNTS.with(|m| m.borrow().get(&x).cloned())
	}
}

impl Config for Test {
	type ShouldEndSession = TestShouldEndSession;
	#[cfg(feature = "historical")]
	type SessionManager = crate::historical::NoteHistoricalRoot<Test, TestSessionManager>;
	#[cfg(not(feature = "historical"))]
	type SessionManager = TestSessionManager;
	type SessionHandler = TestSessionHandler;
	type ValidatorId = u64;
	type ValidatorIdOf = TestValidatorIdOf;
	type Keys = MockSessionKeys;
	type Event = Event;
	type NextSessionRotation = ();
	type WeightInfo = ();
}

#[cfg(feature = "historical")]
impl crate::historical::Config for Test {
	type FullIdentification = u64;
	type FullIdentificationOf = sp_runtime::traits::ConvertInto;
}
