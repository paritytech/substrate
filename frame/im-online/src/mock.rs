// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::{Module, Trait};
use sp_runtime::Perbill;
use sp_staking::{SessionIndex, offence::{ReportOffence, OffenceError}};
use sp_runtime::testing::{Header, UintAuthorityId, TestXt};
use sp_runtime::traits::{IdentityLookup, BlakeTwo256, ConvertInto};
use sp_core::H256;
use frame_support::{impl_outer_origin, impl_outer_dispatch, parameter_types, weights::Weight};
use frame_system as system;
impl_outer_origin!{
	pub enum Origin for Runtime {}
}

impl_outer_dispatch! {
	pub enum Call for Runtime where origin: Origin {
		imonline::ImOnline,
	}
}

thread_local! {
	pub static VALIDATORS: RefCell<Option<Vec<u64>>> = RefCell::new(Some(vec![
		1,
		2,
		3,
	]));
}

pub struct TestSessionManager;
impl pallet_session::SessionManager<u64> for TestSessionManager {
	fn new_session(_new_index: SessionIndex) -> Option<Vec<u64>> {
		VALIDATORS.with(|l| l.borrow_mut().take())
	}
	fn end_session(_: SessionIndex) {}
	fn start_session(_: SessionIndex) {}
}

impl pallet_session::historical::SessionManager<u64, u64> for TestSessionManager {
	fn new_session(_new_index: SessionIndex) -> Option<Vec<(u64, u64)>> {
		VALIDATORS.with(|l| l
			.borrow_mut()
			.take()
			.map(|validators| {
				validators.iter().map(|v| (*v, *v)).collect()
			})
		)
	}
	fn end_session(_: SessionIndex) {}
	fn start_session(_: SessionIndex) {}
}

/// An extrinsic type used for tests.
pub type Extrinsic = TestXt<Call, ()>;
type IdentificationTuple = (u64, u64);
type Offence = crate::UnresponsivenessOffence<IdentificationTuple>;

thread_local! {
	pub static OFFENCES: RefCell<Vec<(Vec<u64>, Offence)>> = RefCell::new(vec![]);
}

/// A mock offence report handler.
pub struct OffenceHandler;
impl ReportOffence<u64, IdentificationTuple, Offence> for OffenceHandler {
	fn report_offence(reporters: Vec<u64>, offence: Offence) -> Result<(), OffenceError> {
		OFFENCES.with(|l| l.borrow_mut().push((reporters, offence)));
		Ok(())
	}
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	t.into()
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Runtime;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Trait for Runtime {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

parameter_types! {
	pub const Period: u64 = 1;
	pub const Offset: u64 = 0;
}

parameter_types! {
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(33);
}

impl pallet_session::Trait for Runtime {
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Runtime, TestSessionManager>;
	type SessionHandler = (ImOnline, );
	type ValidatorId = u64;
	type ValidatorIdOf = ConvertInto;
	type Keys = UintAuthorityId;
	type Event = ();
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
}

impl pallet_session::historical::Trait for Runtime {
	type FullIdentification = u64;
	type FullIdentificationOf = ConvertInto;
}

parameter_types! {
	pub const UncleGenerations: u32 = 5;
}

impl pallet_authorship::Trait for Runtime {
	type FindAuthor = ();
	type UncleGenerations = UncleGenerations;
	type FilterUncle = ();
	type EventHandler = ImOnline;
}

parameter_types! {
	pub const UnsignedPriority: u64 = 1 << 20;
}

impl Trait for Runtime {
	type AuthorityId = UintAuthorityId;
	type Event = ();
	type ReportUnresponsiveness = OffenceHandler;
	type SessionDuration = Period;
	type UnsignedPriority = UnsignedPriority;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

/// Im Online module.
pub type ImOnline = Module<Runtime>;
pub type System = frame_system::Module<Runtime>;
pub type Session = pallet_session::Module<Runtime>;

pub fn advance_session() {
	let now = System::block_number().max(1);
	System::set_block_number(now + 1);
	Session::rotate_session();
	let keys = Session::validators().into_iter().map(UintAuthorityId).collect();
	ImOnline::set_keys(keys);
	assert_eq!(Session::current_index(), (now / Period::get()) as u32);
}
