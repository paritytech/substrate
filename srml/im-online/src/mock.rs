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

//! Test utilities

#![cfg(test)]

use std::cell::RefCell;

use crate::{Module, Trait};
use sr_primitives::Perbill;
use sr_staking_primitives::{SessionIndex, offence::ReportOffence};
use sr_primitives::testing::{Header, UintAuthorityId, TestXt};
use sr_primitives::traits::{IdentityLookup, BlakeTwo256, ConvertInto};
use primitives::{H256, Blake2Hasher};
use support::{impl_outer_origin, impl_outer_dispatch, parameter_types};
use {runtime_io, system};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

impl_outer_dispatch! {
	pub enum Call for Runtime where origin: Origin {
		imonline::ImOnline,
	}
}

thread_local! {
	pub static VALIDATORS: RefCell<Option<Vec<u64>>> = RefCell::new(Some(vec![1, 2, 3]));
}

pub struct TestOnSessionEnding;
impl session::OnSessionEnding<u64> for TestOnSessionEnding {
	fn on_session_ending(_ending_index: SessionIndex, _will_apply_at: SessionIndex)
		-> Option<Vec<u64>>
	{
		VALIDATORS.with(|l| l.borrow_mut().take())
	}
}

impl session::historical::OnSessionEnding<u64, u64> for TestOnSessionEnding {
	fn on_session_ending(_ending_index: SessionIndex, _will_apply_at: SessionIndex)
		-> Option<(Vec<u64>, Vec<(u64, u64)>)>
	{
		VALIDATORS.with(|l| l
			.borrow_mut()
			.take()
			.map(|validators| {
				let full_identification = validators.iter().map(|v| (*v, *v)).collect();
				(validators, full_identification)
			})
		)
	}
}

/// An extrinsic type used for tests.
pub type Extrinsic = TestXt<Call, ()>;
type SubmitTransaction = system::offchain::TransactionSubmitter<(), Call, Extrinsic>;
type IdentificationTuple = (u64, u64);
type Offence = crate::UnresponsivenessOffence<IdentificationTuple>;

thread_local! {
	pub static OFFENCES: RefCell<Vec<(Vec<u64>, Offence)>> = RefCell::new(vec![]);
}

/// A mock offence report handler.
pub struct OffenceHandler;
impl ReportOffence<u64, IdentificationTuple, Offence> for OffenceHandler {
	fn report_offence(reporters: Vec<u64>, offence: Offence) {
		OFFENCES.with(|l| l.borrow_mut().push((reporters, offence)));
	}
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	let t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	t.into()
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Runtime;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl system::Trait for Runtime {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
}

parameter_types! {
	pub const Period: u64 = 1;
	pub const Offset: u64 = 0;
}

parameter_types! {
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(33);
}

impl session::Trait for Runtime {
	type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
	type OnSessionEnding = session::historical::NoteHistoricalRoot<Runtime, TestOnSessionEnding>;
	type SessionHandler = (ImOnline, );
	type ValidatorId = u64;
	type ValidatorIdOf = ConvertInto;
	type Keys = UintAuthorityId;
	type Event = ();
	type SelectInitialValidators = ();
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
}

impl session::historical::Trait for Runtime {
	type FullIdentification = u64;
	type FullIdentificationOf = ConvertInto;
}

impl Trait for Runtime {
	type AuthorityId = UintAuthorityId;
	type Event = ();
	type Call = Call;
	type SubmitTransaction = SubmitTransaction;
	type ReportUnresponsiveness = OffenceHandler;
}

/// Im Online module.
pub type ImOnline = Module<Runtime>;
pub type System = system::Module<Runtime>;
pub type Session = session::Module<Runtime>;

pub fn advance_session() {
	let now = System::block_number();
	System::set_block_number(now + 1);
	Session::rotate_session();
	assert_eq!(Session::current_index(), (now / Period::get()) as u32);
}
