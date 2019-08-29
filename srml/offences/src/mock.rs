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
use crate::{Module, Trait};
use codec::Encode;
use sr_primitives::Perbill;
use sr_staking_primitives::{
	SessionIndex,
	offence::{self, Kind, OffenceDetails},
};
use sr_primitives::testing::Header;
use sr_primitives::traits::{IdentityLookup, BlakeTwo256};
use substrate_primitives::{H256, Blake2Hasher};
use support::{impl_outer_origin, impl_outer_event, parameter_types, StorageMap, StorageDoubleMap};
use {runtime_io, system};

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

pub struct OnOffenceHandler;

thread_local! {
	pub static ON_OFFENCE_PERBILL: RefCell<Vec<Perbill>> = RefCell::new(Default::default());
}

impl<Reporter, Offender> offence::OnOffenceHandler<Reporter, Offender> for OnOffenceHandler {
	fn on_offence(
		_offenders: &[OffenceDetails<Reporter, Offender>],
		slash_fraction: &[Perbill],
	) {
		ON_OFFENCE_PERBILL.with(|f| {
			*f.borrow_mut() = slash_fraction.to_vec();
		});
	}
}

pub fn with_on_offence_fractions<R, F: FnOnce(&mut Vec<Perbill>) -> R>(f: F) -> R {
	ON_OFFENCE_PERBILL.with(|fractions| {
		f(&mut *fractions.borrow_mut())
	})
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
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
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
}

impl Trait for Runtime {
	type Event = TestEvent;
	type IdentificationTuple = u64;
	type OnOffenceHandler = OnOffenceHandler;
}

mod offences {
	pub use crate::Event;
}

impl_outer_event! {
	pub enum TestEvent for Runtime {
		offences,
	}
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	let t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	t.into()
}

/// Offences module.
pub type Offences = Module<Runtime>;
pub type System = system::Module<Runtime>;

pub const KIND: [u8; 16] = *b"test_report_1234";

/// Returns all offence details for the specific `kind` happened at the specific time slot.
pub fn offence_reports(kind: Kind, time_slot: u128) -> Vec<OffenceDetails<u64, u64>> {
	<crate::ConcurrentReportsIndex<Runtime>>::get(&kind, &time_slot.encode())
		.into_iter()
		.map(|report_id| {
			<crate::Reports<Runtime>>::get(&report_id)
				.expect("dangling report id is found in ConcurrentReportsIndex")
		})
		.collect()
}

#[derive(Clone)]
pub struct Offence<T> {
	pub validator_set_count: u32,
	pub offenders: Vec<T>,
	pub time_slot: u128,
}

impl<T: Clone> offence::Offence<T> for Offence<T> {
	const ID: offence::Kind = KIND;
	type TimeSlot = u128;

	fn offenders(&self) -> Vec<T> {
		self.offenders.clone()
	}

	fn validator_set_count(&self) -> u32 {
		self.validator_set_count
	}

	fn time_slot(&self) -> u128 {
		self.time_slot
	}

	fn session_index(&self) -> SessionIndex {
		// session index is not used by the srml-offences directly, but rather it exists only for
		// filtering historical reports.
		unimplemented!()
	}

	fn slash_fraction(
		offenders_count: u32,
		validator_set_count: u32,
	) -> Perbill {
		Perbill::from_percent(5 + offenders_count * 100 / validator_set_count)
	}
}
