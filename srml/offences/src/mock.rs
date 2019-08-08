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
use sr_primitives::Perbill;
use sr_staking_primitives::offence::{self, OffenceDetails, TimeSlot};
use sr_primitives::testing::Header;
use sr_primitives::traits::{IdentityLookup, BlakeTwo256};
use substrate_primitives::{H256, Blake2Hasher};
use support::{impl_outer_origin, parameter_types};
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

pub fn with_on_offence_perbill<R, F: FnOnce(&mut Vec<Perbill>) -> R>(f: F) -> R {
	// Feel free to rename this to _mut and add a version that makes `borrow` if required.
	ON_OFFENCE_PERBILL.with(|on_offence_perbill| {
		f(&mut *on_offence_perbill.borrow_mut())
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
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
}

impl Trait for Runtime {
	type IdentificationTuple = u64;
	type OnOffenceHandler = OnOffenceHandler;
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	let t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
	t.into()
}

/// Offences module.
pub type Offences = Module<Runtime>;

pub const KIND: [u8; 16] = *b"test_report_1234";

#[derive(Clone)]
pub struct Offence<T> {
	pub validators_count: u32,
	pub session_index: u32,
	pub offenders: Vec<T>,
	pub time_slot: TimeSlot,
}

impl<T: Clone> offence::Offence<T> for Offence<T> {
	const ID: offence::Kind = KIND;

	fn offenders(&self) -> Vec<T> {
		self.offenders.clone()
	}

	fn session_index(&self) -> u32 {
		self.session_index
	}

	fn validators_count(&self) -> u32 {
		self.validators_count
	}

	fn time_slot(&self) -> TimeSlot {
		self.time_slot
	}

	fn slash_fraction(
		offenders_count: u32,
		validators_count: u32,
	) -> Perbill {
		Perbill::from_percent(5 + offenders_count * 100 / validators_count)
	}
}
