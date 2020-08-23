// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! Test utilities

#![cfg(test)]

use std::cell::RefCell;
use crate::{Module, Trait};
use codec::Encode;
use sp_runtime::Perbill;
use sp_staking::{
	SessionIndex,
	offence::{self, Kind, OffenceDetails},
};
use sp_runtime::testing::Header;
use sp_runtime::traits::{IdentityLookup, BlakeTwo256};
use sp_core::H256;
use frame_support::{
	impl_outer_origin, impl_outer_event, parameter_types, StorageMap, StorageDoubleMap,
	weights::{Weight, constants::{WEIGHT_PER_SECOND, RocksDbWeight}},
};
use frame_system as system;

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

pub struct OnOffenceHandler;

thread_local! {
	pub static ON_OFFENCE_PERBILL: RefCell<Vec<Perbill>> = RefCell::new(Default::default());
	pub static CAN_REPORT: RefCell<bool> = RefCell::new(true);
	pub static OFFENCE_WEIGHT: RefCell<Weight> = RefCell::new(Default::default());
}

impl<Reporter, Offender>
	offence::OnOffenceHandler<Reporter, Offender, Weight> for OnOffenceHandler
{
	fn on_offence(
		_offenders: &[OffenceDetails<Reporter, Offender>],
		slash_fraction: &[Perbill],
		_offence_session: SessionIndex,
	) -> Result<Weight, ()> {
		if <Self as offence::OnOffenceHandler<Reporter, Offender, Weight>>::can_report() {
			ON_OFFENCE_PERBILL.with(|f| {
				*f.borrow_mut() = slash_fraction.to_vec();
			});

			Ok(OFFENCE_WEIGHT.with(|w| *w.borrow()))
		} else {
			Err(())
		}
	}

	fn can_report() -> bool {
		CAN_REPORT.with(|c| *c.borrow())
	}
}

pub fn set_can_report(can_report: bool) {
	CAN_REPORT.with(|c| *c.borrow_mut() = can_report);
}

pub fn with_on_offence_fractions<R, F: FnOnce(&mut Vec<Perbill>) -> R>(f: F) -> R {
	ON_OFFENCE_PERBILL.with(|fractions| {
		f(&mut *fractions.borrow_mut())
	})
}

pub fn set_offence_weight(new: Weight) {
	OFFENCE_WEIGHT.with(|w| *w.borrow_mut() = new);
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Runtime;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 2 * WEIGHT_PER_SECOND;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Runtime {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = RocksDbWeight;
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

parameter_types! {
	pub OffencesWeightSoftLimit: Weight = Perbill::from_percent(60) * MaximumBlockWeight::get();
}

impl Trait for Runtime {
	type Event = TestEvent;
	type IdentificationTuple = u64;
	type OnOffenceHandler = OnOffenceHandler;
	type WeightSoftLimit = OffencesWeightSoftLimit;
	type WeightInfo = ();
}

mod offences {
	pub use crate::Event;
}

impl_outer_event! {
	pub enum TestEvent for Runtime {
		system<T>,
		offences,
	}
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

/// Offences module.
pub type Offences = Module<Runtime>;
pub type System = frame_system::Module<Runtime>;

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
		1
	}

	fn slash_fraction(
		offenders_count: u32,
		validator_set_count: u32,
	) -> Perbill {
		Perbill::from_percent(5 + offenders_count * 100 / validator_set_count)
	}
}
