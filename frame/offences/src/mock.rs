// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate as offences;
use crate::Config;
use codec::Encode;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
	weights::{constants::RocksDbWeight, Weight},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	Perbill,
};
use sp_staking::{
	offence::{self, DisableStrategy, Kind, OffenceDetails},
	SessionIndex,
};

pub struct OnOffenceHandler;

parameter_types! {
	pub static OnOffencePerbill: Vec<Perbill> = Default::default();
	pub static OffenceWeight: Weight = Default::default();
}

impl<Reporter, Offender> offence::OnOffenceHandler<Reporter, Offender, Weight>
	for OnOffenceHandler
{
	fn on_offence(
		_offenders: &[OffenceDetails<Reporter, Offender>],
		slash_fraction: &[Perbill],
		_offence_session: SessionIndex,
		_disable_strategy: DisableStrategy,
	) -> Weight {
		OnOffencePerbill::mutate(|f| {
			*f = slash_fraction.to_vec();
		});

		OffenceWeight::get()
	}
}

pub fn with_on_offence_fractions<R, F: FnOnce(&mut Vec<Perbill>) -> R>(f: F) -> R {
	OnOffencePerbill::mutate(|fractions| f(fractions))
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;

frame_support::construct_runtime!(
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Offences: offences::{Pallet, Storage, Event},
	}
);

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = RocksDbWeight;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
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

impl Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type IdentificationTuple = u64;
	type OnOffenceHandler = OnOffenceHandler;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

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
pub struct Offence {
	pub validator_set_count: u32,
	pub offenders: Vec<u64>,
	pub time_slot: u128,
}

impl offence::Offence<u64> for Offence {
	const ID: offence::Kind = KIND;
	type TimeSlot = u128;

	fn offenders(&self) -> Vec<u64> {
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

	fn slash_fraction(&self, offenders_count: u32) -> Perbill {
		Perbill::from_percent(5 + offenders_count * 100 / self.validator_set_count)
	}
}

/// Create the report id for the given `offender` and `time_slot` combination.
pub fn report_id(time_slot: u128, offender: u64) -> H256 {
	Offences::report_id::<Offence>(&time_slot, &offender)
}
