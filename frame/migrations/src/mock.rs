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

#![cfg(test)]

use crate::{Event, Historic};
use codec::{Decode, Encode};
use core::cell::RefCell;
#[use_attr]
use frame_support::derive_impl;
use frame_support::{
	macro_magic::use_attr,
	migrations::*,
	traits::{OnFinalize, OnInitialize},
	weights::{Weight, WeightMeter},
};
use frame_system::EventRecord;
use sp_core::{ConstU32, Get, H256};
use sp_runtime::BoundedVec;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Migrations: crate,
	}
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum MockedMigrationKind {
	SucceedAfter,
	FailAfter,
}
use MockedMigrationKind::*; // C style

pub struct MockedMigrate(MockedMigrationKind, u32);

impl SteppedMigration for MockedMigrate {
	type Cursor = BoundedVec<u8, ConstU32<1024>>;
	type Identifier = BoundedVec<u8, ConstU32<32>>;

	fn id(&self) -> Self::Identifier {
		mocked_id(self.0, self.1)
	}

	fn step(
		&self,
		cursor: &Option<Self::Cursor>,
		_meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		let mut count: u32 =
			cursor.as_ref().and_then(|c| Decode::decode(&mut &c[..]).ok()).unwrap_or(0);
		log::debug!("MockedMigrate: Step {}", count);
		if count != self.1 {
			count += 1;
			return Ok(Some(count.encode().try_into().unwrap()))
		}

		match self.0 {
			SucceedAfter => {
				log::debug!("MockedMigrate: Succeeded after {} steps", count);
				Ok(None)
			},
			FailAfter => {
				log::debug!("MockedMigrate: Failed after {} steps", count);
				Err(SteppedMigrationError::Failed)
			},
		}
	}
}

type MockedCursor = BoundedVec<u8, ConstU32<1024>>;
type MockedIdentifier = BoundedVec<u8, ConstU32<32>>;

frame_support::parameter_types! {
	pub const ServiceWeight: Weight = Weight::MAX;
}

thread_local! {
	pub static MIGRATIONS: RefCell<Vec<(MockedMigrationKind, u32)>> = RefCell::new(vec![]);
}

pub struct MigrationsStorage;
impl Get<Vec<Box<dyn SteppedMigration<Cursor = MockedCursor, Identifier = MockedIdentifier>>>>
	for MigrationsStorage
{
	fn get() -> Vec<Box<dyn SteppedMigration<Cursor = MockedCursor, Identifier = MockedIdentifier>>>
	{
		MIGRATIONS.with(|m| {
			m.borrow()
				.clone()
				.into_iter()
				.map(|(k, v)| {
					Box::new(MockedMigrate(k, v))
						as Box<
							dyn SteppedMigration<
								Cursor = MockedCursor,
								Identifier = MockedIdentifier,
							>,
						>
				})
				.collect()
		})
	}
}

impl MigrationsStorage {
	/// Set the migrations to run.
	pub fn set(migrations: Vec<(MockedMigrationKind, u32)>) {
		MIGRATIONS.with(|m| *m.borrow_mut() = migrations);
	}
}

pub fn mocked_id(kind: MockedMigrationKind, steps: u32) -> MockedIdentifier {
	format!("MockedMigrate({:?}, {})", kind, steps)
		.as_bytes()
		.to_vec()
		.try_into()
		.unwrap()
}

pub fn historic() -> Vec<MockedIdentifier> {
	let mut historic = Historic::<Test>::iter_keys().collect::<Vec<_>>();
	historic.sort();
	historic
}

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Migrations = MigrationsStorage;
	type Cursor = MockedCursor;
	type Identifier = MockedIdentifier;
	type ServiceWeight = ServiceWeight;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

/// Run this closure in test externalities.
pub fn test_closure<R>(f: impl FnOnce() -> R) -> R {
	let mut ext = new_test_ext();
	ext.execute_with(f)
}

pub struct LoggingSuspender<Inner>(core::marker::PhantomData<Inner>);
impl<Inner: ExtrinsicSuspenderQuery> ExtrinsicSuspenderQuery for LoggingSuspender<Inner> {
	fn is_suspended() -> bool {
		let res = Inner::is_suspended();
		log::debug!("IsSuspended: {res}");
		res
	}
}

pub fn run_to_block(n: u32) {
	while System::block_number() < n {
		if System::block_number() > 1 {
			Migrations::on_finalize(System::block_number());
			System::on_finalize(System::block_number());
		}
		log::debug!("Block {}", System::block_number());
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		Migrations::on_initialize(System::block_number());
	}
}

// Traits to make using events less insufferable:

pub trait IntoRecord {
	fn into_record(self) -> EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256>;
}

impl IntoRecord for Event<Test> {
	fn into_record(self) -> EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256> {
		let re: <Test as frame_system::Config>::RuntimeEvent = self.into();
		EventRecord { phase: frame_system::Phase::Initialization, event: re, topics: vec![] }
	}
}

pub trait IntoRecords {
	fn into_records(self) -> Vec<EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256>>;
}

impl<E: IntoRecord> IntoRecords for Vec<E> {
	fn into_records(self) -> Vec<EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256>> {
		self.into_iter().map(|e| e.into_record()).collect()
	}
}

pub fn assert_events<E: IntoRecord>(events: Vec<E>) {
	assert_eq!(System::events(), events.into_records());
	System::reset_events();
}
