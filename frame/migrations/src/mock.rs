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

use crate::{mock_helpers::*, Event, Historic};

use core::cell::RefCell;
#[use_attr]
use frame_support::derive_impl;
use frame_support::{
	macro_magic::use_attr,
	migrations::*,
	traits::{OnFinalize, OnInitialize},
	weights::Weight,
};
use frame_system::EventRecord;
use sp_core::{Get, H256};

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

frame_support::parameter_types! {
	pub const ServiceWeight: Weight = Weight::MAX.div(10);
}

thread_local! {
	/// The configs for the migrations to run.
	pub static MIGRATIONS: RefCell<Vec<(MockedMigrationKind, u32)>> = RefCell::new(vec![]);
}

/// Dynamically set the migrations to run.
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
					Box::new(MockedMigration(k, v))
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

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Migrations = MigrationsStorage;
	type Cursor = MockedCursor;
	type Identifier = MockedIdentifier;
	type OnMigrationUpdate = MockedOnMigrationUpdate;
	type ServiceWeight = ServiceWeight;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	sp_tracing::try_init_simple();
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

/// Run this closure in test externalities.
pub fn test_closure<R>(f: impl FnOnce() -> R) -> R {
	let mut ext = new_test_ext();
	ext.execute_with(f)
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
	pretty_assertions::assert_eq!(events.into_records(), System::events());
	System::reset_events();
}

frame_support::parameter_types! {
	/// The number of started upgrades.
	pub static UpgradesStarted: u32 = 0;
	/// The number of completed upgrades.
	pub static UpgradesCompleted: u32 = 0;
	/// The migrations that failed.
	pub static UpgradesFailed: Vec<Option<u32>> = vec![];
	/// Return value of `MockedOnMigrationUpdate::failed`.
	pub static FailedUpgradeResponse: FailedUpgradeHandling = FailedUpgradeHandling::KeepStuck;
}

pub struct MockedOnMigrationUpdate;
impl OnMigrationUpdate for MockedOnMigrationUpdate {
	fn started() {
		log::info!("OnMigrationUpdate started");
		UpgradesStarted::mutate(|v| *v += 1);
	}

	fn completed() {
		log::info!("OnMigrationUpdate completed");
		UpgradesCompleted::mutate(|v| *v += 1);
	}

	fn failed(migration: Option<u32>) -> FailedUpgradeHandling {
		UpgradesFailed::mutate(|v| v.push(migration));
		let res = FailedUpgradeResponse::get();
		log::error!("OnMigrationUpdate failed at: {migration:?}, handling as {res:?}");
		res
	}
}

/// Returns the number of `(started, completed, failed)` upgrades and resets their numbers.
pub fn upgrades_started_completed_failed() -> (u32, u32, u32) {
	(UpgradesStarted::take(), UpgradesCompleted::take(), UpgradesFailed::take().len() as u32)
}

pub fn historic() -> Vec<MockedIdentifier> {
	let mut historic = Historic::<Test>::iter_keys().collect::<Vec<_>>();
	historic.sort();
	historic
}
