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

use crate::{mock::*, mock::MockedMigrationKind::*, Event, Historic};
use frame_support::traits::OnRuntimeUpgrade;
use sp_core::H256;
use frame_system::EventRecord;

/// Example output:
///
/// ```pre
/// Suspend    
/// MockedMigrate: Step 1/2    
/// MockedMigrate: Step 2/2    
/// MockedMigrate: Succeeded after 2 steps    
/// MockedMigrate: Step 1/3    
/// MockedMigrate: Step 2/3    
/// MockedMigrate: Step 3/3    
/// MockedMigrate: Succeeded after 3 steps    
/// Resume
/// ```
#[test]
fn basic_works() {
	new_test_ext().execute_with(|| {
		MIGRATIONS.with(|migrations| {
			*migrations.borrow_mut() = vec![
				(SucceedAfter, 0),
				(SucceedAfter, 1),
				(SucceedAfter, 2),
			];
		});

		System::set_block_number(1);
		Migrations::on_runtime_upgrade();

		run_to_block(10);

		// Just three, since two were added twice.
		assert_eq!(Historic::<Test>::iter().count(), 3);
		dbg!(System::events());
		assert_eq!(System::events(), vec![
			Event::UpgradeStarted.into_record(),

			Event::MigrationCompleted { index: 0, took: 0 }.into_record(),

			Event::MigrationAdvanced { index: 1, step: 0 }.into_record(),
			Event::MigrationCompleted { index: 1, took: 1 }.into_record(),
			
			Event::MigrationAdvanced { index: 2, step: 0 }.into_record(),
			Event::MigrationAdvanced { index: 2, step: 1 }.into_record(),
			Event::MigrationCompleted { index: 2, took: 2 }.into_record(),
			
			Event::UpgradeCompleted { migrations: 3 }.into_record(),
		]);
	});
}

#[test]
fn historic_skipping_works() {
	new_test_ext().execute_with(|| {
		MIGRATIONS.with(|migrations| {
			*migrations.borrow_mut() = vec![
				(SucceedAfter, 0),
				(SucceedAfter, 0), // Will be skipped
				(SucceedAfter, 1),
				(SucceedAfter, 2),
				(SucceedAfter, 1), // Will be skipped
			];
		});

		System::set_block_number(1);
		Migrations::on_runtime_upgrade();

		run_to_block(10);

		// Just three, since two were added twice.
		assert_eq!(Historic::<Test>::iter().count(), 3);
		assert_eq!(System::events(), vec![
			Event::UpgradeStarted.into_record(),

			Event::MigrationCompleted { index: 0, took: 0 }.into_record(),
			
			Event::MigrationSkippedHistoric { index: 1 }.into_record(),
			
			Event::MigrationAdvanced { index: 2, step: 0 }.into_record(),
			Event::MigrationCompleted { index: 2, took: 1 }.into_record(),
			
			Event::MigrationAdvanced { index: 3, step: 0 }.into_record(),
			Event::MigrationAdvanced { index: 3, step: 1 }.into_record(),
			Event::MigrationCompleted { index: 3, took: 2 }.into_record(),

			Event::MigrationSkippedHistoric { index: 4 }.into_record(),
			
			Event::UpgradeCompleted { migrations: 5 }.into_record(),
		]);
	});
}

trait IntoRecord {
	fn into_record(self) -> EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256>;
}

impl IntoRecord for Event<Test> {
	fn into_record(self) -> EventRecord<<Test as frame_system::Config>::RuntimeEvent, H256> {
		let re: <Test as frame_system::Config>::RuntimeEvent = self.into();
		EventRecord {
			phase: frame_system::Phase::Initialization,
			event: re,
			topics: vec![],
		}
	}
}
