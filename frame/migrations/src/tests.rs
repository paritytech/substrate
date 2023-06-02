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

use crate::{
	mock::{MockedMigrationKind::*, Test as T, *},
	Cursor, Event, MigrationCursor,
};
use frame_support::traits::OnRuntimeUpgrade;

#[test]
fn basic_works() {
	test_closure(|| {
		// Add three migrations. Each taking one block longer.
		MigrationsStorage::set(vec![(SucceedAfter, 0), (SucceedAfter, 1), (SucceedAfter, 2)]);

		System::set_block_number(1);
		Migrations::on_runtime_upgrade();
		run_to_block(10);

		// Check that the executed migrations are recorded into `Historical`.
		assert_eq!(
			historic(),
			vec![
				mocked_id(SucceedAfter, 0),
				mocked_id(SucceedAfter, 1),
				mocked_id(SucceedAfter, 2),
			]
		);
		// Check that we got all events.
		assert_events(vec![
			Event::UpgradeStarted,
			Event::MigrationCompleted { index: 0, took: 0 },
			Event::MigrationAdvanced { index: 1, step: 0 },
			Event::MigrationCompleted { index: 1, took: 1 },
			Event::MigrationAdvanced { index: 2, step: 0 },
			Event::MigrationAdvanced { index: 2, step: 1 },
			Event::MigrationCompleted { index: 2, took: 2 },
			Event::UpgradeCompleted { migrations: 3 },
		]);
	});
}

#[test]
fn historic_skipping_works() {
	test_closure(|| {
		MigrationsStorage::set(vec![
			(SucceedAfter, 0),
			(SucceedAfter, 0), // duplicate
			(SucceedAfter, 1),
			(SucceedAfter, 2),
			(SucceedAfter, 1), // duplicate
		]);

		System::set_block_number(1);
		Migrations::on_runtime_upgrade();
		run_to_block(10);

		// Just three historical ones, since two were added twice.
		assert_eq!(
			historic(),
			vec![
				mocked_id(SucceedAfter, 0),
				mocked_id(SucceedAfter, 1),
				mocked_id(SucceedAfter, 2),
			]
		);
		// Events received.
		assert_events(vec![
			Event::UpgradeStarted,
			Event::MigrationCompleted { index: 0, took: 0 },
			Event::MigrationSkippedHistoric { index: 1 },
			Event::MigrationAdvanced { index: 2, step: 0 },
			Event::MigrationCompleted { index: 2, took: 1 },
			Event::MigrationAdvanced { index: 3, step: 0 },
			Event::MigrationAdvanced { index: 3, step: 1 },
			Event::MigrationCompleted { index: 3, took: 2 },
			Event::MigrationSkippedHistoric { index: 4 },
			Event::UpgradeCompleted { migrations: 5 },
		]);

		// Now go for another upgrade; just to make sure that it wont execute again.
		System::reset_events();
		Migrations::on_runtime_upgrade();
		run_to_block(20);

		// Same historical ones as before.
		assert_eq!(
			historic(),
			vec![
				mocked_id(SucceedAfter, 0),
				mocked_id(SucceedAfter, 1),
				mocked_id(SucceedAfter, 2),
			]
		);

		// Everything got skipped.
		assert_events(vec![
			Event::UpgradeStarted,
			Event::MigrationSkippedHistoric { index: 0 },
			Event::MigrationSkippedHistoric { index: 1 },
			Event::MigrationSkippedHistoric { index: 2 },
			Event::MigrationSkippedHistoric { index: 3 },
			Event::MigrationSkippedHistoric { index: 4 },
			Event::UpgradeCompleted { migrations: 5 },
		]);
	});
}

/// When another upgrade happens while a migration is still running, it should set the cursor to
/// stuck.
#[test]
fn upgrade_fails_when_migration_active() {
	test_closure(|| {
		MigrationsStorage::set(vec![(SucceedAfter, 10)]);

		System::set_block_number(1);
		Migrations::on_runtime_upgrade();
		run_to_block(3);

		//assert_eq!( // TODO
		//	historic(),
		//	vec![mocked_id(SucceedAfter, 0)]
		//);
		// Events received.
		assert_events(vec![
			Event::UpgradeStarted,
			Event::MigrationAdvanced { index: 0, step: 0 },
			Event::MigrationAdvanced { index: 0, step: 1 },
		]);
		// Upgrade again.
		Migrations::on_runtime_upgrade();
		// -- Defensive path --
		assert_eq!(Cursor::<T>::get(), Some(MigrationCursor::Stuck));
		assert_events(vec![Event::UpgradeFailed]);
	});
}
