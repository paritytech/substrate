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

use crate::{mock::*, Event, Executed};
use frame_support::traits::OnRuntimeUpgrade;

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
	sp_tracing::try_init_simple();

	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Migrations::on_runtime_upgrade();

		run_to_block(10);

		assert_last_event::<Test>(Event::UpgradeCompleted { migrations: 4 }.into());
		// Just three, since one was added twice.
		assert_eq!(Executed::<Test>::iter().count(), 3);
	});
}
