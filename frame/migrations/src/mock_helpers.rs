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

//! Helpers for std and no-std testing. Can be re-used by other crates.

use super::*;

use sp_core::ConstU32;
use sp_runtime::BoundedVec;

/// An opaque cursor of a migration.
pub type MockedCursor = BoundedVec<u8, ConstU32<1024>>;
/// An opaque identifier of a migration.
pub type MockedIdentifier = BoundedVec<u8, ConstU32<256>>;

/// How a [`MockedMigration`] should behave.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum MockedMigrationKind {
	/// Succeed after its number of steps elapsed.
	SucceedAfter,
	/// Fail after its number of steps elapsed.
	FailAfter,
	/// Never terminate.
	TimeoutAfter,
	/// Cause an [`InsufficientWeight`] error after its number of steps elapsed.
	HightWeightAfter(Weight),
}
use MockedMigrationKind::*; // C style

/// A migration that does something after a certain number of steps.
pub struct MockedMigration(pub MockedMigrationKind, pub u32);

impl SteppedMigration for MockedMigration {
	type Cursor = MockedCursor;
	type Identifier = MockedIdentifier;

	fn id(&self) -> Self::Identifier {
		mocked_id(self.0, self.1)
	}

	fn max_steps(&self) -> Option<u32> {
		matches!(self.0, TimeoutAfter).then(|| self.1)
	}

	fn step(
		&self,
		cursor: &Option<Self::Cursor>,
		_meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		let mut count: u32 =
			cursor.as_ref().and_then(|c| Decode::decode(&mut &c[..]).ok()).unwrap_or(0);
		log::debug!("MockedMigration: Step {}", count);
		if count != self.1 || matches!(self.0, TimeoutAfter) {
			count += 1;
			return Ok(Some(count.encode().try_into().unwrap()))
		}

		match self.0 {
			SucceedAfter => {
				log::debug!("MockedMigration: Succeeded after {} steps", count);
				Ok(None)
			},
			HightWeightAfter(required) => {
				log::debug!("MockedMigration: Not enough weight after {} steps", count);
				Err(SteppedMigrationError::InsufficientWeight { required })
			},
			FailAfter => {
				log::debug!("MockedMigration: Failed after {} steps", count);
				Err(SteppedMigrationError::Failed)
			},
			TimeoutAfter => unreachable!(),
		}
	}
}

/// Calculate the identifier of a mocked migration.
pub fn mocked_id(kind: MockedMigrationKind, steps: u32) -> MockedIdentifier {
	format!("MockedMigration({:?}, {})", kind, steps)
		.as_bytes()
		.to_vec()
		.try_into()
		.unwrap()
}
