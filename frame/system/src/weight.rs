// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use codec::{Encode, Decode};
use frame_support::weights::{Weight, DispatchClass};
use sp_runtime::RuntimeDebug;

/// An object to track the currently used extrinsic weight in a block.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct ExtrinsicsWeight {
	normal: Weight,
	operational: Weight,
}

impl ExtrinsicsWeight {
	/// Returns the total weight consumed by all extrinsics in the block.
	pub fn total(&self) -> Weight {
		self.normal.saturating_add(self.operational)
	}

	/// Add some weight of a specific dispatch class, saturating at the numeric bounds of `Weight`.
	pub fn add(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_add(weight);
	}

	/// Try to add some weight of a specific dispatch class, returning Err(()) if overflow would
	/// occur.
	pub fn checked_add(&mut self, weight: Weight, class: DispatchClass) -> Result<(), ()> {
		let value = self.get_mut(class);
		*value = value.checked_add(weight).ok_or(())?;
		Ok(())
	}

	/// Subtract some weight of a specific dispatch class, saturating at the numeric bounds of
	/// `Weight`.
	pub fn sub(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_sub(weight);
	}

	/// Get the current weight of a specific dispatch class.
	pub fn get(&self, class: DispatchClass) -> Weight {
		match class {
			DispatchClass::Operational => self.operational,
			DispatchClass::Normal | DispatchClass::Mandatory => self.normal,
		}
	}

	/// Get a mutable reference to the current weight of a specific dispatch class.
	fn get_mut(&mut self, class: DispatchClass) -> &mut Weight {
		match class {
			DispatchClass::Operational => &mut self.operational,
			DispatchClass::Normal | DispatchClass::Mandatory => &mut self.normal,
		}
	}

	/// Set the weight of a specific dispatch class.
	pub fn put(&mut self, new: Weight, class: DispatchClass) {
		*self.get_mut(class) = new;
	}
}
