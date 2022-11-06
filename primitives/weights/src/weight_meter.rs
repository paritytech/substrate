// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Contains the `WeightMeter` primitive to meter weight usage.

use super::Weight;

use sp_arithmetic::Perbill;

/// Meters consumed weight and a hard limit for the maximal consumable weight.
///
/// Can be used to check if enough weight for an operation is available before committing to it.
///
/// # Example
///
/// ```rust
/// use sp_weights::{Weight, WeightMeter};
///
/// // The weight is limited to (10, 0).
/// let mut meter = WeightMeter::from_limit(Weight::from_parts(10, 0));
/// // There is enough weight remaining for an operation with (5, 0) weight.
/// assert!(meter.check_accrue(Weight::from_parts(5, 0)));
/// // There is not enough weight remaining for an operation with (6, 0) weight.
/// assert!(!meter.check_accrue(Weight::from_parts(6, 0)));
/// ```
#[derive(Debug, Clone)]
pub struct WeightMeter {
	/// The already consumed weight.
	pub consumed: Weight,

	/// The maximal consumable weight.
	pub limit: Weight,
}

impl WeightMeter {
	/// Creates [`Self`] from a limit for the maximal consumable weight.
	pub fn from_limit(limit: Weight) -> Self {
		Self { consumed: Weight::zero(), limit }
	}

	/// Creates [`Self`] with the maximal possible limit for the consumable weight.
	pub fn max_limit() -> Self {
		Self::from_limit(Weight::MAX)
	}

	/// The remaining weight that can still be consumed.
	pub fn remaining(&self) -> Weight {
		self.limit.saturating_sub(self.consumed)
	}

	/// The ratio of consumed weight to the limit.
	///
	/// Calculates one ratio per component and returns the largest.
	pub fn consumed_ratio(&self) -> Perbill {
		let time = Perbill::from_rational(self.consumed.ref_time(), self.limit.ref_time());
		let pov = Perbill::from_rational(self.consumed.proof_size(), self.limit.proof_size());
		time.max(pov)
	}

	/// Consume the given weight after checking that it can be consumed. Otherwise do nothing.
	pub fn check_accrue(&mut self, w: Weight) -> bool {
		self.consumed.checked_add(&w).map_or(false, |test| {
			if test.any_gt(self.limit) {
				false
			} else {
				self.consumed = test;
				true
			}
		})
	}

	/// Check if the given weight can be consumed.
	pub fn can_accrue(&self, w: Weight) -> bool {
		self.consumed.checked_add(&w).map_or(false, |t| t.all_lte(self.limit))
	}
}

#[cfg(test)]
mod tests {
	use crate::*;

	#[test]
	fn weight_meter_remaining_works() {
		let mut meter = WeightMeter::from_limit(Weight::from_parts(10, 20));

		assert!(meter.check_accrue(Weight::from_parts(5, 0)));
		assert_eq!(meter.consumed, Weight::from_parts(5, 0));
		assert_eq!(meter.remaining(), Weight::from_parts(5, 20));

		assert!(meter.check_accrue(Weight::from_parts(2, 10)));
		assert_eq!(meter.consumed, Weight::from_parts(7, 10));
		assert_eq!(meter.remaining(), Weight::from_parts(3, 10));

		assert!(meter.check_accrue(Weight::from_parts(3, 10)));
		assert_eq!(meter.consumed, Weight::from_parts(10, 20));
		assert_eq!(meter.remaining(), Weight::from_parts(0, 0));
	}

	#[test]
	fn weight_meter_can_accrue_works() {
		let meter = WeightMeter::from_limit(Weight::from_parts(1, 1));

		assert!(meter.can_accrue(Weight::from_parts(0, 0)));
		assert!(meter.can_accrue(Weight::from_parts(1, 1)));
		assert!(!meter.can_accrue(Weight::from_parts(0, 2)));
		assert!(!meter.can_accrue(Weight::from_parts(2, 0)));
		assert!(!meter.can_accrue(Weight::from_parts(2, 2)));
	}

	#[test]
	fn weight_meter_check_accrue_works() {
		let mut meter = WeightMeter::from_limit(Weight::from_parts(2, 2));

		assert!(meter.check_accrue(Weight::from_parts(0, 0)));
		assert!(meter.check_accrue(Weight::from_parts(1, 1)));
		assert!(!meter.check_accrue(Weight::from_parts(0, 2)));
		assert!(!meter.check_accrue(Weight::from_parts(2, 0)));
		assert!(!meter.check_accrue(Weight::from_parts(2, 2)));
		assert!(meter.check_accrue(Weight::from_parts(0, 1)));
		assert!(meter.check_accrue(Weight::from_parts(1, 0)));
	}

	#[test]
	fn weight_meter_check_and_can_accrue_works() {
		let mut meter = WeightMeter::max_limit();

		assert!(meter.can_accrue(Weight::from_parts(u64::MAX, 0)));
		assert!(meter.check_accrue(Weight::from_parts(u64::MAX, 0)));

		assert!(meter.can_accrue(Weight::from_parts(0, u64::MAX)));
		assert!(meter.check_accrue(Weight::from_parts(0, u64::MAX)));

		assert!(!meter.can_accrue(Weight::from_parts(0, 1)));
		assert!(!meter.check_accrue(Weight::from_parts(0, 1)));

		assert!(!meter.can_accrue(Weight::from_parts(1, 0)));
		assert!(!meter.check_accrue(Weight::from_parts(1, 0)));

		assert!(meter.can_accrue(Weight::zero()));
		assert!(meter.check_accrue(Weight::zero()));
	}

	#[test]
	fn consumed_ratio_works() {
		let mut meter = WeightMeter::from_limit(Weight::from_parts(10, 20));

		assert!(meter.check_accrue(Weight::from_parts(5, 0)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(50));
		assert!(meter.check_accrue(Weight::from_parts(0, 12)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(60));

		assert!(meter.check_accrue(Weight::from_parts(2, 0)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(70));
		assert!(meter.check_accrue(Weight::from_parts(0, 4)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(80));

		assert!(meter.check_accrue(Weight::from_parts(3, 0)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(100));
		assert!(meter.check_accrue(Weight::from_parts(0, 4)));
		assert_eq!(meter.consumed_ratio(), Perbill::from_percent(100));
	}
}
