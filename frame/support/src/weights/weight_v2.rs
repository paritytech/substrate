// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use codec::{Decode, Encode, MaxEncodedLen};
use core::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};
use sp_runtime::{
	traits::{Bounded, CheckedAdd, CheckedSub, One, Zero},
	RuntimeDebug,
};

use super::*;

#[derive(
	Encode, Decode, MaxEncodedLen, TypeInfo, Eq, PartialEq, Copy, Clone, RuntimeDebug, Default,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Weight {
	/// The weight of computational time used.
	computation: ComputationWeight,
	/// The weight of the storage bandwidth used.
	bandwidth: BandwidthWeight,
}

impl Weight {
	/// Create a new Weight with zero computation and bandwidth.
	pub const fn new() -> Self {
		Self { computation: 0, bandwidth: 0 }
	}

	/// Set the computational part of the weight.
	pub const fn set_computation(mut self, c: ComputationWeight) -> Self {
		self.computation = c;
		self
	}

	/// Set the bandwidth part of the weight.
	pub const fn set_bandwidth(mut self, b: BandwidthWeight) -> Self {
		self.bandwidth = b;
		self
	}

	/// Return the computational part of the weight.
	pub const fn computation(&self) -> ComputationWeight {
		self.computation
	}

	/// Return the bandwidth part of the weight.
	pub const fn bandwidth(&self) -> BandwidthWeight {
		self.bandwidth
	}

	/// Return a mutable computational part of the weight.
	pub fn computation_mut(&mut self) -> &mut ComputationWeight {
		&mut self.computation
	}

	/// Return a mutable bandwidth part of the weight.
	pub fn bandwidth_mut(&mut self) -> &mut BandwidthWeight {
		&mut self.bandwidth
	}

	pub const MAX: Self =
		Self { computation: ComputationWeight::MAX, bandwidth: BandwidthWeight::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self {
			computation: self.computation.min(other.computation),
			bandwidth: self.bandwidth.min(other.bandwidth),
		}
	}

	/// Get the aggressive max of `self` and `other` weight.
	pub fn max(&self, other: Self) -> Self {
		Self {
			computation: self.computation.max(other.computation),
			bandwidth: self.bandwidth.max(other.bandwidth),
		}
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.computation > limit.computation || total.bandwidth > limit.bandwidth {
			None
		} else {
			Some(total)
		}
	}

	/// Construct with computation weight only (zero `bandwith`).
	pub const fn from_computation(computation: ComputationWeight) -> Self {
		Self { computation, bandwidth: 0 }
	}

	/// Checks if any param of `self` is less than `other`.
	pub fn is_any_less_than(&self, other: &Self) -> bool {
		self.computation < other.computation || self.bandwidth < other.bandwidth
	}

	/// Checks if any param of `self` is less than `other`.
	pub fn is_any_greater_than(&self, other: &Self) -> bool {
		self.computation > other.computation || self.bandwidth > other.bandwidth
	}

	/// Checks if all params of `self` are less than `other`.
	pub fn is_strictly_less_than(&self, other: &Self) -> bool {
		self.computation < other.computation && self.bandwidth < other.bandwidth
	}

	/// Checks if all params of `self` are greater than `other`.
	pub fn is_strictly_greater_than(&self, other: &Self) -> bool {
		self.computation > other.computation && self.bandwidth > other.bandwidth
	}

	/// Checks if all params of `self` are less than or equal to `other`.
	pub fn is_strictly_less_than_or_equal(&self, other: &Self) -> bool {
		self.computation <= other.computation && self.bandwidth <= other.bandwidth
	}

	/// Checks if all params of `self` are greater than or equal to `other`.
	pub fn is_strictly_greater_than_or_equal(&self, other: &Self) -> bool {
		self.computation >= other.computation && self.bandwidth >= other.bandwidth
	}

	pub fn checked_mul(self, rhs: u64) -> Option<Self> {
		let computation = self.computation.checked_mul(rhs)?;
		let bandwidth = self.bandwidth.checked_mul(rhs)?;
		Some(Self { computation, bandwidth })
	}

	pub fn checked_div(self, rhs: u64) -> Option<Self> {
		let computation = self.computation.checked_div(rhs)?;
		let bandwidth = self.bandwidth.checked_div(rhs)?;
		Some(Self { computation, bandwidth })
	}
}

impl From<(ComputationWeight, BandwidthWeight)> for Weight {
	fn from(a: (ComputationWeight, BandwidthWeight)) -> Self {
		Self { computation: a.0, bandwidth: a.1 }
	}
}

impl Zero for Weight {
	fn zero() -> Self {
		Self { computation: 0, bandwidth: 0 }
	}

	fn is_zero(&self) -> bool {
		self.computation == 0 && self.bandwidth == 0
	}
}

impl One for Weight {
	fn one() -> Self {
		Self { computation: 1, bandwidth: 1 }
	}
}

impl Add for Weight {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self {
			computation: self.computation + rhs.computation,
			bandwidth: self.bandwidth + rhs.bandwidth,
		}
	}
}

impl Sub for Weight {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self {
			computation: self.computation - rhs.computation,
			bandwidth: self.bandwidth - rhs.bandwidth,
		}
	}
}

impl From<ComputationWeight> for Weight {
	fn from(t: ComputationWeight) -> Self {
		Self { computation: t, bandwidth: 0 }
	}
}

impl Mul for Weight {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self {
			computation: b.computation * self.computation,
			bandwidth: b.bandwidth * self.bandwidth,
		}
	}
}

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { computation: b * self.computation, bandwidth: b * self.bandwidth }
	}
}

impl<T> Div<T> for Weight
where
	u64: Div<T, Output = u64>,
	T: Copy,
{
	type Output = Self;
	fn div(self, b: T) -> Self {
		Self { computation: self.computation / b, bandwidth: self.bandwidth / b }
	}
}

impl Mul<Weight> for Perbill {
	type Output = Weight;
	fn mul(self, b: Weight) -> Weight {
		Weight { computation: self * b.computation, bandwidth: self * b.bandwidth }
	}
}

impl Saturating for Weight {
	fn saturating_add(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_add(rhs.computation),
			bandwidth: self.bandwidth.saturating_add(rhs.bandwidth),
		}
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_sub(rhs.computation),
			bandwidth: self.bandwidth.saturating_sub(rhs.bandwidth),
		}
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_mul(rhs.computation),
			bandwidth: self.bandwidth.saturating_mul(rhs.bandwidth),
		}
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self {
			computation: self.computation.saturating_pow(exp as u32),
			bandwidth: self.bandwidth.saturating_pow(exp as u32),
		}
	}
}

impl CheckedAdd for Weight {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let computation = self.computation.checked_add(rhs.computation)?;
		let bandwidth = self.bandwidth.checked_add(rhs.bandwidth)?;
		Some(Self { computation, bandwidth })
	}
}

impl CheckedSub for Weight {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		let computation = self.computation.checked_sub(rhs.computation)?;
		let bandwidth = self.bandwidth.checked_sub(rhs.bandwidth)?;
		Some(Self { computation, bandwidth })
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (Weight, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (Weight, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (Weight, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

impl From<(Option<Weight>, Pays)> for PostDispatchInfo {
	fn from(post_weight_info: (Option<Weight>, Pays)) -> Self {
		let (actual_weight, pays_fee) = post_weight_info;
		Self { actual_weight, pays_fee }
	}
}

impl From<Option<Weight>> for PostDispatchInfo {
	fn from(actual_weight: Option<Weight>) -> Self {
		Self { actual_weight, pays_fee: Default::default() }
	}
}

impl<T> WeighData<T> for Weight {
	fn weigh_data(&self, _: T) -> Weight {
		return *self
	}
}

impl<T> ClassifyDispatch<T> for Weight {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for Weight {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl core::fmt::Display for Weight {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "Weight(computation: {}, bandwidth: {})", self.computation, self.bandwidth)
	}
}

impl Bounded for Weight {
	fn min_value() -> Self {
		Zero::zero()
	}
	fn max_value() -> Self {
		Self::MAX
	}
}

impl AddAssign for Weight {
	fn add_assign(&mut self, other: Self) {
		*self = Self {
			computation: self.computation + other.computation,
			bandwidth: self.bandwidth + other.bandwidth,
		};
	}
}

impl SubAssign for Weight {
	fn sub_assign(&mut self, other: Self) {
		*self = Self {
			computation: self.computation - other.computation,
			bandwidth: self.bandwidth - other.bandwidth,
		};
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn comparison_functions_work_as_expected() {
		let weight_99_1 = Weight { computation: 99, bandwidth: 1 };
		let weight_1_99 = Weight { computation: 1, bandwidth: 99 };
		let weight_50_50 = Weight { computation: 50, bandwidth: 50 };
		let weight_1_1 = Weight { computation: 1, bandwidth: 1 };

		assert!(!weight_1_1.is_any_greater_than(&weight_50_50));
		assert!(weight_99_1.is_any_greater_than(&weight_1_99));
		assert!(weight_1_99.is_any_greater_than(&weight_99_1));

		assert!(!weight_99_1.is_strictly_greater_than(&weight_1_1));
		assert!(weight_50_50.is_strictly_greater_than(&weight_1_1));

		assert!(weight_99_1.is_strictly_greater_than_or_equal(&weight_1_1));
		assert!(!weight_1_1.is_strictly_greater_than_or_equal(&weight_99_1));

		assert!(!weight_50_50.is_any_less_than(&weight_1_1));
		assert!(weight_99_1.is_any_less_than(&weight_1_99));
		assert!(weight_1_99.is_any_less_than(&weight_99_1));

		assert!(!weight_1_1.is_strictly_less_than(&weight_1_99));
		assert!(weight_1_1.is_strictly_less_than(&weight_50_50));

		assert!(weight_1_1.is_strictly_less_than_or_equal(&weight_1_99));
		assert!(!weight_99_1.is_strictly_less_than_or_equal(&weight_1_99));
	}

	#[test]
	fn try_add_works_as_expected() {
		let limit = Weight { computation: 100, bandwidth: 100 };

		let weight_99_1 = Weight { computation: 99, bandwidth: 1 };
		let weight_1_99 = Weight { computation: 1, bandwidth: 99 };
		let weight_50_50 = Weight { computation: 50, bandwidth: 50 };

		let total1 = weight_99_1.try_add(&weight_1_99, &limit);
		let total2 = weight_99_1.try_add(&weight_50_50, &limit);
		let total3 = weight_1_99.try_add(&weight_50_50, &limit);

		assert_eq!(total1.unwrap(), limit);
		assert!(total2.is_none());
		assert!(total3.is_none());
	}
}
