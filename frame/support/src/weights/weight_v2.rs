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

pub type ComputationWeight = u64;

#[derive(
	Encode, Decode, MaxEncodedLen, TypeInfo, Eq, PartialEq, Copy, Clone, RuntimeDebug, Default,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Weight {
	/// The weight of computational time used based on some reference hardware.
	ref_time: ComputationWeight,
}

impl Weight {
	/// Create a new Weight with zero computation and bandwidth.
	pub const fn new() -> Self {
		Self { computation: 0 }
	}

	/// Set the computational part of the weight.
	pub const fn set_computation(mut self, c: ComputationWeight) -> Self {
		self.computation = c;
		self
	}

	/// Return the computational part of the weight.
	pub const fn computation(&self) -> ComputationWeight {
		self.computation
	}

	/// Return a mutable computational part of the weight.
	pub fn computation_mut(&mut self) -> &mut ComputationWeight {
		&mut self.computation
	}

	pub const MAX: Self =
		Self { computation: ComputationWeight::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self {
			computation: self.computation.min(other.computation),
		}
	}

	/// Get the aggressive max of `self` and `other` weight.
	pub fn max(&self, other: Self) -> Self {
		Self {
			computation: self.computation.max(other.computation),
		}
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.computation > limit.computation {
			None
		} else {
			Some(total)
		}
	}

	/// Construct with computation weight only (zero `bandwith`).
	pub const fn from_computation(computation: ComputationWeight) -> Self {
		Self { computation }
	}

	pub fn checked_mul(self, rhs: u64) -> Option<Self> {
		let computation = self.computation.checked_mul(rhs)?;
		Some(Self { computation })
	}

	pub fn checked_div(self, rhs: u64) -> Option<Self> {
		let computation = self.computation.checked_div(rhs)?;
		Some(Self { computation })
	}
}

impl Zero for Weight {
	fn zero() -> Self {
		Self { computation: 0 }
	}

	fn is_zero(&self) -> bool {
		self.computation == 0
	}
}

impl One for Weight {
	fn one() -> Self {
		Self { computation: 1 }
	}
}

impl Add for Weight {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self {
			computation: self.computation + rhs.computation,
		}
	}
}

impl Sub for Weight {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self {
			computation: self.computation - rhs.computation,
		}
	}
}

impl Mul for Weight {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self {
			computation: b.computation * self.computation,
		}
	}
}

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { computation: b * self.computation }
	}
}

impl<T> Div<T> for Weight
where
	u64: Div<T, Output = u64>,
	T: Copy,
{
	type Output = Self;
	fn div(self, b: T) -> Self {
		Self { computation: self.computation / b }
	}
}

impl Mul<Weight> for Perbill {
	type Output = Weight;
	fn mul(self, b: Weight) -> Weight {
		Weight { computation: self * b.computation }
	}
}

impl Saturating for Weight {
	fn saturating_add(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_add(rhs.computation),
		}
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_sub(rhs.computation),
		}
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		Self {
			computation: self.computation.saturating_mul(rhs.computation),
		}
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self {
			computation: self.computation.saturating_pow(exp as u32),
		}
	}
}

impl CheckedAdd for Weight {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let computation = self.computation.checked_add(rhs.computation)?;
		Some(Self { computation })
	}
}

impl CheckedSub for Weight {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		let computation = self.computation.checked_sub(rhs.computation)?;
		Some(Self { computation })
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
		write!(f, "Weight(computation: {})", self.computation)
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
		};
	}
}

impl SubAssign for Weight {
	fn sub_assign(&mut self, other: Self) {
		*self = Self {
			computation: self.computation - other.computation,
		};
	}
}
