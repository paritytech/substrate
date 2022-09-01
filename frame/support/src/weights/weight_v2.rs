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

use codec::{CompactAs, Decode, Encode, MaxEncodedLen};
use core::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};
use sp_runtime::{
	traits::{Bounded, CheckedAdd, CheckedSub, One, Zero},
	Perquintill, RuntimeDebug,
};

use super::*;

/// The unit of measurement for computational time spent when executing runtime logic on reference
/// hardware.
pub type RefTimeWeight = u64;

#[derive(
	Encode,
	Decode,
	MaxEncodedLen,
	TypeInfo,
	Eq,
	PartialEq,
	Copy,
	Clone,
	RuntimeDebug,
	Default,
	Ord,
	PartialOrd,
	CompactAs,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Weight {
	/// The weight of computational time used based on some reference hardware.
	ref_time: RefTimeWeight,
}

impl Weight {
	/// Create a new Weight with zero.
	pub const fn new() -> Self {
		Self { ref_time: 0 }
	}

	/// Set the reference time part of the weight.
	pub const fn set_ref_time(mut self, c: RefTimeWeight) -> Self {
		self.ref_time = c;
		self
	}

	/// Return the reference time part of the weight.
	pub const fn ref_time(&self) -> RefTimeWeight {
		self.ref_time
	}

	/// Return a mutable reference time part of the weight.
	pub fn ref_time_mut(&mut self) -> &mut RefTimeWeight {
		&mut self.ref_time
	}

	pub const MAX: Self = Self { ref_time: RefTimeWeight::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self { ref_time: self.ref_time.min(other.ref_time) }
	}

	/// Get the aggressive max of `self` and `other` weight.
	pub fn max(&self, other: Self) -> Self {
		Self { ref_time: self.ref_time.max(other.ref_time) }
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.ref_time > limit.ref_time {
			None
		} else {
			Some(total)
		}
	}

	/// Construct with reference time weight.
	pub const fn from_ref_time(ref_time: RefTimeWeight) -> Self {
		Self { ref_time }
	}

	pub fn checked_mul(self, rhs: u64) -> Option<Self> {
		let ref_time = self.ref_time.checked_mul(rhs)?;
		Some(Self { ref_time })
	}

	pub fn checked_div(self, rhs: u64) -> Option<Self> {
		let ref_time = self.ref_time.checked_div(rhs)?;
		Some(Self { ref_time })
	}

	pub const fn scalar_saturating_mul(self, rhs: u64) -> Self {
		Self { ref_time: self.ref_time.saturating_mul(rhs) }
	}

	pub const fn scalar_div(self, rhs: u64) -> Self {
		Self { ref_time: self.ref_time / rhs }
	}
}

impl Zero for Weight {
	fn zero() -> Self {
		Self::zero()
	}

	fn is_zero(&self) -> bool {
		self.ref_time == 0
	}
}

impl One for Weight {
	fn one() -> Self {
		Self::one()
	}
}

impl Add for Weight {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time + rhs.ref_time }
	}
}

impl Sub for Weight {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time - rhs.ref_time }
	}
}

impl Mul for Weight {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self { ref_time: b.ref_time * self.ref_time }
	}
}

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { ref_time: b * self.ref_time }
	}
}

impl Mul<Weight> for Perbill {
	type Output = Weight;
	fn mul(self, b: Weight) -> Weight {
		Weight { ref_time: self * b.ref_time }
	}
}

impl Mul<Weight> for Perquintill {
	type Output = Weight;
	fn mul(self, b: Weight) -> Weight {
		Weight { ref_time: self * b.ref_time }
	}
}

impl Mul<Weight> for u64 {
	type Output = Weight;
	fn mul(self, b: Weight) -> Weight {
		Weight { ref_time: self * b.ref_time }
	}
}

impl<T> Div<T> for Weight
where
	u64: Div<T, Output = u64>,
	T: Copy,
{
	type Output = Self;
	fn div(self, b: T) -> Self {
		Self { ref_time: self.ref_time / b }
	}
}

impl Saturating for Weight {
	fn saturating_add(self, rhs: Self) -> Self {
		self.saturating_add(rhs)
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		self.saturating_sub(rhs)
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		self.saturating_mul(rhs)
	}

	fn saturating_pow(self, exp: usize) -> Self {
		self.saturating_pow(exp)
	}
}

impl CheckedAdd for Weight {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		self.checked_add(rhs)
	}
}

impl CheckedSub for Weight {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		self.checked_sub(rhs)
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
		write!(f, "Weight(ref_time: {})", self.ref_time)
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
		*self = Self { ref_time: self.ref_time + other.ref_time };
	}
}

impl SubAssign for Weight {
	fn sub_assign(&mut self, other: Self) {
		*self = Self { ref_time: self.ref_time - other.ref_time };
	}
}

impl sp_runtime::traits::Printable for Weight {
	fn print(&self) {
		self.ref_time().print()
	}
}

// Re-export common functions so you do not need to import trait.
impl Weight {
	pub const fn zero() -> Self {
		Self { ref_time: 0 }
	}

	pub const fn one() -> Self {
		Self { ref_time: 1 }
	}

	pub const fn saturating_add(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time.saturating_add(rhs.ref_time) }
	}

	pub const fn saturating_sub(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time.saturating_sub(rhs.ref_time) }
	}

	pub const fn saturating_mul(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time.saturating_mul(rhs.ref_time) }
	}

	pub const fn saturating_pow(self, exp: usize) -> Self {
		Self { ref_time: self.ref_time.saturating_pow(exp as u32) }
	}

	pub const fn checked_add(&self, rhs: &Self) -> Option<Self> {
		match self.ref_time.checked_add(rhs.ref_time) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}

	pub const fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		match self.ref_time.checked_sub(rhs.ref_time) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}
}

// TODO: Eventually remove these

impl From<Option<RefTimeWeight>> for PostDispatchInfo {
	fn from(maybe_actual_computation: Option<RefTimeWeight>) -> Self {
		let actual_weight = match maybe_actual_computation {
			Some(actual_computation) => Some(Weight::new().set_ref_time(actual_computation)),
			None => None,
		};
		Self { actual_weight, pays_fee: Default::default() }
	}
}

impl From<(Option<RefTimeWeight>, Pays)> for PostDispatchInfo {
	fn from(post_weight_info: (Option<RefTimeWeight>, Pays)) -> Self {
		let (maybe_actual_time, pays_fee) = post_weight_info;
		let actual_weight = match maybe_actual_time {
			Some(actual_time) => Some(Weight::new().set_ref_time(actual_time)),
			None => None,
		};
		Self { actual_weight, pays_fee }
	}
}

impl<T> WeighData<T> for RefTimeWeight {
	fn weigh_data(&self, _: T) -> Weight {
		return Weight::new().set_ref_time(*self)
	}
}

impl<T> ClassifyDispatch<T> for RefTimeWeight {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for RefTimeWeight {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (RefTimeWeight, DispatchClass, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (RefTimeWeight, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (RefTimeWeight, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (RefTimeWeight, DispatchClass) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (RefTimeWeight, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (RefTimeWeight, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (RefTimeWeight, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (RefTimeWeight, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (RefTimeWeight, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

// END TODO
