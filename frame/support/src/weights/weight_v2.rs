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
	traits::{Bounded, CheckedAdd, CheckedSub, Zero},
	RuntimeDebug,
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

	/// Construct [`Weight`] with reference time weight.
	pub const fn from_ref_time(ref_time: RefTimeWeight) -> Self {
		Self { ref_time }
	}

	/// Saturating [`Weight`] addition. Computes `self + rhs`, saturating at the numeric bounds of
	/// all fields instead of overflowing.
	pub const fn saturating_add(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time.saturating_add(rhs.ref_time) }
	}

	/// Saturating [`Weight`] subtraction. Computes `self - rhs`, saturating at the numeric bounds
	/// of all fields instead of overflowing.
	pub const fn saturating_sub(self, rhs: Self) -> Self {
		Self { ref_time: self.ref_time.saturating_sub(rhs.ref_time) }
	}

	/// Saturating [`Weight`] scalar multiplication. Computes `self.field * scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_mul(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time.saturating_mul(scalar) }
	}

	/// Saturating [`Weight`] scalar division. Computes `self.field / scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_div(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time.saturating_div(scalar) }
	}

	/// Saturating [`Weight`] scalar exponentiation. Computes `self.field.pow(exp)` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_pow(self, exp: u32) -> Self {
		Self { ref_time: self.ref_time.saturating_pow(exp) }
	}

	/// Increment [`Weight`] by `amount` via saturating addition.
	pub fn saturating_accrue(&mut self, amount: Self) {
		*self = self.saturating_add(amount);
	}

	/// Checked [`Weight`] addition. Computes `self + rhs`, returning `None` if overflow occurred.
	pub const fn checked_add(&self, rhs: &Self) -> Option<Self> {
		match self.ref_time.checked_add(rhs.ref_time) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}

	/// Checked [`Weight`] subtraction. Computes `self - rhs`, returning `None` if overflow
	/// occurred.
	pub const fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		match self.ref_time.checked_sub(rhs.ref_time) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}

	/// Checked [`Weight`] scalar multiplication. Computes `self.field * scalar` for each field,
	/// returning `None` if overflow occurred.
	pub const fn checked_mul(self, scalar: u64) -> Option<Self> {
		match self.ref_time.checked_mul(scalar) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}

	/// Checked [`Weight`] scalar division. Computes `self.field / scalar` for each field, returning
	/// `None` if overflow occurred.
	pub const fn checked_div(self, scalar: u64) -> Option<Self> {
		match self.ref_time.checked_div(scalar) {
			Some(ref_time) => Some(Self { ref_time }),
			None => None,
		}
	}

	/// Return a [`Weight`] where all fields are zero.
	pub const fn zero() -> Self {
		Self { ref_time: 0 }
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

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { ref_time: b * self.ref_time }
	}
}

macro_rules! weight_mul_per_impl {
	($($t:ty),* $(,)?) => {
		$(
			impl Mul<Weight> for $t {
				type Output = Weight;
				fn mul(self, b: Weight) -> Weight {
					Weight { ref_time: self * b.ref_time }
				}
			}
		)*
	}
}
weight_mul_per_impl!(
	sp_runtime::Percent,
	sp_runtime::PerU16,
	sp_runtime::Permill,
	sp_runtime::Perbill,
	sp_runtime::Perquintill,
);

macro_rules! weight_mul_primitive_impl {
	($($t:ty),* $(,)?) => {
		$(
			impl Mul<Weight> for $t {
				type Output = Weight;
				fn mul(self, b: Weight) -> Weight {
					Weight { ref_time: u64::from(self) * b.ref_time }
				}
			}
		)*
	}
}
weight_mul_primitive_impl!(u8, u16, u32, u64);

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

// TODO: Eventually remove these

impl From<Option<RefTimeWeight>> for PostDispatchInfo {
	fn from(maybe_actual_computation: Option<RefTimeWeight>) -> Self {
		let actual_weight = match maybe_actual_computation {
			Some(actual_computation) => Some(Weight::zero().set_ref_time(actual_computation)),
			None => None,
		};
		Self { actual_weight, pays_fee: Default::default() }
	}
}

impl From<(Option<RefTimeWeight>, Pays)> for PostDispatchInfo {
	fn from(post_weight_info: (Option<RefTimeWeight>, Pays)) -> Self {
		let (maybe_actual_time, pays_fee) = post_weight_info;
		let actual_weight = match maybe_actual_time {
			Some(actual_time) => Some(Weight::zero().set_ref_time(actual_time)),
			None => None,
		};
		Self { actual_weight, pays_fee }
	}
}

impl<T> WeighData<T> for RefTimeWeight {
	fn weigh_data(&self, _: T) -> Weight {
		return Weight::zero().set_ref_time(*self)
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
