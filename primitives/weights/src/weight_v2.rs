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
use sp_arithmetic::traits::{Bounded, CheckedAdd, CheckedSub, Zero};
use sp_debug_derive::RuntimeDebug;

use super::*;

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
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Weight {
	#[codec(compact)]
	/// The weight of computational time used based on some reference hardware.
	ref_time: u64,
	#[codec(compact)]
	/// The weight of storage space used.
	storage_size: u64,
}

impl Weight {
	/// Set the reference time part of the weight.
	pub const fn set_ref_time(mut self, c: u64) -> Self {
		self.ref_time = c;
		self
	}

	/// Set the storage size part of the weight.
	pub const fn set_storage_size(mut self, c: u64) -> Self {
		self.storage_size = c;
		self
	}

	/// Return the reference time part of the weight.
	pub const fn ref_time(&self) -> u64 {
		self.ref_time
	}

	/// Return the storage size part of the weight.
	pub const fn storage_size(&self) -> u64 {
		self.storage_size
	}

	/// Return a mutable reference to the reference time part of the weight.
	pub fn ref_time_mut(&mut self) -> &mut u64 {
		&mut self.ref_time
	}

	/// Return a mutable reference to the storage size part of the weight.
	pub fn storage_size_mut(&mut self) -> &mut u64 {
		&mut self.storage_size
	}

	pub const MAX: Self = Self { ref_time: u64::MAX, storage_size: u64::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self {
			ref_time: self.ref_time.min(other.ref_time),
			storage_size: self.storage_size.min(other.storage_size),
		}
	}

	/// Get the aggressive max of `self` and `other` weight.
	pub fn max(&self, other: Self) -> Self {
		Self {
			ref_time: self.ref_time.max(other.ref_time),
			storage_size: self.storage_size.max(other.storage_size),
		}
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.ref_time > limit.ref_time || total.storage_size > limit.storage_size {
			None
		} else {
			Some(total)
		}
	}

	/// Construct [`Weight`] with reference time weight and 0 storage size weight.
	pub const fn from_ref_time(ref_time: u64) -> Self {
		Self { ref_time, storage_size: 0 }
	}

	/// Construct [`Weight`] with storage size weight and 0 reference time weight.
	pub const fn from_storage_size(storage_size: u64) -> Self {
		Self { ref_time: 0, storage_size }
	}

	/// Construct [`Weight`] with weight components, namely reference time and storage size weights.
	pub const fn from_components(ref_time: u64, storage_size: u64) -> Self {
		Self { ref_time, storage_size }
	} 

	/// Saturating [`Weight`] addition. Computes `self + rhs`, saturating at the numeric bounds of
	/// all fields instead of overflowing.
	pub const fn saturating_add(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time.saturating_add(rhs.ref_time),
			storage_size: self.storage_size.saturating_add(rhs.storage_size),
		}
	}

	/// Saturating [`Weight`] subtraction. Computes `self - rhs`, saturating at the numeric bounds
	/// of all fields instead of overflowing.
	pub const fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time.saturating_sub(rhs.ref_time),
			storage_size: self.storage_size.saturating_sub(rhs.storage_size),
		}
	}

	/// Saturating [`Weight`] scalar multiplication. Computes `self.field * scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_mul(self, scalar: u64) -> Self {
		Self {
			ref_time: self.ref_time.saturating_mul(scalar),
			storage_size: self.storage_size.saturating_mul(scalar),
		}
	}

	/// Saturating [`Weight`] scalar division. Computes `self.field / scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_div(self, scalar: u64) -> Self {
		Self {
			ref_time: self.ref_time.saturating_div(scalar),
			storage_size: self.storage_size.saturating_div(scalar),
		}
	}

	/// Saturating [`Weight`] scalar exponentiation. Computes `self.field.pow(exp)` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_pow(self, exp: u32) -> Self {
		Self {
			ref_time: self.ref_time.saturating_pow(exp),
			storage_size: self.storage_size.saturating_pow(exp),
		}
	}

	/// Increment [`Weight`] by `amount` via saturating addition.
	pub fn saturating_accrue(&mut self, amount: Self) {
		*self = self.saturating_add(amount);
	}

	/// Checked [`Weight`] addition. Computes `self + rhs`, returning `None` if overflow occurred.
	pub const fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let ref_time = match self.ref_time.checked_add(rhs.ref_time) {
			Some(t) => t,
			None => return None,
		};
		let storage_size = match self.storage_size.checked_add(rhs.storage_size) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, storage_size })
	}

	/// Checked [`Weight`] subtraction. Computes `self - rhs`, returning `None` if overflow
	/// occurred.
	pub const fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		let ref_time = match self.ref_time.checked_sub(rhs.ref_time) {
			Some(t) => t,
			None => return None,
		};
		let storage_size = match self.storage_size.checked_sub(rhs.storage_size) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, storage_size })
	}

	/// Checked [`Weight`] scalar multiplication. Computes `self.field * scalar` for each field,
	/// returning `None` if overflow occurred.
	pub const fn checked_mul(self, scalar: u64) -> Option<Self> {
		let ref_time = match self.ref_time.checked_mul(scalar) {
			Some(t) => t,
			None => return None,
		};
		let storage_size = match self.storage_size.checked_mul(scalar) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, storage_size })
	}

	/// Checked [`Weight`] scalar division. Computes `self.field / scalar` for each field, returning
	/// `None` if overflow occurred.
	pub const fn checked_div(self, scalar: u64) -> Option<Self> {
		let ref_time = match self.ref_time.checked_div(scalar) {
			Some(t) => t,
			None => return None,
		};
		let storage_size = match self.storage_size.checked_div(scalar) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, storage_size })
	}

	/// Return a [`Weight`] where all fields are zero.
	pub const fn zero() -> Self {
		Self { ref_time: 0, storage_size: 0 }
	}

	/// Returns true if any of `self`'s constituent weights is strictly greater than that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_gt(self, other: Self) -> bool {
		self.ref_time > other.ref_time || self.storage_size > other.storage_size
	}

	/// Returns true if all of `self`'s constituent weights is strictly greater than that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_gt(self, other: Self) -> bool {
		self.ref_time > other.ref_time && self.storage_size > other.storage_size
	}

	/// Returns true if any of `self`'s constituent weights is strictly less than that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_lt(self, other: Self) -> bool {
		self.ref_time < other.ref_time || self.storage_size < other.storage_size
	}

	/// Returns true if all of `self`'s constituent weights is strictly less than that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_lt(self, other: Self) -> bool {
		self.ref_time < other.ref_time && self.storage_size < other.storage_size
	}

	/// Returns true if any of `self`'s constituent weights is greater than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_gte(self, other: Self) -> bool {
		self.ref_time >= other.ref_time || self.storage_size >= other.storage_size
	}

	/// Returns true if all of `self`'s constituent weights is greater than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_gte(self, other: Self) -> bool {
		self.ref_time >= other.ref_time && self.storage_size >= other.storage_size
	}

	/// Returns true if any of `self`'s constituent weights is less than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_lte(self, other: Self) -> bool {
		self.ref_time <= other.ref_time || self.storage_size <= other.storage_size
	}

	/// Returns true if all of `self`'s constituent weights is less than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_lte(self, other: Self) -> bool {
		self.ref_time <= other.ref_time && self.storage_size <= other.storage_size
	}

	/// Returns true if any of `self`'s constituent weights is equal to that of the `other`'s,
	/// otherwise returns false.
	pub const fn any_eq(self, other: Self) -> bool {
		self.ref_time == other.ref_time || self.storage_size == other.storage_size
	}

	// NOTE: `all_eq` does not exist, as it's simply the `eq` method from the `PartialEq` trait.
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
		Self {
			ref_time: self.ref_time + rhs.ref_time,
			storage_size: self.storage_size + rhs.storage_size,
		}
	}
}

impl Sub for Weight {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time - rhs.ref_time,
			storage_size: self.storage_size - rhs.storage_size,
		}
	}
}

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self {
			ref_time: b * self.ref_time,
			storage_size: b * self.storage_size,
		}
	}
}

macro_rules! weight_mul_per_impl {
	($($t:ty),* $(,)?) => {
		$(
			impl Mul<Weight> for $t {
				type Output = Weight;
				fn mul(self, b: Weight) -> Weight {
					Weight {
						ref_time: self * b.ref_time,
						storage_size: self * b.storage_size,
					}
				}
			}
		)*
	}
}
weight_mul_per_impl!(
	sp_arithmetic::Percent,
	sp_arithmetic::PerU16,
	sp_arithmetic::Permill,
	sp_arithmetic::Perbill,
	sp_arithmetic::Perquintill,
);

macro_rules! weight_mul_primitive_impl {
	($($t:ty),* $(,)?) => {
		$(
			impl Mul<Weight> for $t {
				type Output = Weight;
				fn mul(self, b: Weight) -> Weight {
					Weight {
						ref_time: u64::from(self) * b.ref_time,
						storage_size: u64::from(self) * b.storage_size,
					}
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
		Self { ref_time: self.ref_time / b, storage_size: self.storage_size / b }
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

impl core::fmt::Display for Weight {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "Weight(ref_time: {}, storage_size: {})", self.ref_time, self.storage_size)
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
			ref_time: self.ref_time + other.ref_time,
			storage_size: self.storage_size + other.storage_size,
		};
	}
}

impl SubAssign for Weight {
	fn sub_assign(&mut self, other: Self) {
		*self = Self {
			ref_time: self.ref_time - other.ref_time,
			storage_size: self.storage_size - other.storage_size,
		};
	}
}
