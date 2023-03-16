// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	Encode, Decode, MaxEncodedLen, TypeInfo, Eq, PartialEq, Copy, Clone, RuntimeDebug, Default,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Weight {
	#[codec(compact)]
	/// The weight of computational time used based on some reference hardware.
	ref_time: u64,
	#[codec(compact)]
	/// The weight of storage space used by proof of validity.
	proof_size: u64,
}

impl From<OldWeight> for Weight {
	fn from(old: OldWeight) -> Self {
		Weight::from_parts(old.0, 0)
	}
}

impl Weight {
	/// Set the reference time part of the weight.
	pub const fn set_ref_time(mut self, c: u64) -> Self {
		self.ref_time = c;
		self
	}

	/// Set the storage size part of the weight.
	pub const fn set_proof_size(mut self, c: u64) -> Self {
		self.proof_size = c;
		self
	}

	/// Return the reference time part of the weight.
	pub const fn ref_time(&self) -> u64 {
		self.ref_time
	}

	/// Return the storage size part of the weight.
	pub const fn proof_size(&self) -> u64 {
		self.proof_size
	}

	/// Return a mutable reference to the reference time part of the weight.
	pub fn ref_time_mut(&mut self) -> &mut u64 {
		&mut self.ref_time
	}

	/// Return a mutable reference to the storage size part of the weight.
	pub fn proof_size_mut(&mut self) -> &mut u64 {
		&mut self.proof_size
	}

	/// Return self but discard any reference time.
	pub const fn without_ref_time(&self) -> Self {
		Self { ref_time: 0, proof_size: self.proof_size }
	}

	/// Return self but discard any proof size.
	pub const fn without_proof_size(&self) -> Self {
		Self { ref_time: self.ref_time, proof_size: 0 }
	}

	pub const MAX: Self = Self { ref_time: u64::MAX, proof_size: u64::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self {
			ref_time: self.ref_time.min(other.ref_time),
			proof_size: self.proof_size.min(other.proof_size),
		}
	}

	/// Get the aggressive max of `self` and `other` weight.
	pub fn max(&self, other: Self) -> Self {
		Self {
			ref_time: self.ref_time.max(other.ref_time),
			proof_size: self.proof_size.max(other.proof_size),
		}
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.any_gt(*limit) {
			None
		} else {
			Some(total)
		}
	}

	/// Construct [`Weight`] with reference time weight and 0 storage size weight.
	#[deprecated = "Will be removed soon; use `from_parts` instead."]
	pub const fn from_ref_time(ref_time: u64) -> Self {
		Self { ref_time, proof_size: 0 }
	}

	/// Construct [`Weight`] with storage size weight and 0 reference time weight.
	#[deprecated = "Will be removed soon; use `from_parts` instead."]
	pub const fn from_proof_size(proof_size: u64) -> Self {
		Self { ref_time: 0, proof_size }
	}

	/// Construct [`Weight`] from weight parts, namely reference time and proof size weights.
	pub const fn from_parts(ref_time: u64, proof_size: u64) -> Self {
		Self { ref_time, proof_size }
	}

	/// Construct [`Weight`] from the same weight for all parts.
	pub const fn from_all(value: u64) -> Self {
		Self { ref_time: value, proof_size: value }
	}

	/// Saturating [`Weight`] addition. Computes `self + rhs`, saturating at the numeric bounds of
	/// all fields instead of overflowing.
	pub const fn saturating_add(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time.saturating_add(rhs.ref_time),
			proof_size: self.proof_size.saturating_add(rhs.proof_size),
		}
	}

	/// Saturating [`Weight`] subtraction. Computes `self - rhs`, saturating at the numeric bounds
	/// of all fields instead of overflowing.
	pub const fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time.saturating_sub(rhs.ref_time),
			proof_size: self.proof_size.saturating_sub(rhs.proof_size),
		}
	}

	/// Saturating [`Weight`] scalar multiplication. Computes `self.field * scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_mul(self, scalar: u64) -> Self {
		Self {
			ref_time: self.ref_time.saturating_mul(scalar),
			proof_size: self.proof_size.saturating_mul(scalar),
		}
	}

	/// Saturating [`Weight`] scalar division. Computes `self.field / scalar` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_div(self, scalar: u64) -> Self {
		Self {
			ref_time: self.ref_time.saturating_div(scalar),
			proof_size: self.proof_size.saturating_div(scalar),
		}
	}

	/// Saturating [`Weight`] scalar exponentiation. Computes `self.field.pow(exp)` for all fields,
	/// saturating at the numeric bounds of all fields instead of overflowing.
	pub const fn saturating_pow(self, exp: u32) -> Self {
		Self {
			ref_time: self.ref_time.saturating_pow(exp),
			proof_size: self.proof_size.saturating_pow(exp),
		}
	}

	/// Increment [`Weight`] by `amount` via saturating addition.
	pub fn saturating_accrue(&mut self, amount: Self) {
		*self = self.saturating_add(amount);
	}

	/// Reduce [`Weight`] by `amount` via saturating subtraction.
	pub fn saturating_reduce(&mut self, amount: Self) {
		*self = self.saturating_sub(amount);
	}

	/// Checked [`Weight`] addition. Computes `self + rhs`, returning `None` if overflow occurred.
	pub const fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let ref_time = match self.ref_time.checked_add(rhs.ref_time) {
			Some(t) => t,
			None => return None,
		};
		let proof_size = match self.proof_size.checked_add(rhs.proof_size) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, proof_size })
	}

	/// Checked [`Weight`] subtraction. Computes `self - rhs`, returning `None` if overflow
	/// occurred.
	pub const fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		let ref_time = match self.ref_time.checked_sub(rhs.ref_time) {
			Some(t) => t,
			None => return None,
		};
		let proof_size = match self.proof_size.checked_sub(rhs.proof_size) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, proof_size })
	}

	/// Checked [`Weight`] scalar multiplication. Computes `self.field * scalar` for each field,
	/// returning `None` if overflow occurred.
	pub const fn checked_mul(self, scalar: u64) -> Option<Self> {
		let ref_time = match self.ref_time.checked_mul(scalar) {
			Some(t) => t,
			None => return None,
		};
		let proof_size = match self.proof_size.checked_mul(scalar) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, proof_size })
	}

	/// Checked [`Weight`] scalar division. Computes `self.field / scalar` for each field, returning
	/// `None` if overflow occurred.
	pub const fn checked_div(self, scalar: u64) -> Option<Self> {
		let ref_time = match self.ref_time.checked_div(scalar) {
			Some(t) => t,
			None => return None,
		};
		let proof_size = match self.proof_size.checked_div(scalar) {
			Some(s) => s,
			None => return None,
		};
		Some(Self { ref_time, proof_size })
	}

	/// Calculates how many `other` fit into `self`.
	///
	/// Divides each component of `self` against the same component of `other`. Returns the minimum
	/// of all those divisions. Returns `None` in case **all** components of `other` are zero.
	///
	/// This returns `Some` even if some components of `other` are zero as long as there is at least
	/// one non-zero component in `other`. The division for this particular component will then
	/// yield the maximum value (e.g u64::MAX). This is because we assume not every operation and
	/// hence each `Weight` will necessarily use each resource.
	pub const fn checked_div_per_component(self, other: &Self) -> Option<u64> {
		let mut all_zero = true;
		let ref_time = match self.ref_time.checked_div(other.ref_time) {
			Some(ref_time) => {
				all_zero = false;
				ref_time
			},
			None => u64::MAX,
		};
		let proof_size = match self.proof_size.checked_div(other.proof_size) {
			Some(proof_size) => {
				all_zero = false;
				proof_size
			},
			None => u64::MAX,
		};
		if all_zero {
			None
		} else {
			Some(if ref_time < proof_size { ref_time } else { proof_size })
		}
	}

	/// Try to increase `self` by `amount` via checked addition.
	pub fn checked_accrue(&mut self, amount: Self) -> Option<()> {
		self.checked_add(&amount).map(|new_self| *self = new_self)
	}

	/// Try to reduce `self` by `amount` via checked subtraction.
	pub fn checked_reduce(&mut self, amount: Self) -> Option<()> {
		self.checked_sub(&amount).map(|new_self| *self = new_self)
	}

	/// Return a [`Weight`] where all fields are zero.
	pub const fn zero() -> Self {
		Self { ref_time: 0, proof_size: 0 }
	}

	/// Constant version of Add for `ref_time` component with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn add_ref_time(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time + scalar, proof_size: self.proof_size }
	}

	/// Constant version of Add for `proof_size` component with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn add_proof_size(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time, proof_size: self.proof_size + scalar }
	}

	/// Constant version of Sub for `ref_time` component with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn sub_ref_time(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time - scalar, proof_size: self.proof_size }
	}

	/// Constant version of Sub for `proof_size` component with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn sub_proof_size(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time, proof_size: self.proof_size - scalar }
	}

	/// Constant version of Div with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn div(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time / scalar, proof_size: self.proof_size / scalar }
	}

	/// Constant version of Mul with u64.
	///
	/// Is only overflow safe when evaluated at compile-time.
	pub const fn mul(self, scalar: u64) -> Self {
		Self { ref_time: self.ref_time * scalar, proof_size: self.proof_size * scalar }
	}

	/// Returns true if any of `self`'s constituent weights is strictly greater than that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_gt(self, other: Self) -> bool {
		self.ref_time > other.ref_time || self.proof_size > other.proof_size
	}

	/// Returns true if all of `self`'s constituent weights is strictly greater than that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_gt(self, other: Self) -> bool {
		self.ref_time > other.ref_time && self.proof_size > other.proof_size
	}

	/// Returns true if any of `self`'s constituent weights is strictly less than that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_lt(self, other: Self) -> bool {
		self.ref_time < other.ref_time || self.proof_size < other.proof_size
	}

	/// Returns true if all of `self`'s constituent weights is strictly less than that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_lt(self, other: Self) -> bool {
		self.ref_time < other.ref_time && self.proof_size < other.proof_size
	}

	/// Returns true if any of `self`'s constituent weights is greater than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_gte(self, other: Self) -> bool {
		self.ref_time >= other.ref_time || self.proof_size >= other.proof_size
	}

	/// Returns true if all of `self`'s constituent weights is greater than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_gte(self, other: Self) -> bool {
		self.ref_time >= other.ref_time && self.proof_size >= other.proof_size
	}

	/// Returns true if any of `self`'s constituent weights is less than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn any_lte(self, other: Self) -> bool {
		self.ref_time <= other.ref_time || self.proof_size <= other.proof_size
	}

	/// Returns true if all of `self`'s constituent weights is less than or equal to that of the
	/// `other`'s, otherwise returns false.
	pub const fn all_lte(self, other: Self) -> bool {
		self.ref_time <= other.ref_time && self.proof_size <= other.proof_size
	}

	/// Returns true if any of `self`'s constituent weights is equal to that of the `other`'s,
	/// otherwise returns false.
	pub const fn any_eq(self, other: Self) -> bool {
		self.ref_time == other.ref_time || self.proof_size == other.proof_size
	}

	// NOTE: `all_eq` does not exist, as it's simply the `eq` method from the `PartialEq` trait.
}

impl Zero for Weight {
	fn zero() -> Self {
		Self::zero()
	}

	fn is_zero(&self) -> bool {
		self == &Self::zero()
	}
}

impl Add for Weight {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time + rhs.ref_time,
			proof_size: self.proof_size + rhs.proof_size,
		}
	}
}

impl Sub for Weight {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self {
			ref_time: self.ref_time - rhs.ref_time,
			proof_size: self.proof_size - rhs.proof_size,
		}
	}
}

impl<T> Mul<T> for Weight
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { ref_time: b * self.ref_time, proof_size: b * self.proof_size }
	}
}

#[cfg(any(test, feature = "std", feature = "runtime-benchmarks"))]
impl From<u64> for Weight {
	fn from(value: u64) -> Self {
		Self::from_parts(value, value)
	}
}

#[cfg(any(test, feature = "std", feature = "runtime-benchmarks"))]
impl From<(u64, u64)> for Weight {
	fn from(value: (u64, u64)) -> Self {
		Self::from_parts(value.0, value.1)
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
						proof_size: self * b.proof_size,
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
						proof_size: u64::from(self) * b.proof_size,
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
		Self { ref_time: self.ref_time / b, proof_size: self.proof_size / b }
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
		write!(f, "Weight(ref_time: {}, proof_size: {})", self.ref_time, self.proof_size)
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
			proof_size: self.proof_size + other.proof_size,
		};
	}
}

impl SubAssign for Weight {
	fn sub_assign(&mut self, other: Self) {
		*self = Self {
			ref_time: self.ref_time - other.ref_time,
			proof_size: self.proof_size - other.proof_size,
		};
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn is_zero_works() {
		assert!(Weight::zero().is_zero());
		assert!(!Weight::from_parts(1, 0).is_zero());
		assert!(!Weight::from_parts(0, 1).is_zero());
		assert!(!Weight::MAX.is_zero());
	}

	#[test]
	fn from_parts_works() {
		assert_eq!(Weight::from_parts(0, 0), Weight { ref_time: 0, proof_size: 0 });
		assert_eq!(Weight::from_parts(5, 5), Weight { ref_time: 5, proof_size: 5 });
		assert_eq!(
			Weight::from_parts(u64::MAX, u64::MAX),
			Weight { ref_time: u64::MAX, proof_size: u64::MAX }
		);
	}

	#[test]
	fn from_all_works() {
		assert_eq!(Weight::from_all(0), Weight::from_parts(0, 0));
		assert_eq!(Weight::from_all(5), Weight::from_parts(5, 5));
		assert_eq!(Weight::from_all(u64::MAX), Weight::from_parts(u64::MAX, u64::MAX));
	}

	#[test]
	fn from_u64_works() {
		assert_eq!(Weight::from_all(0), 0_u64.into());
		assert_eq!(Weight::from_all(123), 123_u64.into());
		assert_eq!(Weight::from_all(u64::MAX), u64::MAX.into());
	}

	#[test]
	fn from_u64_pair_works() {
		assert_eq!(Weight::from_parts(0, 1), (0, 1).into());
		assert_eq!(Weight::from_parts(123, 321), (123u64, 321u64).into());
		assert_eq!(Weight::from_parts(u64::MAX, 0), (u64::MAX, 0).into());
	}

	#[test]
	fn saturating_reduce_works() {
		let mut weight = Weight::from_parts(10, 20);
		weight.saturating_reduce(Weight::from_all(5));
		assert_eq!(weight, Weight::from_parts(5, 15));
		weight.saturating_reduce(Weight::from_all(5));
		assert_eq!(weight, Weight::from_parts(0, 10));
		weight.saturating_reduce(Weight::from_all(11));
		assert!(weight.is_zero());
		weight.saturating_reduce(Weight::from_all(u64::MAX));
		assert!(weight.is_zero());
	}

	#[test]
	fn checked_accrue_works() {
		let mut weight = Weight::from_parts(10, 20);
		assert!(weight.checked_accrue(Weight::from_all(2)).is_some());
		assert_eq!(weight, Weight::from_parts(12, 22));
		assert!(weight.checked_accrue(Weight::from_parts(u64::MAX, 0)).is_none());
		assert!(weight.checked_accrue(Weight::from_parts(0, u64::MAX)).is_none());
		assert_eq!(weight, Weight::from_parts(12, 22));
		assert!(weight
			.checked_accrue(Weight::from_parts(u64::MAX - 12, u64::MAX - 22))
			.is_some());
		assert_eq!(weight, Weight::MAX);
		assert!(weight.checked_accrue(Weight::from_parts(1, 0)).is_none());
		assert!(weight.checked_accrue(Weight::from_parts(0, 1)).is_none());
		assert_eq!(weight, Weight::MAX);
	}

	#[test]
	fn checked_reduce_works() {
		let mut weight = Weight::from_parts(10, 20);
		assert!(weight.checked_reduce(Weight::from_all(2)).is_some());
		assert_eq!(weight, Weight::from_parts(8, 18));
		assert!(weight.checked_reduce(Weight::from_parts(9, 0)).is_none());
		assert!(weight.checked_reduce(Weight::from_parts(0, 19)).is_none());
		assert_eq!(weight, Weight::from_parts(8, 18));
		assert!(weight.checked_reduce(Weight::from_parts(8, 0)).is_some());
		assert_eq!(weight, Weight::from_parts(0, 18));
		assert!(weight.checked_reduce(Weight::from_parts(0, 18)).is_some());
		assert!(weight.is_zero());
	}

	#[test]
	fn checked_div_per_component_works() {
		assert_eq!(
			Weight::from_parts(10, 20).checked_div_per_component(&Weight::from_parts(2, 10)),
			Some(2)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(2, 10)),
			Some(5)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(1, 10)),
			Some(10)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(2, 1)),
			Some(5)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(0, 10)),
			Some(20)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(1, 0)),
			Some(10)
		);
		assert_eq!(
			Weight::from_parts(0, 200).checked_div_per_component(&Weight::from_parts(2, 3)),
			Some(0)
		);
		assert_eq!(
			Weight::from_parts(10, 0).checked_div_per_component(&Weight::from_parts(2, 3)),
			Some(0)
		);
		assert_eq!(
			Weight::from_parts(10, 200).checked_div_per_component(&Weight::from_parts(0, 0)),
			None,
		);
		assert_eq!(
			Weight::from_parts(0, 0).checked_div_per_component(&Weight::from_parts(0, 0)),
			None,
		);
	}
}
