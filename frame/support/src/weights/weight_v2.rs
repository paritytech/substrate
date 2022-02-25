use codec::{Decode, Encode, MaxEncodedLen};
use core::ops::{Add, Mul, Sub};
use sp_runtime::{
	traits::{CheckedAdd, One, Zero},
	RuntimeDebug,
};

use super::*;

#[derive(
	Encode, Decode, MaxEncodedLen, TypeInfo, Eq, PartialEq, Copy, Clone, RuntimeDebug, Default,
)]
pub struct WeightV2 {
	pub time: TimeWeight,
	pub bandwidth: StorageWeight,
}

impl WeightV2 {
	pub const MAX: Self = Self { time: TimeWeight::MAX, bandwidth: StorageWeight::MAX };

	/// Get the conservative min of `self` and `other` weight.
	pub fn min(&self, other: Self) -> Self {
		Self { time: self.time.min(other.time), bandwidth: self.bandwidth.min(other.bandwidth) }
	}

	/// Try to add some `other` weight while upholding the `limit`.
	pub fn try_add(&self, other: &Self, limit: &Self) -> Option<Self> {
		let total = self.checked_add(other)?;
		if total.time > limit.time || total.bandwidth > limit.bandwidth {
			None
		} else {
			Some(total)
		}
	}

	/// Checks if any param of `self` is less than `other`.
	pub fn is_any_less_than(&self, other: &Self) -> bool {
		self.time < other.time || self.bandwidth < other.bandwidth
	}

	/// Checks if any param of `self` is less than `other`.
	pub fn is_any_greater_than(&self, other: &Self) -> bool {
		self.time > other.time || self.bandwidth > other.bandwidth
	}

	/// Checks if all params of `self` are less than `other`.
	pub fn is_strictly_less_than(&self, other: &Self) -> bool {
		self.time < other.time && self.bandwidth < other.bandwidth
	}

	/// Checks if all params of `self` are greater than `other`.
	pub fn is_strictly_greater_than(&self, other: &Self) -> bool {
		self.time > other.time && self.bandwidth > other.bandwidth
	}

	/// Checks if all params of `self` are less than or equal to `other`.
	pub fn is_strictly_less_than_or_equal(&self, other: &Self) -> bool {
		if self.time > other.time || self.bandwidth > other.bandwidth {
			return false
		}

		true
	}

	/// Checks if all params of `self` are greater than or equal to `other`.
	pub fn is_strictly_greater_than_or_equal(&self, other: &Self) -> bool {
		if self.time < other.time || self.bandwidth < other.bandwidth {
			return false
		}

		true
	}
}

impl From<(TimeWeight, StorageWeight)> for WeightV2 {
	fn from(a: (TimeWeight, StorageWeight)) -> Self {
		Self { time: a.0, bandwidth: a.1 }
	}
}

impl Zero for WeightV2 {
	fn zero() -> Self {
		Self { time: 0, bandwidth: 0 }
	}

	fn is_zero(&self) -> bool {
		self.time == 0 && self.bandwidth == 0
	}
}

impl One for WeightV2 {
	fn one() -> Self {
		Self { time: 1, bandwidth: 1 }
	}
}

impl Add for WeightV2 {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self { time: self.time + rhs.time, bandwidth: self.bandwidth + rhs.bandwidth }
	}
}

impl Sub for WeightV2 {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self { time: self.time - rhs.time, bandwidth: self.bandwidth - rhs.bandwidth }
	}
}

impl From<TimeWeight> for WeightV2 {
	fn from(t: TimeWeight) -> Self {
		Self { time: t, bandwidth: 0 }
	}
}

impl Mul for WeightV2 {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self { time: b.time * self.time, bandwidth: b.bandwidth * self.bandwidth }
	}
}

impl Mul<Perbill> for WeightV2 {
	type Output = Self;
	fn mul(self, b: Perbill) -> Self {
		Self { time: b * self.time, bandwidth: b * self.bandwidth }
	}
}

impl Mul<WeightV2> for Perbill {
	type Output = WeightV2;
	fn mul(self, b: WeightV2) -> WeightV2 {
		WeightV2 { time: self * b.time, bandwidth: self * b.bandwidth }
	}
}

impl Saturating for WeightV2 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_add(rhs.time),
			bandwidth: self.bandwidth.saturating_add(rhs.bandwidth),
		}
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_sub(rhs.time),
			bandwidth: self.bandwidth.saturating_sub(rhs.bandwidth),
		}
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_mul(rhs.time),
			bandwidth: self.bandwidth.saturating_mul(rhs.bandwidth),
		}
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self {
			time: self.time.saturating_pow(exp as u32),
			bandwidth: self.bandwidth.saturating_pow(exp as u32),
		}
	}
}

impl CheckedAdd for WeightV2 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let time = self.time.checked_add(rhs.time)?;
		let bandwidth = self.bandwidth.checked_add(rhs.bandwidth)?;
		Some(Self { time, bandwidth })
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	// This test verifies that when any parameter of the WeightV2 is greater, the whole weight is
	// greater. This can to two things both being greater than each other, but that is okay :)
	#[test]
	fn comparison_works_as_expected() {
		let limit = WeightV2 { time: 100, bandwidth: 100 };

		let weight1 = WeightV2 { time: 99, bandwidth: 1 };

		let weight2 = WeightV2 { time: 1, bandwidth: 99 };

		let weight3 = WeightV2 { time: 50, bandwidth: 50 };

		let total1 = weight1.try_add(&weight2, &limit);
		let total2 = weight1.try_add(&weight3, &limit);
		let total3 = weight2.try_add(&weight3, &limit);

		assert_eq!(total1.unwrap(), limit);
		assert!(total2.is_none());
		assert!(total3.is_none());
	}
}
