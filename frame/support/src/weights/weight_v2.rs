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
	/// The weight of computational time used.
	pub time: TimeWeight,
	/// The weight of the storage bandwidth used.
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
		self.time <= other.time && self.bandwidth <= other.bandwidth
	}

	/// Checks if all params of `self` are greater than or equal to `other`.
	pub fn is_strictly_greater_than_or_equal(&self, other: &Self) -> bool {
		self.time >= other.time && self.bandwidth >= other.bandwidth
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

impl<T> PaysFee<T> for (WeightV2, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (WeightV2, DispatchClass) {
	fn weigh_data(&self, args: T) -> WeightV2 {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (WeightV2, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (WeightV2, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (WeightV2, Pays) {
	fn weigh_data(&self, args: T) -> WeightV2 {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (WeightV2, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (WeightV2, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

impl From<(Option<WeightV2>, Pays)> for PostDispatchInfo {
	fn from(post_weight_info: (Option<WeightV2>, Pays)) -> Self {
		let (actual_weight, pays_fee) = post_weight_info;
		Self { actual_weight, pays_fee }
	}
}

// SHAWN TODO: Disambiguate NONE
// impl From<Option<WeightV2>> for PostDispatchInfo {
// 	fn from(actual_weight: Option<WeightV2>) -> Self {
// 		Self { actual_weight, pays_fee: Default::default() }
// 	}
// }

impl<T> WeighData<T> for WeightV2 {
	fn weigh_data(&self, _: T) -> WeightV2 {
		return *self
	}
}

impl<T> ClassifyDispatch<T> for WeightV2 {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for WeightV2 {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> ClassifyDispatch<T> for (WeightV2, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn comparison_functions_work_as_expected() {
		let weight1 = WeightV2 { time: 99, bandwidth: 1 };
		let weight2 = WeightV2 { time: 1, bandwidth: 99 };
		let weight3 = WeightV2 { time: 50, bandwidth: 50 };
		let weight4 = WeightV2 { time: 1, bandwidth: 1 };

		assert!(!weight4.is_any_greater_than(&weight3));
		assert!(weight1.is_any_greater_than(&weight2));
		assert!(weight2.is_any_greater_than(&weight1));

		assert!(!weight1.is_strictly_greater_than(&weight4));
		assert!(weight3.is_strictly_greater_than(&weight4));

		assert!(weight1.is_strictly_greater_than_or_equal(&weight4));
		assert!(!weight4.is_strictly_greater_than_or_equal(&weight1));

		assert!(!weight3.is_any_less_than(&weight4));
		assert!(weight1.is_any_less_than(&weight2));
		assert!(weight2.is_any_less_than(&weight1));

		assert!(!weight4.is_strictly_less_than(&weight2));
		assert!(weight4.is_strictly_less_than(&weight3));

		assert!(weight4.is_strictly_less_than_or_equal(&weight2));
		assert!(!weight1.is_strictly_less_than_or_equal(&weight2));
	}

	#[test]
	fn try_add_works_as_expected() {
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
