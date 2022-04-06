use codec::{Decode, Encode, MaxEncodedLen};
use core::ops::{Add, Div, Mul, Sub, AddAssign, SubAssign};
use sp_runtime::{
	traits::{Bounded, CheckedAdd, One, Zero},
	RuntimeDebug,
};

use super::*;

#[derive(
	Encode, Decode, MaxEncodedLen, TypeInfo, Eq, PartialEq, Copy, Clone, RuntimeDebug, Default,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct WeightV2 {
	/// The weight of computational time used.
	pub computation: ComputationWeight,
	/// The weight of the storage bandwidth used.
	pub bandwidth: BandwidthWeight,
}

impl WeightV2 {
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

	pub fn zero() -> Self {
		<Self as Zero>::zero()
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

	/// This is a simple helper function which allows us to be backwards compatible, but will be
	/// removed in the future.
	pub const fn todo_from_v1(computation: WeightV1) -> Self {
		Self { computation, bandwidth: 0 }
	}

	/// This is a simple helper function which allows us to be backwards compatible, but will be
	/// removed in the future.
	pub const fn todo_to_v1(&self) -> WeightV1 {
		self.computation
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
}

impl From<(ComputationWeight, BandwidthWeight)> for WeightV2 {
	fn from(a: (ComputationWeight, BandwidthWeight)) -> Self {
		Self { computation: a.0, bandwidth: a.1 }
	}
}

impl Zero for WeightV2 {
	fn zero() -> Self {
		Self { computation: 0, bandwidth: 0 }
	}

	fn is_zero(&self) -> bool {
		self.computation == 0 && self.bandwidth == 0
	}
}

impl One for WeightV2 {
	fn one() -> Self {
		Self { computation: 1, bandwidth: 1 }
	}
}

impl Add for WeightV2 {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self {
			computation: self.computation + rhs.computation,
			bandwidth: self.bandwidth + rhs.bandwidth,
		}
	}
}

impl Sub for WeightV2 {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self {
			computation: self.computation - rhs.computation,
			bandwidth: self.bandwidth - rhs.bandwidth,
		}
	}
}

impl From<ComputationWeight> for WeightV2 {
	fn from(t: ComputationWeight) -> Self {
		Self { computation: t, bandwidth: 0 }
	}
}

impl Mul for WeightV2 {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self {
			computation: b.computation * self.computation,
			bandwidth: b.bandwidth * self.bandwidth,
		}
	}
}

impl<T> Mul<T> for WeightV2
where
	T: Mul<u64, Output = u64> + Copy,
{
	type Output = Self;
	fn mul(self, b: T) -> Self {
		Self { computation: b * self.computation, bandwidth: b * self.bandwidth }
	}
}

impl<T> Div<T> for WeightV2
where
	u64: Div<T, Output = u64>,
	T: Copy,
{
	type Output = Self;
	fn div(self, b: T) -> Self {
		Self { computation: self.computation / b, bandwidth: self.bandwidth / b }
	}
}

impl Mul<WeightV2> for Perbill {
	type Output = WeightV2;
	fn mul(self, b: WeightV2) -> WeightV2 {
		WeightV2 { computation: self * b.computation, bandwidth: self * b.bandwidth }
	}
}

impl Saturating for WeightV2 {
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

impl CheckedAdd for WeightV2 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let computation = self.computation.checked_add(rhs.computation)?;
		let bandwidth = self.bandwidth.checked_add(rhs.bandwidth)?;
		Some(Self { computation, bandwidth })
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

impl<T> WeighData<T> for (WeightV2, DispatchClass, Pays) {
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

impl From<Option<WeightV2>> for PostDispatchInfo {
	fn from(actual_weight: Option<WeightV2>) -> Self {
		Self { actual_weight, pays_fee: Default::default() }
	}
}

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

#[cfg(feature = "std")]
impl std::fmt::Display for WeightV2 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "WeightV2(computation: {}, bandwidth: {})", self.computation, self.bandwidth)
	}
}

impl Bounded for WeightV2 {
	fn min_value() -> Self {
		Zero::zero()
	}
	fn max_value() -> Self {
		Self::MAX
	}
}

impl AddAssign for WeightV2 {
    fn add_assign(&mut self, other: Self) {
        *self = Self {
            computation: self.computation + other.computation,
            bandwidth: self.bandwidth + other.bandwidth,
        };
    }
}

impl SubAssign for WeightV2 {
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
		let weight_99_1 = WeightV2 { computation: 99, bandwidth: 1 };
		let weight_1_99 = WeightV2 { computation: 1, bandwidth: 99 };
		let weight_50_50 = WeightV2 { computation: 50, bandwidth: 50 };
		let weight_1_1 = WeightV2 { computation: 1, bandwidth: 1 };

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
		let limit = WeightV2 { computation: 100, bandwidth: 100 };

		let weight_99_1 = WeightV2 { computation: 99, bandwidth: 1 };
		let weight_1_99 = WeightV2 { computation: 1, bandwidth: 99 };
		let weight_50_50 = WeightV2 { computation: 50, bandwidth: 50 };

		let total1 = weight_99_1.try_add(&weight_1_99, &limit);
		let total2 = weight_99_1.try_add(&weight_50_50, &limit);
		let total3 = weight_1_99.try_add(&weight_50_50, &limit);

		assert_eq!(total1.unwrap(), limit);
		assert!(total2.is_none());
		assert!(total3.is_none());
	}
}
