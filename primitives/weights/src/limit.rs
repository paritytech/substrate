// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

use crate::Weight;
use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_debug_derive::RuntimeDebug;

/// Defines a limit for the [`Weight`] type.
///
/// The properties of this limit type are:
/// - *chromatic*: both components can be limited independently.
/// - *inclusive*: since it [`Self::contains`] the limit.
/// - *optional*: can be set to `None`, in which case it is *unlimited*.
/// - *upper*: semantically it is an upper limit, not a lower.
#[derive(Encode, Decode, Copy, Clone, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize, PartialEq, Eq))]
pub struct WeightLimit {
	/// An optional upper limit on the ref time component.
	pub(crate) ref_time: Option<u64>,

	/// An optional upper limit on the proof size component.
	pub(crate) proof_size: Option<u64>,
}

impl WeightLimit {
	/// The limit that only contains `Weight::zero()`.
	pub const NOTHING: WeightLimit = Self { ref_time: Some(0), proof_size: Some(0) };

	/// The limit that contains all possible `Weight` values.
	pub const UNLIMITED: WeightLimit = Self { ref_time: None, proof_size: None };

	/// The limit that only contains `Weight::zero()`.
	pub const fn nothing() -> Self {
		Self::NOTHING
	}

	/// The limit that contains all possible `Weight` values.
	pub const fn unlimited() -> Self {
		Self::UNLIMITED
	}

	/// Use the provided weight as the limit.
	///
	/// Using `u64::MAX` is deprecated in favour of [`Self::from_limits`].
	pub const fn from_weight(weight: Weight) -> Self {
		Self { ref_time: Some(weight.ref_time), proof_size: Some(weight.proof_size) }
	}

	/// Construct a new [`Self`] with concrete limits per component.
	///
	/// Using `u64::MAX` is deprecated in favour of [`Self::from_limits`].
	pub const fn from_some_limits(ref_time: u64, proof_size: u64) -> Self {
		Self { ref_time: Some(ref_time), proof_size: Some(proof_size) }
	}

	/// Construct a new [`Self`] with optional limits per component.
	///
	/// `None` means that the component is *unlimited*.
	pub const fn from_limits(ref_time: Option<u64>, proof_size: Option<u64>) -> Self {
		Self { ref_time, proof_size }
	}

	/// Construct a new [`Self`] with a concrete time limit. The proof size is unlimited.
	pub const fn from_time_limit(ref_time: u64) -> Self {
		Self { ref_time: Some(ref_time), proof_size: None }
	}

	/// Construct a new [`Self`] with a concrete proof size limit. The time is unlimited.
	pub const fn from_proof_limit(proof_size: u64) -> Self {
		Self { ref_time: None, proof_size: Some(proof_size) }
	}

	/// Set a time limit for `self`. Overrides any existing time limit.
	pub const fn with_time_limit(mut self, ref_time: u64) -> Self {
		self.ref_time = Some(ref_time);
		self
	}

	/// Set a proof size limit for `self`. Overrides any existing proof size limit.
	pub const fn with_proof_limit(mut self, proof_size: u64) -> Self {
		self.proof_size = Some(proof_size);
		self
	}

	/// Whether all components are unlimited.
	pub const fn is_all_unlimited(&self) -> bool {
		self.ref_time.is_none() && self.proof_size.is_none()
	}

	/// Whether all components are limited.
	pub const fn is_all_limited(&self) -> bool {
		self.ref_time.is_some() && self.proof_size.is_some()
	}

	/// Whether any component is unlimited.
	pub const fn is_any_unlimited(&self) -> bool {
		self.ref_time.is_none() || self.proof_size.is_none()
	}

	/// Whether any component is limited.
	pub const fn is_any_limited(&self) -> bool {
		self.ref_time.is_some() || self.proof_size.is_some()
	}

	/// Whether the time is unlimited.
	pub const fn is_time_unlimited(&self) -> bool {
		self.ref_time.is_none()
	}

	/// Whether the proof is unlimited.
	pub const fn is_proof_unlimited(&self) -> bool {
		self.proof_size.is_none()
	}

	/// Whether the time component is limited.
	pub const fn is_time_limited(&self) -> bool {
		self.ref_time.is_some()
	}

	/// Whether the proof is limited.
	pub const fn is_proof_limited(&self) -> bool {
		self.proof_size.is_some()
	}

	/// Returns the concrete time limit. `None` means unlimited.
	pub const fn time_limit(&self) -> Option<u64> {
		self.ref_time
	}

	/// Returns the concrete proof size limit. `None` means unlimited.
	pub const fn proof_limit(&self) -> Option<u64> {
		self.proof_size
	}

	/// Whether all components of `self` are greater-or-equal than the corresponding components of
	/// `weight`.
	pub fn all_gte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit >= weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit >= weight.proof_size)
	}

	/// Whether all components of `self` are greater than the corresponding components of `weight`.
	pub fn all_gt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit > weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit > weight.proof_size)
	}

	/// Whether all components of `self` are less-or-equal than the corresponding components of
	/// `weight`.
	pub fn all_lte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit <= weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit <= weight.proof_size)
	}

	/// Whether all components of `self` are less than the corresponding components of `weight`.
	pub fn all_lt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit < weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit < weight.proof_size)
	}

	/// Whether any component of `self` is greater-or-equal than the corresponding component of
	/// `weight`.
	pub fn any_gte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(false, |limit| limit >= weight.ref_time) ||
			self.proof_size.map_or(false, |limit| limit >= weight.proof_size)
	}

	/// Whether any component of `self` is greater than the corresponding component of `weight`.
	pub fn any_gt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(false, |limit| limit > weight.ref_time) ||
			self.proof_size.map_or(false, |limit| limit > weight.proof_size)
	}

	/// Whether any component of `self` is less-or-equal than the corresponding component of
	/// `weight`.
	pub fn any_lte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(false, |limit| limit <= weight.ref_time) ||
			self.proof_size.map_or(false, |limit| limit <= weight.proof_size)
	}

	/// Whether any component of `self` is less than the corresponding component of `weight`.
	pub fn any_lt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(false, |limit| limit < weight.ref_time) ||
			self.proof_size.map_or(false, |limit| limit < weight.proof_size)
	}

	/// Uses the exact value for each *limited* component and `w` for each unlimited one.
	///
	/// # Example
	///
	/// ```rust
	/// use sp_weights::{Weight, WeightLimit};
	///
	/// let weight = Weight::from_parts(100, 100);
	/// let limit = WeightLimit::from_weight(weight);
	/// // Does nothing if there are concrete limits.
	/// assert_eq!(weight, limit.limited_or(Weight::MAX));
	///
	/// let limit = WeightLimit::from_time_limit(100);
	/// // Uses `u64::MAX` for the proof size, since there is no *limited* proof size.
	/// let weight = Weight::from_parts(100, u64::MAX);
	/// assert_eq!(weight, limit.limited_or(Weight::MAX));
	/// ```
	pub fn limited_or(self, w: Weight) -> Weight {
		Weight {
			ref_time: self.ref_time.unwrap_or(w.ref_time),
			proof_size: self.proof_size.unwrap_or(w.proof_size),
		}
	}

	/// Uses the exact value for each *limited* component and `u64::MAX` for each unlimited one.
	///
	/// Equivalent to `limited_or(Weight::MAX)`.
	pub fn limited_or_max(self) -> Weight {
		self.limited_or(Weight::MAX)
	}

	/// Uses the exact value for each *limited* component and `0` for each unlimited one.
	///
	/// Equivalent to `limited_or(Weight::zero())`.
	pub fn limited_or_min(self) -> Weight {
		self.limited_or(Weight::zero())
	}

	/// Subtract `other` from `self` and saturate. Does nothing for *unlimited* components.
	pub fn saturating_sub(mut self, weight: Weight) -> Self {
		self.saturating_reduce(weight);
		self
	}

	/// Decrease `self` by `other` and saturate. Does nothing for *unlimited* components.
	pub fn saturating_reduce(&mut self, weight: Weight) {
		self.ref_time = self.ref_time.map(|t| t.saturating_sub(weight.ref_time));
		self.proof_size = self.proof_size.map(|s| s.saturating_sub(weight.proof_size));
	}

	/// Returns the exact weight limits for each component.
	///
	/// The exact limit is the larges possible weight that is still *within* the limit. Returns
	/// `None` if one of the components is unlimited.
	pub const fn exact_limits(self) -> Option<Weight> {
		match (self.ref_time, self.proof_size) {
			(Some(t), Some(s)) => Some(Weight { ref_time: t, proof_size: s }),
			_ => None,
		}
	}

	/// Whether `weight` is within the limits of `self`.
	pub fn contains(&self, weight: Weight) -> bool {
		self.all_gte(&weight)
	}

	/// Check that `weight` is within the limits of `self`.
	pub fn check_contains(&self, weight: Weight) -> Result<(), ()> {
		self.contains(weight).then(|| ()).ok_or(())
	}
}

impl From<Weight> for WeightLimit {
	fn from(w: Weight) -> Self {
		Self::from_weight(w)
	}
}

#[cfg(test)]
mod tests {
	use super::WeightLimit as L;
	use crate::Weight;

	#[test]
	fn nothing_works() /* pun intended */
	{
		assert_eq!(L::NOTHING, L::nothing());
		let nothing = L::NOTHING;

		assert!(!nothing.is_any_unlimited());
		assert!(!nothing.is_all_unlimited());
		assert!(nothing.is_any_limited());
		assert!(nothing.is_all_limited());
	}

	#[test]
	fn unlimited_works() {
		assert_eq!(L::UNLIMITED, L::unlimited());
		let unlimited = L::UNLIMITED;

		assert!(unlimited.is_any_unlimited());
		assert!(unlimited.is_all_unlimited());
		assert!(!unlimited.is_any_limited());
		assert!(!unlimited.is_all_limited());
	}

	#[test]
	fn from_weight_works() {
		let l = L::from_weight(Weight::from_parts(u64::MAX, 123));
		assert_eq!(l, L { ref_time: Some(u64::MAX), proof_size: Some(123) });
		assert!(l.is_all_limited());
	}

	#[test]
	fn from_some_limits_works() {
		let l = L::from_some_limits(u64::MAX, 123);
		assert_eq!(l, L { ref_time: Some(u64::MAX), proof_size: Some(123) });
		assert!(l.is_all_limited());
	}

	#[test]
	fn from_limits_works() {
		let l = L::from_limits(Some(u64::MAX), Some(123));
		assert_eq!(l, L { ref_time: Some(u64::MAX), proof_size: Some(123) });
		assert!(l.is_all_limited());

		let l = L::from_limits(None, Some(123));
		assert_eq!(l, L { ref_time: None, proof_size: Some(123) });
		assert!(!l.is_all_limited());
		assert!(!l.is_all_unlimited());
	}

	#[test]
	fn from_time_limit_works() {
		let l = L::from_time_limit(u64::MAX);
		assert_eq!(l, L { ref_time: Some(u64::MAX), proof_size: None });
		assert!(l.is_time_limited());
		assert!(l.is_proof_unlimited());

		let l = L::from_time_limit(0);
		assert_eq!(l, L { ref_time: Some(0), proof_size: None });
		assert!(l.is_time_limited());
		assert!(l.is_proof_unlimited());
	}

	#[test]
	fn from_proof_limit_works() {
		let l = L::from_proof_limit(u64::MAX);
		assert_eq!(l, L { ref_time: None, proof_size: Some(u64::MAX) });
		assert!(l.is_time_unlimited());
		assert!(l.is_proof_limited());

		let l = L::from_proof_limit(0);
		assert_eq!(l, L { ref_time: None, proof_size: Some(0) });
		assert!(l.is_time_unlimited());
		assert!(l.is_proof_limited());
	}

	#[test]
	fn with_time_limit_works() {
		let l = L::UNLIMITED.with_time_limit(u64::MAX).with_time_limit(5);
		assert_eq!(l, L::from_time_limit(5));

		let l = L::UNLIMITED.with_time_limit(2).with_time_limit(u64::MAX);
		assert_eq!(l, L::from_time_limit(u64::MAX));
	}

	#[test]
	fn with_proof_limit_works() {
		let l = L::UNLIMITED.with_proof_limit(u64::MAX).with_proof_limit(5);
		assert_eq!(l, L::from_proof_limit(5));

		let l = L::UNLIMITED.with_proof_limit(2).with_proof_limit(u64::MAX);
		assert_eq!(l, L::from_proof_limit(u64::MAX));
	}

	#[test]
	fn with_limit_works() {
		let l = L::UNLIMITED.with_time_limit(10).with_proof_limit(5);
		let m = L::UNLIMITED.with_proof_limit(5).with_time_limit(10);
		assert_eq!(l, m, "Order does not matter");
		assert_eq!(m, L::from_some_limits(10, 5));
	}

	#[test]
	fn time_limit_works() {
		assert_eq!(L::from_time_limit(5).time_limit(), Some(5));
		assert_eq!(L::from_time_limit(u64::MAX).time_limit(), Some(u64::MAX));
	}

	#[test]
	fn proof_limit_works() {
		assert_eq!(L::from_proof_limit(5).proof_limit(), Some(5));
		assert_eq!(L::from_proof_limit(u64::MAX).proof_limit(), Some(u64::MAX));
	}

	#[test]
	fn comparison_basic_works() {
		let l = L::from_some_limits(1, 2);
		let m = Weight::from_parts(1, 1);

		assert!(l.all_gte(&m));
		assert!(l.any_gte(&m));
		assert!(!l.all_gt(&m));
		assert!(l.any_gt(&m));
		assert!(!l.all_lte(&m));
		assert!(l.any_lte(&m));
		assert!(!l.all_lt(&m));
		assert!(!l.any_lt(&m));

		let l = l.exact_limits().unwrap();
		let m = L::from_weight(m);

		assert!(!m.all_gte(&l));
		assert!(m.any_gte(&l));
		assert!(!m.all_gt(&l));
		assert!(!m.any_gt(&l));
		assert!(m.all_lte(&l));
		assert!(m.any_lte(&l));
		assert!(!m.all_lt(&l));
		assert!(m.any_lt(&l));
	}

	#[test]
	fn comparison_works_same_as_weight() {
		for (x, y) in good_values() {
			let l = L::from_weight(x);

			assert_eq!(x.all_gte(y), l.all_gte(&y));
			assert_eq!(x.all_gt(y), l.all_gt(&y));
			assert_eq!(x.all_lte(y), l.all_lte(&y));
			assert_eq!(x.all_lt(y), l.all_lt(&y));

			assert_eq!(x.any_gte(y), l.any_gte(&y));
			assert_eq!(x.any_gt(y), l.any_gt(&y));
			assert_eq!(x.any_lte(y), l.any_lte(&y));
			assert_eq!(x.any_lt(y), l.any_lt(&y));
		}
	}

	#[test]
	fn limited_or_works() {
		assert_eq!(L::NOTHING.limited_or(Weight::from_parts(10, 5)), Weight::zero());
		assert_eq!(L::NOTHING.limited_or(Weight::MAX), Weight::zero());

		assert_eq!(L::UNLIMITED.limited_or(Weight::from_parts(10, 5)), Weight::from_parts(10, 5));
		assert_eq!(L::UNLIMITED.limited_or(Weight::MAX), Weight::MAX);

		let l = L::from_time_limit(10);
		let m = L::from_proof_limit(5);
		assert_eq!(l.limited_or(Weight::from_parts(0, 5)), m.limited_or(Weight::from_parts(10, 0)));
	}

	#[test]
	fn limited_or_max_works() {
		assert_eq!(L::UNLIMITED.limited_or_max(), L::UNLIMITED.limited_or(Weight::MAX));
		assert_eq!(L::UNLIMITED.limited_or_max(), Weight::MAX);
		assert_eq!(L::NOTHING.limited_or_max(), Weight::zero());

		let l = L::from_time_limit(5);
		assert_eq!(l.limited_or_max(), Weight::from_parts(5, u64::MAX));
		let m = L::from_proof_limit(5);
		assert_eq!(m.limited_or_max(), Weight::from_parts(u64::MAX, 5));
	}

	#[test]
	fn limited_or_min_works() {
		assert_eq!(L::UNLIMITED.limited_or_min(), L::UNLIMITED.limited_or(Weight::zero()));
		assert_eq!(L::UNLIMITED.limited_or_min(), Weight::zero());
		assert_eq!(L::NOTHING.limited_or_min(), Weight::zero());

		let l = L::from_time_limit(5);
		assert_eq!(l.limited_or_min(), Weight::from_parts(5, 0));
		let m = L::from_proof_limit(5);
		assert_eq!(m.limited_or_min(), Weight::from_parts(0, 5));
	}

	#[test]
	fn saturating_sub_works() {
		assert_eq!(L::UNLIMITED.saturating_sub(Weight::from_parts(1, 2)), L::UNLIMITED);
		assert_eq!(L::UNLIMITED.saturating_sub(Weight::MAX), L::UNLIMITED);

		assert_eq!(L::NOTHING.saturating_sub(Weight::from_parts(1, 2)), L::NOTHING);
		assert_eq!(L::NOTHING.saturating_sub(Weight::MAX), L::NOTHING);

		assert_eq!(
			L::from_time_limit(10).saturating_sub(Weight::from_parts(5, 10)),
			L::from_time_limit(5)
		);
		assert_eq!(
			L::from_time_limit(10).saturating_sub(Weight::from_parts(50, 0)),
			L::from_time_limit(0)
		);

		assert_eq!(
			L::from_proof_limit(10).saturating_sub(Weight::from_parts(10, 5)),
			L::from_proof_limit(5)
		);
		assert_eq!(
			L::from_proof_limit(10).saturating_sub(Weight::from_parts(0, 50)),
			L::from_proof_limit(0)
		);

		assert_eq!(L::from_weight(Weight::MAX).saturating_sub(Weight::MAX), L::NOTHING);
	}

	#[test]
	fn saturating_reduce_works() {
		let mut l = L::UNLIMITED;
		l.saturating_reduce(Weight::from_parts(1, 2));
		assert_eq!(l, L::UNLIMITED);

		let mut l = L::UNLIMITED;
		l.saturating_reduce(Weight::MAX);
		assert_eq!(l, L::UNLIMITED);

		let mut l = L::NOTHING;
		l.saturating_reduce(Weight::from_parts(1, 2));
		assert_eq!(l, L::NOTHING);
		let mut l = L::NOTHING;
		l.saturating_reduce(Weight::MAX);
		assert_eq!(l, L::NOTHING);

		let mut l = L::from_time_limit(10);
		l.saturating_reduce(Weight::from_parts(5, 10));
		assert_eq!(l, L::from_time_limit(5));
		let mut l = L::from_time_limit(10);
		l.saturating_reduce(Weight::from_parts(50, 0));
		assert_eq!(l, L::from_time_limit(0));

		let mut l = L::from_proof_limit(10);
		l.saturating_reduce(Weight::from_parts(10, 5));
		assert_eq!(l, L::from_proof_limit(5));

		let mut l = L::from_proof_limit(10);
		l.saturating_reduce(Weight::from_parts(0, 50));
		assert_eq!(l, L::from_proof_limit(0));

		let mut l = L::from_weight(Weight::MAX);
		l.saturating_reduce(Weight::MAX);
		assert_eq!(l, L::NOTHING);
	}

	#[test]
	fn exact_limits_works() {
		assert!(L::UNLIMITED.exact_limits().is_none());
		assert_eq!(L::NOTHING.exact_limits(), Some(Weight::zero()));

		assert!(L::from_time_limit(5).exact_limits().is_none());
		assert!(L::from_proof_limit(5).exact_limits().is_none());

		assert_eq!(
			L::from_proof_limit(5).with_time_limit(10).exact_limits(),
			Some(Weight::from_parts(10, 5))
		);
		assert_eq!(L::from_limits(Some(2), Some(1)).exact_limits(), Some(Weight::from_parts(2, 1)));
		assert!(L::from_limits(None, Some(1)).exact_limits().is_none());
		assert!(L::from_limits(Some(2), None).exact_limits().is_none());
		assert_eq!(L::from_some_limits(2, 1).exact_limits(), Some(Weight::from_parts(2, 1)));
	}

	#[test]
	fn contains_works() {
		assert!(L::NOTHING.contains(Weight::zero()));
		assert!(!L::NOTHING.contains(Weight::from_parts(1, 0)));
		assert!(!L::NOTHING.contains(Weight::from_parts(0, 1)));
		assert!(!L::NOTHING.contains(Weight::MAX));

		assert!(L::UNLIMITED.contains(Weight::zero()));
		assert!(L::UNLIMITED.contains(Weight::from_parts(u64::MAX, 0)));
		assert!(L::UNLIMITED.contains(Weight::from_parts(0, u64::MAX)));
		assert!(L::UNLIMITED.contains(Weight::MAX));

		assert!(L::from_time_limit(10).contains(Weight::zero()));
		assert!(L::from_time_limit(10).contains(Weight::from_parts(1, 200)));
		assert!(L::from_time_limit(10).contains(Weight::from_parts(10, u64::MAX)));
		assert!(!L::from_time_limit(10).contains(Weight::from_parts(11, 0)));

		assert!(L::from_proof_limit(10).contains(Weight::zero()));
		assert!(L::from_proof_limit(10).contains(Weight::from_parts(200, 1)));
		assert!(L::from_proof_limit(10).contains(Weight::from_parts(u64::MAX, 10)));
		assert!(!L::from_proof_limit(10).contains(Weight::from_parts(0, 11)));
	}

	#[test]
	fn check_contains_works_same_as_contains() {
		for (x, y) in good_values() {
			let l = L::from_weight(x);
			assert_eq!(l.contains(y), l.check_contains(y).is_ok());
		}
	}

	#[test]
	fn check_contains_works() {
		assert!(L::NOTHING.check_contains(Weight::zero()).is_ok());
		assert!(!L::NOTHING.check_contains(Weight::from_parts(1, 0)).is_ok());
		assert!(!L::NOTHING.check_contains(Weight::from_parts(0, 1)).is_ok());
		assert!(!L::NOTHING.check_contains(Weight::MAX).is_ok());

		assert!(L::UNLIMITED.check_contains(Weight::zero()).is_ok());
		assert!(L::UNLIMITED.check_contains(Weight::from_parts(u64::MAX, 0)).is_ok());
		assert!(L::UNLIMITED.check_contains(Weight::from_parts(0, u64::MAX)).is_ok());
		assert!(L::UNLIMITED.check_contains(Weight::MAX).is_ok());

		assert!(L::from_time_limit(10).check_contains(Weight::zero()).is_ok());
		assert!(L::from_time_limit(10).check_contains(Weight::from_parts(1, 200)).is_ok());
		assert!(L::from_time_limit(10).check_contains(Weight::from_parts(10, u64::MAX)).is_ok());
		assert!(!L::from_time_limit(10).check_contains(Weight::from_parts(11, 0)).is_ok());

		assert!(L::from_proof_limit(10).check_contains(Weight::zero()).is_ok());
		assert!(L::from_proof_limit(10).check_contains(Weight::from_parts(200, 1)).is_ok());
		assert!(L::from_proof_limit(10).check_contains(Weight::from_parts(u64::MAX, 10)).is_ok());
		assert!(!L::from_proof_limit(10).check_contains(Weight::from_parts(0, 11)).is_ok());
	}

	/// Some known-good weight pairs.
	fn good_values() -> Vec<(Weight, Weight)> {
		let c = vec![0, 1, 1000, u64::MAX - 1, u64::MAX];
		let weights = c
			.iter()
			.flat_map(|t| c.iter().map(|p| Weight::from_parts(*t, *p)))
			.collect::<Vec<_>>();
		weights
			.iter()
			.flat_map(|x| weights.iter().map(|y| (*x, *y)))
			.collect::<Vec<_>>()
	}
}
