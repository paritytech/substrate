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
/// - *inclusive*: since the maximum value [`is_within`] the limit.
/// - *optional*: can be set to `None`, in which case it is *unlimited*.
/// - *upper*: semantically it is an upper limit, not a lower.
#[derive(Encode, Decode, Copy, Clone, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
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
		self.saturating_decrease(weight);
		self
	}

	/// Decrease `self` by `other` and saturate. Does nothing for *unlimited* components.
	pub fn saturating_decrease(&mut self, weight: Weight) {
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
	pub fn is_within(&self, weight: Weight) -> bool {
		self.all_gte(&weight)
	}

	/// Check that `weight` is within the limits of `self`.
	pub fn check_within(&self, weight: Weight) -> Result<(), ()> {
		self.is_within(weight).then(|| ()).ok_or(())
	}
}

impl From<Weight> for WeightLimit {
	fn from(w: Weight) -> Self {
		Self::from_weight(w)
	}
}
