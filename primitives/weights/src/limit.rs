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

#![allow(unused_imports)] // FAIL-CI remove
use crate::Weight;

use codec::{CompactAs, Decode, Encode, MaxEncodedLen};
use core::ops::Mul;
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use sp_arithmetic::{
	traits::{BaseArithmetic, SaturatedConversion, Saturating, Unsigned, Zero},
	Perbill,
};
use sp_core::Get;
use sp_debug_derive::RuntimeDebug;

/// Defines a chromatic, inclusive, upper and optional limit for the [`Weight`] type.
///
/// - The limit is *chromatic* since both components can be limited independently.
/// - It is *inclusive*, since its [`Contains`] the limit itself.
/// - It is *upper* in the sense that it is a maximum value. It is not a minimum value.
/// - Is is *optional*, since it can set to `None` in which case it is *unlimited*.
#[derive(codec::Encode, codec::Decode, Copy, Clone, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct WeightLimit {
	/// An optional upper limit on the ref time component.
	pub ref_time: Option<u64>,

	/// An optional upper limit on the proof size component.
	pub proof_size: Option<u64>,
}

impl WeightLimit {
	/// The limit that only contains `Weight::zero()`.
	pub const NOTHING: WeightLimit = Self { ref_time: Some(0), proof_size: Some(0) };

	/// The limit that contains all possible `Weight`s.
	pub const UNLIMITED: WeightLimit = Self { ref_time: None, proof_size: None };

	/// The limit that only contains `Weight::zero()`.
	pub const fn nothing() -> Self {
		Self::NOTHING
	}

	pub const fn unlimited() -> Self {
		Self::UNLIMITED
	}

	pub const fn from_weight(weight: Weight) -> Self {
		Self { ref_time: Some(weight.ref_time), proof_size: Some(weight.proof_size) }
	}

	pub const fn from_limits(ref_time: Option<u64>, proof_size: Option<u64>) -> Self {
		Self { ref_time, proof_size }
	}

	pub const fn from_some_limits(ref_time: u64, proof_size: u64) -> Self {
		Self { ref_time: Some(ref_time), proof_size: Some(proof_size) }
	}

	pub const fn from_time_limit(ref_time: u64) -> Self {
		Self { ref_time: Some(ref_time), proof_size: None }
	}
	// `from_some_time_limit` omitted

	pub const fn from_proof_limit(proof_size: u64) -> Self {
		Self { ref_time: None, proof_size: Some(proof_size) }
	}
	// `from_some_proof_limit` omitted

	pub fn with_time_limit(mut self, ref_time: u64) -> Self {
		self.ref_time = Some(ref_time);
		self
	}

	pub fn with_proof_limit(mut self, proof_size: u64) -> Self {
		self.proof_size = Some(proof_size);
		self
	}

	// FAIL-CI: TODO try if const
	pub fn is_unlimited(&self) -> bool {
		self.ref_time.is_none() && self.proof_size.is_none()
	}

	pub fn is_all_unlimited(&self) -> bool {
		self.ref_time.is_none() && self.proof_size.is_none()
	}

	pub fn is_any_limited(&self) -> bool {
		self.ref_time.is_some() || self.proof_size.is_some()
	}

	pub fn is_all_limited(&self) -> bool {
		self.ref_time.is_some() && self.proof_size.is_some()
	}

	/// All components are zero.
	pub fn is_nothing(&self) -> bool {
		self.ref_time.map_or(false, |t| t.is_zero()) &&
			self.proof_size.map_or(false, |s| s.is_zero())
	}

	pub fn is_time_limited(&self) -> bool {
		self.ref_time.is_some()
	}

	pub fn is_proof_limited(&self) -> bool {
		self.proof_size.is_some()
	}

	pub fn is_time_unlimited(&self) -> bool {
		self.ref_time.is_none()
	}

	pub fn is_proof_unlimited(&self) -> bool {
		self.proof_size.is_none()
	}

	pub fn time_limit(&self) -> Option<u64> {
		self.ref_time
	}

	pub fn proof_limit(&self) -> Option<u64> {
		self.proof_size
	}

	pub fn all_gte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit >= weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit >= weight.proof_size)
	}

	pub fn all_gt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit > weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit > weight.proof_size)
	}

	pub fn all_lte(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit <= weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit <= weight.proof_size)
	}

	pub fn all_lt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(true, |limit| limit < weight.ref_time) &&
			self.proof_size.map_or(true, |limit| limit < weight.proof_size)
	}

	pub fn any_lt(&self, weight: &Weight) -> bool {
		self.ref_time.map_or(false, |limit| limit < weight.ref_time) ||
			self.proof_size.map_or(false, |limit| limit < weight.proof_size)
	}

	pub fn chromatic_min(&self, other: &WeightLimit) -> Self {
		Self {
			ref_time: self
				.ref_time
				.map_or(other.ref_time, |t| Some(t.min(other.ref_time.unwrap_or(u64::MAX)))),
			proof_size: self
				.proof_size
				.map_or(other.proof_size, |s| Some(s.min(other.proof_size.unwrap_or(u64::MAX)))),
		}
	}

	/// Uses the exact value for each *limited* component and `w` for each unlimited one.
	pub fn chromatic_limited_or(self, w: Weight) -> Weight {
		Weight {
			ref_time: self.ref_time.unwrap_or(w.ref_time),
			proof_size: self.proof_size.unwrap_or(w.proof_size),
		}
	}

	pub fn limited_or_max(self) -> Weight {
		self.chromatic_limited_or(Weight::MAX)
	}

	pub fn limited_or_min(self) -> Weight {
		self.chromatic_limited_or(Weight::zero())
	}

	pub fn saturating_sub(self, other: Weight) -> Self {
		Self {
			ref_time: self.ref_time.map(|t| t.saturating_sub(other.ref_time)),
			proof_size: self.proof_size.map(|s| s.saturating_sub(other.proof_size)),
		}
	}

	pub fn saturating_decrease(&mut self, other: Self) {
		self.ref_time = self.ref_time.map(|t| t.saturating_sub(other.ref_time.unwrap_or(0)));
		self.proof_size = self.proof_size.map(|s| s.saturating_sub(other.proof_size.unwrap_or(0)));
	}

	pub fn exact_limits(self) -> Option<Weight> {
		match (self.ref_time, self.proof_size) {
			(Some(t), Some(s)) => Some(Weight { ref_time: t, proof_size: s }),
			_ => None,
		}
	}

	pub fn check_within(&self, weight: Weight) -> Result<(), ()> {
		if self.all_gte(&weight) {
			Ok(())
		} else {
			Err(())
		}
	}
}

impl From<Weight> for WeightLimit {
	fn from(w: Weight) -> Self {
		Self::from_weight(w)
	}
}

macro_rules! weight_mul_per_impl {
	($($t:ty),* $(,)?) => {
		$(
			impl Mul<WeightLimit> for $t {
				type Output = WeightLimit;
				fn mul(self, b: WeightLimit) -> WeightLimit {
					WeightLimit {
						ref_time: b.ref_time.map(|t| self * t),
						proof_size: b.proof_size.map(|s| self * s),
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
