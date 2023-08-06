// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Types and helpers to define and handle election bounds.
//!
//! ### Overview
//!
//! This module defines and implements types that help creating and handling election bounds.
//! [`DataProviderBounds`] encapsulates the upper limits for the results provided by `DataProvider`
//! implementors. Those limits can be defined over two axis: number of elements returned (`count`)
//! and/or the size of the returned SCALE encoded structure (`size`).
//!
//! [`ElectionBoundsBuilder`] is a helper to construct data election bounds and it aims at
//! preventing the caller from mistake the order of size and count limits.
//!
//! ### Examples
//!
//! [`ElectionBoundsBuilder`] helps defining the size and count bounds for both voters and targets.
//!
//! ```
//! use frame_election_provider_support::bounds::*;
//!
//! // unbounded limits are never exhausted.
//! let unbounded = ElectionBoundsBuilder::default().build();
//! assert!(!unbounded.targets.exhausted(SizeBound(1_000_000_000).into(), None));
//!
//! let bounds = ElectionBoundsBuilder::default()
//!     .voters_count(100.into())
//!     .voters_size(1_000.into())
//!     .targets_count(200.into())
//!     .targets_size(2_000.into())
//!     .build();
//!
//! assert!(!bounds.targets.exhausted(SizeBound(1).into(), CountBound(1).into()));
//! assert!(bounds.targets.exhausted(SizeBound(1).into(), CountBound(100_000).into()));
//! ```
//!
//! ### Implementation details
//!
//! A default or `None` bound means that no bounds are enforced (i.e. unlimited result size). In
//! general, be careful when using unbounded election bounds in production.

use core::ops::Add;
use sp_runtime::traits::Zero;

/// Count type for data provider bounds.
///
/// Encapsulates the counting of things that can be bounded in an election, such as voters,
/// targets or anything else.
///
/// This struct is defined mostly to prevent callers from mistankingly using `CountBound` instead of
/// `SizeBound` and vice-versa.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CountBound(pub u32);

impl From<u32> for CountBound {
	fn from(value: u32) -> Self {
		CountBound(value)
	}
}

impl Add for CountBound {
	type Output = Self;
	fn add(self, rhs: Self) -> Self::Output {
		CountBound(self.0.saturating_add(rhs.0))
	}
}

impl Zero for CountBound {
	fn is_zero(&self) -> bool {
		self.0 == 0u32
	}
	fn zero() -> Self {
		CountBound(0)
	}
}

/// Size type for data provider bounds.
///
/// Encapsulates the size limit of things that can be bounded in an election, such as voters,
/// targets or anything else. The size unit can represent anything depending on the election
/// logic and implementation, but it most likely will represent bytes in SCALE encoding in this
/// context.
///
/// This struct is defined mostly to prevent callers from mistankingly using `CountBound` instead of
/// `SizeBound` and vice-versa.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SizeBound(pub u32);

impl From<u32> for SizeBound {
	fn from(value: u32) -> Self {
		SizeBound(value)
	}
}

impl Zero for SizeBound {
	fn is_zero(&self) -> bool {
		self.0 == 0u32
	}
	fn zero() -> Self {
		SizeBound(0)
	}
}

impl Add for SizeBound {
	type Output = Self;
	fn add(self, rhs: Self) -> Self::Output {
		SizeBound(self.0.saturating_add(rhs.0))
	}
}

/// Data bounds for election data.
///
/// Limits the data returned by `DataProvider` implementors, defined over two axis: `count`,
/// defining the maximum number of elements returned, and `size`, defining the limit in size
/// (bytes) of the SCALE encoded result.
///
/// `None` represents unlimited bounds in both `count` and `size` axis.
#[derive(Clone, Copy, Default, Debug, Eq, PartialEq)]
pub struct DataProviderBounds {
	pub count: Option<CountBound>,
	pub size: Option<SizeBound>,
}

impl DataProviderBounds {
	///  Returns true if `given_count` exhausts `self.count`.
	pub fn count_exhausted(self, given_count: CountBound) -> bool {
		self.count.map_or(false, |count| given_count > count)
	}

	///  Returns true if `given_size` exhausts `self.size`.
	pub fn size_exhausted(self, given_size: SizeBound) -> bool {
		self.size.map_or(false, |size| given_size > size)
	}

	/// Returns true if `given_size` or `given_count` exhausts `self.size` or `self_count`,
	/// respectively.
	pub fn exhausted(self, given_size: Option<SizeBound>, given_count: Option<CountBound>) -> bool {
		self.count_exhausted(given_count.unwrap_or(CountBound::zero())) ||
			self.size_exhausted(given_size.unwrap_or(SizeBound::zero()))
	}

	/// Returns an instance of `Self` that is constructed by capping both the `count` and `size`
	/// fields. If `self` is None, overwrite it with the provided bounds.
	pub fn max(self, bounds: DataProviderBounds) -> Self {
		DataProviderBounds {
			count: self
				.count
				.map(|c| {
					c.clamp(CountBound::zero(), bounds.count.unwrap_or(CountBound(u32::MAX))).into()
				})
				.or(bounds.count),
			size: self
				.size
				.map(|c| {
					c.clamp(SizeBound::zero(), bounds.size.unwrap_or(SizeBound(u32::MAX))).into()
				})
				.or(bounds.size),
		}
	}
}

/// The voter and target bounds of an election.
///
/// The bounds are defined over two axis: `count` of element of the election (voters or targets) and
/// the `size` of the SCALE encoded result snapshot.
#[derive(Clone, Debug, Copy)]
pub struct ElectionBounds {
	pub voters: DataProviderBounds,
	pub targets: DataProviderBounds,
}

impl ElectionBounds {
	/// Returns an error if the provided `count` and `size` do not fit in the voter's election
	/// bounds.
	pub fn ensure_voters_limits(
		self,
		count: CountBound,
		size: SizeBound,
	) -> Result<(), &'static str> {
		match self.voters.exhausted(Some(size), Some(count)) {
			true => Err("Ensure voters bounds: bounds exceeded."),
			false => Ok(()),
		}
	}

	/// Returns an error if the provided `count` and `size` do not fit in the target's election
	/// bounds.
	pub fn ensure_targets_limits(
		self,
		count: CountBound,
		size: SizeBound,
	) -> Result<(), &'static str> {
		match self.targets.exhausted(Some(size), Some(count).into()) {
			true => Err("Ensure targets bounds: bounds exceeded."),
			false => Ok(()),
		}
	}
}

/// Utility builder for [`ElectionBounds`].
#[derive(Copy, Clone, Default)]
pub struct ElectionBoundsBuilder {
	voters: Option<DataProviderBounds>,
	targets: Option<DataProviderBounds>,
}

impl From<ElectionBounds> for ElectionBoundsBuilder {
	fn from(bounds: ElectionBounds) -> Self {
		ElectionBoundsBuilder { voters: Some(bounds.voters), targets: Some(bounds.targets) }
	}
}

impl ElectionBoundsBuilder {
	/// Sets the voters count bounds.
	pub fn voters_count(mut self, count: CountBound) -> Self {
		self.voters = self.voters.map_or(
			Some(DataProviderBounds { count: Some(count), size: None }),
			|mut bounds| {
				bounds.count = Some(count);
				Some(bounds)
			},
		);
		self
	}

	/// Sets the voters size bounds.
	pub fn voters_size(mut self, size: SizeBound) -> Self {
		self.voters = self.voters.map_or(
			Some(DataProviderBounds { count: None, size: Some(size) }),
			|mut bounds| {
				bounds.size = Some(size);
				Some(bounds)
			},
		);
		self
	}

	/// Sets the targets count bounds.
	pub fn targets_count(mut self, count: CountBound) -> Self {
		self.targets = self.targets.map_or(
			Some(DataProviderBounds { count: Some(count), size: None }),
			|mut bounds| {
				bounds.count = Some(count);
				Some(bounds)
			},
		);
		self
	}

	/// Sets the targets size bounds.
	pub fn targets_size(mut self, size: SizeBound) -> Self {
		self.targets = self.targets.map_or(
			Some(DataProviderBounds { count: None, size: Some(size) }),
			|mut bounds| {
				bounds.size = Some(size);
				Some(bounds)
			},
		);
		self
	}

	/// Set the voters bounds.
	pub fn voters(mut self, bounds: Option<DataProviderBounds>) -> Self {
		self.voters = bounds;
		self
	}

	/// Set the targets bounds.
	pub fn targets(mut self, bounds: Option<DataProviderBounds>) -> Self {
		self.targets = bounds;
		self
	}

	/// Caps the number of the voters bounds in self to `voters` bounds. If `voters` bounds are
	/// higher than the self bounds, keeps it. Note that `None` bounds are equivalent to maximum
	/// and should be treated as such.
	pub fn voters_or_lower(mut self, voters: DataProviderBounds) -> Self {
		self.voters = match self.voters {
			None => Some(voters),
			Some(v) => Some(v.max(voters)),
		};
		self
	}

	/// Caps the number of the target bounds in self to `voters` bounds. If `voters` bounds are
	/// higher than the self bounds, keeps it. Note that `None` bounds are equivalent to maximum
	/// and should be treated as such.
	pub fn targets_or_lower(mut self, targets: DataProviderBounds) -> Self {
		self.targets = match self.targets {
			None => Some(targets),
			Some(t) => Some(t.max(targets)),
		};
		self
	}

	/// Returns an instance of `ElectionBounds` from the current state.
	pub fn build(self) -> ElectionBounds {
		ElectionBounds {
			voters: self.voters.unwrap_or_default(),
			targets: self.targets.unwrap_or_default(),
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;

	use frame_support::{assert_err, assert_ok};

	#[test]
	fn data_provider_bounds_unbounded_works() {
		let bounds = DataProviderBounds::default();
		assert!(!bounds.exhausted(None, None));
		assert!(!bounds.exhausted(SizeBound(u32::MAX).into(), CountBound(u32::MAX).into()));
	}

	#[test]
	fn election_bounds_builder_and_exhausted_bounds_work() {
		// voter bounds exhausts if count > 100 or size > 1_000; target bounds exhausts if count >
		// 200 or size > 2_000.
		let bounds = ElectionBoundsBuilder::default()
			.voters_count(100.into())
			.voters_size(1_000.into())
			.targets_count(200.into())
			.targets_size(2_000.into())
			.build();

		assert!(!bounds.voters.exhausted(None, None));
		assert!(!bounds.voters.exhausted(SizeBound(10).into(), CountBound(10).into()));
		assert!(!bounds.voters.exhausted(None, CountBound(100).into()));
		assert!(!bounds.voters.exhausted(SizeBound(1_000).into(), None));
		// exhausts bounds.
		assert!(bounds.voters.exhausted(None, CountBound(101).into()));
		assert!(bounds.voters.exhausted(SizeBound(1_001).into(), None));

		assert!(!bounds.targets.exhausted(None, None));
		assert!(!bounds.targets.exhausted(SizeBound(20).into(), CountBound(20).into()));
		assert!(!bounds.targets.exhausted(None, CountBound(200).into()));
		assert!(!bounds.targets.exhausted(SizeBound(2_000).into(), None));
		// exhausts bounds.
		assert!(bounds.targets.exhausted(None, CountBound(201).into()));
		assert!(bounds.targets.exhausted(SizeBound(2_001).into(), None));
	}

	#[test]
	fn election_bounds_ensure_limits_works() {
		let bounds = ElectionBounds {
			voters: DataProviderBounds { count: Some(CountBound(10)), size: Some(SizeBound(10)) },
			targets: DataProviderBounds { count: Some(CountBound(10)), size: Some(SizeBound(10)) },
		};

		assert_ok!(bounds.ensure_voters_limits(CountBound(1), SizeBound(1)));
		assert_ok!(bounds.ensure_voters_limits(CountBound(1), SizeBound(1)));
		assert_ok!(bounds.ensure_voters_limits(CountBound(10), SizeBound(10)));
		assert_err!(
			bounds.ensure_voters_limits(CountBound(1), SizeBound(11)),
			"Ensure voters bounds: bounds exceeded."
		);
		assert_err!(
			bounds.ensure_voters_limits(CountBound(11), SizeBound(10)),
			"Ensure voters bounds: bounds exceeded."
		);

		assert_ok!(bounds.ensure_targets_limits(CountBound(1), SizeBound(1)));
		assert_ok!(bounds.ensure_targets_limits(CountBound(1), SizeBound(1)));
		assert_ok!(bounds.ensure_targets_limits(CountBound(10), SizeBound(10)));
		assert_err!(
			bounds.ensure_targets_limits(CountBound(1), SizeBound(11)),
			"Ensure targets bounds: bounds exceeded."
		);
		assert_err!(
			bounds.ensure_targets_limits(CountBound(11), SizeBound(10)),
			"Ensure targets bounds: bounds exceeded."
		);
	}

	#[test]
	fn data_provider_max_unbounded_works() {
		let unbounded = DataProviderBounds::default();

		// max of some bounds with unbounded data provider bounds will always return the defined
		// bounds.
		let bounds = DataProviderBounds { count: CountBound(5).into(), size: SizeBound(10).into() };
		assert_eq!(unbounded.max(bounds), bounds);

		let bounds = DataProviderBounds { count: None, size: SizeBound(10).into() };
		assert_eq!(unbounded.max(bounds), bounds);

		let bounds = DataProviderBounds { count: CountBound(5).into(), size: None };
		assert_eq!(unbounded.max(bounds), bounds);
	}

	#[test]
	fn data_provider_max_bounded_works() {
		let bounds_one =
			DataProviderBounds { count: CountBound(10).into(), size: SizeBound(100).into() };
		let bounds_two =
			DataProviderBounds { count: CountBound(100).into(), size: SizeBound(10).into() };
		let max_bounds_expected =
			DataProviderBounds { count: CountBound(10).into(), size: SizeBound(10).into() };

		assert_eq!(bounds_one.max(bounds_two), max_bounds_expected);
		assert_eq!(bounds_two.max(bounds_one), max_bounds_expected);
	}

	#[test]
	fn election_bounds_clamp_works() {
		let bounds = ElectionBoundsBuilder::default()
			.voters_count(10.into())
			.voters_size(10.into())
			.voters_or_lower(DataProviderBounds {
				count: CountBound(5).into(),
				size: SizeBound(20).into(),
			})
			.targets_count(20.into())
			.targets_or_lower(DataProviderBounds {
				count: CountBound(30).into(),
				size: SizeBound(30).into(),
			})
			.build();

		assert_eq!(bounds.voters.count.unwrap(), CountBound(5));
		assert_eq!(bounds.voters.size.unwrap(), SizeBound(10));
		assert_eq!(bounds.targets.count.unwrap(), CountBound(20));
		assert_eq!(bounds.targets.size.unwrap(), SizeBound(30));

		// note that unbounded bounds (None) are equivalent to maximum value.
		let bounds = ElectionBoundsBuilder::default()
			.voters_or_lower(DataProviderBounds {
				count: CountBound(5).into(),
				size: SizeBound(20).into(),
			})
			.targets_or_lower(DataProviderBounds {
				count: CountBound(10).into(),
				size: SizeBound(10).into(),
			})
			.build();

		assert_eq!(bounds.voters.count.unwrap(), CountBound(5));
		assert_eq!(bounds.voters.size.unwrap(), SizeBound(20));
		assert_eq!(bounds.targets.count.unwrap(), CountBound(10));
		assert_eq!(bounds.targets.size.unwrap(), SizeBound(10));
	}
}
