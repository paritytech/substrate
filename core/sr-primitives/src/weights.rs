// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Primitives for transaction weighting.
//!
//! Each dispatch function within `decl_module!` can have an optional `#[weight = $x]` attribute.
//! `$x` can be any type that implements the `ClassifyDispatch<T>` and `WeighData<T>` traits. By
//! default, All transactions are annotated with `#[weight = SimpleDispatchInfo::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail if an invalid struct
//! (something that does not  implement `Weighable`) is passed in.

use crate::{Fixed64, traits::Saturating};
use crate::codec::{Encode, Decode};

pub use crate::transaction_validity::TransactionPriority;
use crate::traits::Bounded;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// A generalized group of dispatch types. This is only distinguishing normal, user-triggered transactions
/// (`Normal`) and anything beyond which serves a higher purpose to the system (`Operational`).
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DispatchClass {
	/// A normal dispatch.
	Normal,
	/// An operational dispatch.
	Operational,
}

impl Default for DispatchClass {
	fn default() -> Self {
		DispatchClass::Normal
	}
}

impl From<SimpleDispatchInfo> for DispatchClass {
	fn from(tx: SimpleDispatchInfo) -> Self {
		match tx {
			SimpleDispatchInfo::FixedOperational(_) => DispatchClass::Operational,
			SimpleDispatchInfo::MaxOperational => DispatchClass::Operational,
			SimpleDispatchInfo::FreeOperational => DispatchClass::Operational,

			SimpleDispatchInfo::FixedNormal(_) => DispatchClass::Normal,
			SimpleDispatchInfo::MaxNormal => DispatchClass::Normal,
			SimpleDispatchInfo::FreeNormal => DispatchClass::Normal,
		}
	}
}

/// A bundle of static information collected from the `#[weight = $x]` attributes.
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Debug))]
#[derive(Clone, Copy, Default)]
pub struct DispatchInfo {
	/// Weight of this transaction.
	pub weight: Weight,
	/// Class of this transaction.
	pub class: DispatchClass,
}

impl DispatchInfo {
	/// Determine if this dispatch should pay the base length-related fee or not.
	pub fn pay_length_fee(&self) -> bool {
		match self.class {
			DispatchClass::Normal => true,
			// For now we assume all operational transactions don't pay the length fee.
			DispatchClass::Operational => false,
		}
	}
}

/// A `Dispatchable` function (aka transaction) that can carry some static information along with it, using the
/// `#[weight]` attribute.
pub trait GetDispatchInfo {
	/// Return a `DispatchInfo`, containing relevant information of this dispatch.
	///
	/// This is done independently of its encoded size.
	fn get_dispatch_info(&self) -> DispatchInfo;
}

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`.
	fn weigh_data(&self, target: T) -> Weight;
}

/// Means of classifying a dispatchable function.
pub trait ClassifyDispatch<T> {
	/// Classify the dispatch function based on input data `target` of type `T`.
	fn classify_dispatch(&self, target: T) -> DispatchClass;
}

/// Default type used with the `#[weight = x]` attribute in a substrate chain.
///
/// A user may pass in any other type that implements the correct traits. If not, the `Default`
/// implementation of [`SimpleDispatchInfo`] is used.
///
/// For each generalized group (`Normal` and `Operation`):
///   - A `Fixed` variant means weight fee is charged normally and the weight is the number
///      specified in the inner value of the variant.
///   - A `Free` variant is equal to `::Fixed(0)`. Note that this does not guarantee inclusion.
///   - A `Max` variant is equal to `::Fixed(Weight::max_value())`.
///
/// Based on the final weight value, based on the above variants:
///   - A _weight-fee_  is deducted.
///   - The block weight is consumed proportionally.
///
/// As for the generalized groups themselves:
///   - `Normal` variants will be assigned a priority proportional to their weight. They can only
///     consume a portion (1/4) of the maximum block resource limits.
///   - `Operational` variants will be assigned the maximum priority. They can potentially consume
///     the entire block resource limit.
#[derive(Clone, Copy)]
pub enum SimpleDispatchInfo {
	/// A normal dispatch with fixed weight.
	FixedNormal(Weight),
	/// A normal dispatch with the maximum weight.
	MaxNormal,
	/// A normal dispatch with no weight.
	FreeNormal,
	/// An operational dispatch with fixed weight.
	FixedOperational(Weight),
	/// An operational dispatch with the maximum weight.
	MaxOperational,
	/// An operational dispatch with no weight.
	FreeOperational,
}

impl<T> WeighData<T> for SimpleDispatchInfo {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			SimpleDispatchInfo::FixedNormal(w) => *w,
			SimpleDispatchInfo::MaxNormal => Bounded::max_value(),
			SimpleDispatchInfo::FreeNormal => Bounded::min_value(),

			SimpleDispatchInfo::FixedOperational(w) => *w,
			SimpleDispatchInfo::MaxOperational => Bounded::max_value(),
			SimpleDispatchInfo::FreeOperational => Bounded::min_value(),
		}
	}
}

impl<T> ClassifyDispatch<T> for SimpleDispatchInfo {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::from(*self)
	}
}

impl Default for SimpleDispatchInfo {
	fn default() -> Self {
		// Default weight of all transactions.
		SimpleDispatchInfo::FixedNormal(10_000)
	}
}

/// Representation of a weight multiplier. This represents how a fee value can be computed from a
/// weighted transaction.
///
/// This is basically a wrapper for the `Fixed64` type a slightly tailored multiplication to u32
/// in the form of the `apply_to` method.
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct WeightMultiplier(Fixed64);

impl WeightMultiplier {
	/// Apply the inner Fixed64 as a weight multiplier to a weight value.
	///
	/// This will perform a saturated  `weight + weight * self.0`.
	pub fn apply_to(&self, weight: Weight) -> Weight {
		self.0.saturated_multiply_accumulate(weight)
	}

	/// build self from raw parts per billion.
	#[cfg(feature = "std")]
	pub fn from_parts(parts: i64) -> Self {
		Self(Fixed64(parts))
	}

	/// build self from a fixed64 value.
	pub fn from_fixed(f: Fixed64) -> Self {
		Self(f)
	}

	/// Approximate the fraction `n/d`.
	pub fn from_rational(n: i64, d: u64) -> Self {
		Self(Fixed64::from_rational(n, d))
	}
}

impl Saturating for WeightMultiplier {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}
	fn saturating_mul(self, rhs: Self) -> Self {
		Self(self.0.saturating_mul(rhs.0))

	}
	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn multiplier_apply_to_works() {
		let test_set = vec![0, 1, 10, 1000, 1_000_000_000];

		// negative (1/2)
		let mut fm = WeightMultiplier::from_rational(-1, 2);
		test_set.clone().into_iter().for_each(|i| { assert_eq!(fm.apply_to(i) as i32, i as i32  - i as i32 / 2); });

		// unit (1) multiplier
		fm = WeightMultiplier::from_parts(0);
		test_set.clone().into_iter().for_each(|i| { assert_eq!(fm.apply_to(i), i); });

		// i.5 multiplier
		fm = WeightMultiplier::from_rational(1, 2);
		test_set.clone().into_iter().for_each(|i| { assert_eq!(fm.apply_to(i), i * 3 / 2); });

		// dual multiplier
		fm = WeightMultiplier::from_rational(1, 1);
		test_set.clone().into_iter().for_each(|i| { assert_eq!(fm.apply_to(i), i * 2); });
	}
}
