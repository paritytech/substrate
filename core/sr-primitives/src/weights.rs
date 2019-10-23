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

use arithmetic::traits::Bounded;
use crate::RuntimeDebug;

pub use crate::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// A generalized group of dispatch types. This is only distinguishing normal, user-triggered transactions
/// (`Normal`) and anything beyond which serves a higher purpose to the system (`Operational`).
#[derive(PartialEq, Eq, Clone, Copy, RuntimeDebug)]
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
#[cfg_attr(feature = "std", derive(PartialEq, Eq))]
#[derive(Clone, Copy, Default, RuntimeDebug)]
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
