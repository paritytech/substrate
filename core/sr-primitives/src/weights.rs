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
//! Note that the decl_module macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

pub use crate::transaction_validity::TransactionPriority;
use crate::traits::Bounded;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// A broad range of dispatch types. This is only distinguishing normal, user-triggered transactions
/// and anything beyond which serves a higher purpose to the system (`OperationalNormal`).
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DispatchClass {
	/// A normal dispatch.
	User,
	/// An operational dispatch.
	Operational,
}

impl Default for DispatchClass {
	fn default() -> Self {
		DispatchClass::User
	}
}

impl From<SimpleDispatchInfo> for DispatchClass {
	fn from(tx: SimpleDispatchInfo) -> Self {
		match tx {
			SimpleDispatchInfo::OperationalNormal(_) => DispatchClass::Operational,
			SimpleDispatchInfo::FixedNormal(_) => DispatchClass::User,
			SimpleDispatchInfo::MaxNormal => DispatchClass::User,
			SimpleDispatchInfo::FreeNormal => DispatchClass::User,
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
#[derive(Clone, Copy)]
pub enum SimpleDispatchInfo {
	/// A fixed-weight dispatch function. No dependency on state or input.
	FixedNormal(Weight),
	/// An operational dispatch function. Still incurs a weight-fee but typically has a higher
	/// priority.
	OperationalNormal(Weight),
	/// A dispatch function with the maximum possible weight. This means:
	///   - The weight-fee will be maximum possible, based on the system state.
	///   - This transaction will also have a high priority (but not guaranteed to be included.)
	///   - If included, no more _normal_ dispatches will be permitted in that block. Operational
	///       dispatches might be included nonetheless.
	MaxNormal,
	/// Free. The transaction does not increase the total weight. This means:
	///   - No weight-fee is charged.
	///   - Block weight is not increased (very likely to be included, but not guaranteed).
	FreeNormal,
}

impl<T> WeighData<T> for SimpleDispatchInfo {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			SimpleDispatchInfo::FixedNormal(w) => *w,
			SimpleDispatchInfo::OperationalNormal(w) => *w,
			SimpleDispatchInfo::MaxNormal => Bounded::max_value(),
			SimpleDispatchInfo::FreeNormal => Bounded::min_value(),
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
		// This implies that the weight is currently equal to 100, nothing more
		// for all substrate transactions that do NOT explicitly annotate weight.
		// TODO #2431 needs to be updated with proper max values.
		SimpleDispatchInfo::FixedNormal(1)
	}
}
