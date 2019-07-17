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
//! Each dispatch function within `decl_module!` can have an optional `#[weight = $x]` attribute. $x
//! can be any object that implements the `ClassifyDispatch<T>` and `WeighData<T>` traits. By
//! default, All transactions are annotated by `#[weight = WeightedTransaction::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

pub use crate::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// A broad range of dispatch types. This is only distinguishing normal, user-triggered transactions
/// and anything beyond which serves a higher purpose to the system (`Operational`).
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

impl From<&WeightedTransaction> for DispatchClass {
	fn from(tx: &WeightedTransaction) -> Self {
		match *tx {
			WeightedTransaction::Operational(_) => DispatchClass::Operational,
			WeightedTransaction::Fixed(_) => DispatchClass::User,
		}
	}
}

/// A bundle of static meta information collected from the `#[weight = $x]` tags.
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Debug))]
#[derive(Clone, Copy, Default)]
pub struct TransactionInfo {
	/// Weight of this transaction.
	pub weight: Weight,
	/// Class of this transaction.
	pub class: DispatchClass,
}

/// A `Call` enum (aka transaction) that can be carry some static information along with it using
/// the `#[weight]` tag.
pub trait DispatchInfo {
	/// Return a `TransactionInfo`, containing relevant information of this call.
	///
	/// This is done independently of its encoded size.
	fn dispatch_info(&self) -> TransactionInfo;
}

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`.
	fn weigh_data(&self, target: T) -> Weight;
}

/// Means of classifying a transaction.
pub trait ClassifyDispatch<T> {
	/// Classify transaction based on input data `target`.
	fn classify_dispatch(&self, target: T) -> DispatchClass;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements the correct traits. If not, the `Default`
/// implementation of [`WeightedTransaction`] is used.
pub enum WeightedTransaction {
	/// A fixed-weight transaction. No dependency on state or input.
	Fixed(Weight),
	/// An operational transaction.
	Operational(Weight),
}

impl<T> WeighData<T> for WeightedTransaction {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			WeightedTransaction::Fixed(w) => *w,
			WeightedTransaction::Operational(w) => *w,
		}
	}
}

impl<T> ClassifyDispatch<T> for WeightedTransaction {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::from(self)
	}
}

impl Default for WeightedTransaction {
	fn default() -> Self {
		// This implies that the weight is currently equal to 100, nothing more
		// for all substrate transactions that do NOT explicitly annotate weight.
		// TODO #2431 needs to be updated with proper max values.
		WeightedTransaction::Fixed(1)
	}
}
