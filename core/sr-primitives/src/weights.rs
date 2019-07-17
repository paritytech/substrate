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
//! default, All transactions are annotated by `#[weight = TransactionWeight::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

pub use crate::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// A broad range of dispatch types. This is only distinguishing normal, user-triggered transactions
/// and anything beyond which serves a higher purpose to the system (`Operational`).
#[derive(Clone, Copy)]
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

impl From<&TransactionWeight> for DispatchClass {
	fn from(tx: &TransactionWeight) -> Self {
		match *tx {
			TransactionWeight::Operational(_) => DispatchClass::Operational,
			TransactionWeight::Fixed(_) => DispatchClass::User,
		}
	}
}

/// A bundle of static meta information collected from the `#[weight = $x]` meta tags.
#[derive(Clone, Copy, Default)]
pub struct TransactionInfo {
	/// Weight of this transaction.
	pub weight: Weight,
	/// Class of this transaction.
	pub class: DispatchClass,
}

/// A `Call` enum (aka transaction) that can be weighted using the custom weight attribute of
/// its dispatchable functions. Is implemented by default in the `decl_module!`.
///
/// Both the outer Call enum and the per-module individual ones will implement this.
/// The outer enum simply calls the inner ones based on call type.
// TODO: rename this to sth that says: this traits returns a bunch of static meta-information about
// the tx, including but NOT only weight. Also rename #[weight] to #[meta]?
pub trait Weigh {
	/// Return the (weight, priority) of this call. This is done independently of its encoded size.
	fn weigh(&self) -> TransactionInfo;
}

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`.
	fn weigh_data(&self, target: T) -> Weight;
}

/// Means of classifying a transaction.
pub trait ClassifyDispatch<T> {
	/// Classify transaction based on input data `target`.
	fn class(&self, target: T) -> DispatchClass;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements the correct traits. If not, the `Default`
/// implementation of [`TransactionWeight`] is used.
pub enum TransactionWeight {
	/// A fixed-weight transaction. No dependency on state or input.
	Fixed(Weight),
	/// An operational transaction.
	Operational(Weight),
}

impl<T> WeighData<T> for TransactionWeight {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			TransactionWeight::Fixed(w) => *w,
			TransactionWeight::Operational(w) => *w,
		}
	}
}

impl<T> ClassifyDispatch<T> for TransactionWeight {
	fn class(&self, _: T) -> DispatchClass {
		DispatchClass::from(self)
	}
}

impl Default for TransactionWeight {
	fn default() -> Self {
		// This implies that the weight is currently equal to 100, nothing more
		// for all substrate transactions that do NOT explicitly annotate weight.
		// TODO #2431 needs to be updated with proper max values.
		TransactionWeight::Fixed(1)
	}
}
