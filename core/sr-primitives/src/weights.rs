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
//! Each dispatch function within `decl_module!` can now have an optional
//! `#[weight = $x]` attribute. $x can be any object that implements the
//! `Weigh` trait. By default, All transactions are annotated by
//! `#[weight = TransactionWeight::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

pub use crate::transaction_validity::TransactionPriority;
use crate::traits::Bounded;

pub type Weight = u32;

#[derive(Copy, Clone, Default)]
pub struct TransactionInfo {
	pub weight: Weight,
	pub priority: TransactionPriority,
	pub is_operational: bool,
}

impl TransactionInfo {
	pub fn will_cause_full_block(&self,
		current_weight: Weight,
		maximum_weight: Weight,
	) -> bool {
		let new_weight = current_weight.saturating_add(self.weight);
		let limit = if self.is_operational { maximum_weight / 4 } else { maximum_weight };
		new_weight > limit
	}
}

/// A `Call` enum (aka transaction) that can be weighted using the custom weight attribute of
/// its dispatchable functions. Is implemented by default in the `decl_module!`.
///
/// Both the outer Call enum and the per-module individual ones will implement this.
/// The outer enum simply calls the inner ones based on call type.
// TODO: rename this to sth that says: this traits returns a bunch of static meta-information about the tx,
// including but NOT only weight.
pub trait Weigh {
	/// Return the (weight, priority) of this call. This is done independently of its encoded size.
	fn weigh(&self) -> TransactionInfo;
}

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`.
	fn weigh_data(&self, target: T) -> Weight;
}

/// Means of prioritizing some transaction based on the input `T`.
pub trait PrioritizeData<T> {
	/// Compute the priority.
	fn prioritize(&self, target: T) -> TransactionPriority;
}

pub trait IsOperational<T> {
	fn is_operational(&self, targer: T) -> bool;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements [`Weigh`]. If not, the `Default`
/// implementation of [`TransactionWeight`] is used.
pub enum TransactionWeight {
	/// Basic weight (base, byte).
	/// The values contained are the base weight and byte weight respectively.
	Fixed(Weight),
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

impl<T> IsOperational<T> for TransactionWeight {
	fn is_operational(&self, _: T) -> bool {
		match self {
			TransactionWeight::Fixed(_) => false,
			TransactionWeight::Operational(_) => true,
		}
	}
}

impl<T> PrioritizeData<T> for TransactionWeight {
	fn prioritize(&self, _: T) -> TransactionPriority {
		match self {
			TransactionWeight::Fixed(w) => TransactionPriority::from(*w),
			TransactionWeight::Operational(_) => Bounded::max_value(),
		}
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
