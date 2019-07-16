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

//! Primitives for call metadata.
//!
//! Each dispatch function within `decl_module!` can have an optional
//! `#[meta = $x]` attribute. $x can be any object that implements the
//! `CallMetadata` trait. By default, All transactions are annotated by
//! `#[weight = WeightedTransaction::default()]`.
//!
//! Note that the `decl_module` macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

use crate::traits::{Zero, Bounded};
use crate::transaction_validity::TransactionPriority;

/// The numeric representation of a transaction weight.
pub type Weight = u32;

/// A bundle of the types that must be included in the call metadata.
pub type CallDescriptor = (Weight, TransactionPriority);

/// A `Call` enum (aka transaction) that can carry a set of static information to the executive and
/// subsequent execution paths.
///
/// To be included, each `Call` function must include the `$[meta = $x]` attribute where `$x` can be
/// any type that implements the `TransactionInfo` trait.
pub trait CallMetadata {
	/// Return the weight of this call.
	/// The `len` argument is the encoded length of the transaction/call.
	fn info(&self, len: usize) -> CallDescriptor;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements [`CallMetadata`]. If not, the `Default`
/// implementation of [`WeightedTransaction`] is used.
pub enum WeightedTransaction {
	/// Basic weight (base, byte).
	/// The values contained are the base weight and byte weight respectively.
	Basic(Weight, Weight),
	/// An operational transaction (sudo calls, runtime upgrades, democracy actions). These will
	/// incur no additional weight and will always have maximum priority.
	Operational(Weight, Weight)
}

impl CallMetadata for WeightedTransaction {
	fn info(&self, len: usize) -> CallDescriptor {
		let weight = match self {
			WeightedTransaction::Basic(base, byte) => base + byte * len as Weight,
			WeightedTransaction::Operational(_, _) => Zero::zero(),
		};
		let priority: TransactionPriority = match self {
			WeightedTransaction::Basic(_, _) => weight.into(),
			WeightedTransaction::Operational(_, _) => Bounded::max_value()
		};
		(weight, priority)
	}
}

impl Default for WeightedTransaction {
	fn default() -> Self {
		// This implies that the weight is currently equal to tx-size, nothing more
		// for all substrate transactions that do NOT explicitly annotate weight.
		// TODO #2431 needs to be updated with proper max values.
		WeightedTransaction::Basic(0, 1)
	}
}
