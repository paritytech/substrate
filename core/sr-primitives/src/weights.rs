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
//! `Weighable` trait. By default, All transactions are annotated by
//! `#[weight = TransactionWeight::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail
//! if an invalid struct is passed in.

use crate::transaction_validity::TransactionPriority;

/// The final type that each `#[weight = $x:expr]`'s
/// expression must evaluate to.
pub type Weight = u32;

/// The maximum possible weight of a block.
pub const MAX_TRANSACTIONS_WEIGHT: u32 = 4 * 1024 * 1024;

/// A `Call` enum (aka transaction) that can be weighted using the custom weight attribute of
/// its dispatchable functions. Is implemented by default in the `decl_module!`.
///
/// Both the outer Call enum and the per-module individual ones will implement this.
/// The outer enum simply calls the inner ones based on call type.
pub trait Weighable {
	/// Return the weight of this call.
	/// The `len` argument is the encoded length of the transaction/call.
	fn weight(&self, len: usize) -> Weight;

	/// Return the priority of this transaction.
	fn priority(&self, len: usize) -> TransactionPriority;

	/// Determine, given the current transaction weight and sum of weights in the current block, if
	/// the block is now full or not.
	fn is_block_full(&self, block_weight: Weight, len: usize) -> bool;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements [`Weighable`]. If not, the `Default`
/// implementation of [`TransactionWeight`] is used.
pub enum TransactionWeight {
	/// Basic weight (base, byte).
	/// The values contained are the base weight and byte weight respectively.
	///
	/// The priority of this transaction will be proportional to its computed weight.
	Basic(Weight, Weight),
	/// Operational transaction. These are typically root transactions for operational updates,
	/// runtime code changes or consensus reports through inherents. These transactions are still
	/// subject to the same (base, byte) fee but will have maximum priority and will not affect
	/// block fullness at all.
	Operational(Weight, Weight),
}

impl Weighable for TransactionWeight {
	fn weight(&self, len: usize) -> Weight {
		match self {
			TransactionWeight::Basic(base, byte) => base + byte * len as Weight,
			TransactionWeight::Operational(_, _) => 0,
		}
	}

	fn priority(&self, len: usize) -> TransactionPriority {
		match self {
			TransactionWeight::Basic(_, _) => self.weight(len) as TransactionPriority,
			TransactionWeight::Operational(_, _) => TransactionPriority::max_value(),
		}
	}

	fn is_block_full(&self, block_weight: Weight, len: usize) -> bool {
		match self {
			TransactionWeight::Basic(_, _) => self.weight(len) + block_weight > MAX_TRANSACTIONS_WEIGHT,
			TransactionWeight::Operational(_, _) => false
		}
	}
}

impl Default for TransactionWeight {
	fn default() -> Self {
		// This implies that the weight is currently equal to tx-size, nothing more
		// for all substrate transactions that do NOT explicitly annotate weight.
		// TODO #2431 needs to be updated with proper max values.
		TransactionWeight::Basic(0, 1)
	}
}
