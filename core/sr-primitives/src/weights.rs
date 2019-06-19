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

/// The final type that each `#[weight = $x:expr]`'s
/// expression must evaluate to.
pub type Weight = u32;

/// A `Call` enum (aka transaction) that can be weighted using the custom weight attribute of
/// its dispatchable functions. Is implemented by default in the `decl_module!`.
///
/// Both the outer Call enum and the per-module individual ones will implement this.
/// The outer enum simply calls the inner ones based on call type.
pub trait Weighable {
	/// Return the weight of this call.
	/// The `len` argument is the encoded length of the transaction/call.
	fn weight(&self, len: usize) -> Weight;
}

/// Default type used as the weight representative in a `#[weight = x]` attribute.
///
/// A user may pass in any other type that implements [`Weighable`]. If not, the `Default`
/// implementation of [`TransactionWeight`] is used.
pub enum TransactionWeight {
	/// Basic weight (base, byte).
	/// The values contained are the base weight and byte weight respectively.
	Basic(Weight, Weight),
	/// Maximum fee. This implies that this transaction _might_ get included but
	/// no more transaction can be added. This can be done by setting the
	/// implementation to _maximum block weight_.
	Max,
	/// Free. The transaction does not increase the total weight
	/// (i.e. is not included in weight calculation).
	Free,
}

impl Weighable for TransactionWeight {
	fn weight(&self, len: usize) -> Weight {
		match self {
			TransactionWeight::Basic(base, byte) => base + byte * len as Weight,
			TransactionWeight::Max => 3 * 1024 * 1024,
			TransactionWeight::Free => 0,
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
