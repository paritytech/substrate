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
//!  $x can be any object that implements the `Weighable` trait. By default, All transactions are
//! annotated by `#[weight = TransactionWeight::default()]`.
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail if an invalid struct
//! (something that does not  implement `Weighable`) is passed in.

use crate::{Fixed64, traits::Saturating};
use crate::codec::{Encode, Decode};

/// The final type that each `#[weight = $x:expr]`'s
/// expression must evaluate to.
pub type Weight = u32;

/// Maximum block saturation: 4mb
pub const MAX_TRANSACTIONS_WEIGHT: u32 = 4 * 1024 * 1024;
/// Target block saturation: 25% of max block saturation = 1mb
pub const IDEAL_TRANSACTIONS_WEIGHT: u32 = MAX_TRANSACTIONS_WEIGHT / 4;

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
