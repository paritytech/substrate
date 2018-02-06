// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#![cfg_attr(feature = "std", doc = "Polkadot runtime standard library as compiled when linked with Rust's standard library.")]
#![cfg_attr(not(feature = "std"), doc = "Polkadot's runtime standard library as compiled without Rust's standard library.")]

extern crate polkadot_runtime_codec as codec;

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

/// Prelude of common useful imports.
///
/// This should include only things which are in the normal std prelude.
pub mod prelude {
	pub use ::vec::Vec;
	pub use ::boxed::Box;
}

/// Type definitions and helpers for transactions.
pub mod transaction {
	pub use primitives::relay::{Transaction, UncheckedTransaction};
	use primitives::Signature;

	#[cfg(feature = "std")]
	use std::ops;

	#[cfg(not(feature = "std"))]
	use core::ops;

	/// A type-safe indicator that a transaction has been checked.
	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Debug))]
	pub struct CheckedTransaction(UncheckedTransaction);

	impl CheckedTransaction {
		/// Get a reference to the checked signature.
		pub fn signature(&self) -> &Signature {
			&self.0.signature
		}
	}

	impl ops::Deref for CheckedTransaction {
		type Target = Transaction;

		fn deref(&self) -> &Transaction {
			&self.0.transaction
		}
	}

	/// Check the signature on a transaction.
	///
	/// On failure, return the transaction back.
	pub fn check(tx: UncheckedTransaction) -> Result<CheckedTransaction, UncheckedTransaction> {
		let msg = ::codec::Slicable::to_vec(&tx.transaction);
		if ::ed25519_verify(&tx.signature.0, &msg, &tx.transaction.signed) {
			Ok(CheckedTransaction(tx))
		} else {
			Err(tx)
		}
	}
}

