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

//! The Polkadot runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
extern crate substrate_misbehavior_check as misbehavior_check;
extern crate polkadot_primitives;

#[cfg(all(feature = "std", test))]
extern crate substrate_keyring as keyring;

#[cfg(feature = "std")]
extern crate rustc_hex;

#[cfg_attr(any(test, feature = "std"), macro_use)]
extern crate substrate_primitives as primitives;

#[macro_use]
extern crate substrate_runtime_io as runtime_io;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

pub mod api;
pub mod environment;
pub mod runtime;

#[cfg(feature = "std")]
pub mod genesismap;

/// Type definitions and helpers for transactions.
pub mod transaction {
	use rstd::ops;
	use polkadot_primitives::Signature;
	pub use polkadot_primitives::{Transaction, Function, UncheckedTransaction};

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

	/// Check the validity of a transaction: whether it can appear at the given index
	/// and whether it is correctly authenticated.
	pub fn check(tx: UncheckedTransaction, index: u64) -> Result<CheckedTransaction, UncheckedTransaction> {
		match tx.transaction.function.inherent_index() {
			Some(correct_index) => {
				if index != correct_index || !tx.is_well_formed() { return Err(tx) }
				return Ok(CheckedTransaction(tx));
			}
			None => {
				// non-inherent functions must appear after inherent.
				if index < Function::inherent_functions() { return Err(tx) }
			}
		}

		let msg = ::codec::Slicable::encode(&tx.transaction);
		if ::runtime_io::ed25519_verify(&tx.signature.0, &msg, &tx.transaction.signed) {
			Ok(CheckedTransaction(tx))
		} else {
			Err(tx)
		}
	}
}
