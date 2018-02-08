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

#[macro_use]
extern crate substrate_runtime_io as runtime_io;

#[cfg(feature = "std")]
extern crate rustc_hex;

extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate polkadot_primitives;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
pub mod support;
pub mod runtime;

#[cfg(feature = "std")]
pub mod genesismap;

use rstd::prelude::*;
use codec::Slicable;
use polkadot_primitives::{Header, Block, UncheckedTransaction};

/// Type definitions and helpers for transactions.
pub mod transaction {
	use rstd::ops;
	use polkadot_primitives::Signature;
	pub use polkadot_primitives::{Transaction, UncheckedTransaction};

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
		if ::runtime_io::ed25519_verify(&tx.signature.0, &msg, &tx.transaction.signed) {
			Ok(CheckedTransaction(tx))
		} else {
			Err(tx)
		}
	}
}

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(mut input: &[u8]) -> Vec<u8> {
	runtime::system::internal::execute_block(Block::from_slice(&mut input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let utx = UncheckedTransaction::from_slice(&mut input).unwrap();
	let header = runtime::system::internal::execute_transaction(utx, header);
	header.to_vec()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn finalise_block(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let header = runtime::system::internal::finalise_block(header);
	header.to_vec()
}

/// Run whatever tests we have.
pub fn run_tests(mut input: &[u8]) -> Vec<u8> {
	use runtime_io::print;

	print("run_tests...");
	let block = Block::from_slice(&mut input).unwrap();
	print("deserialised block.");
	let stxs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].to_vec()
}

impl_stubs!(execute_block, execute_transaction, finalise_block, run_tests);
