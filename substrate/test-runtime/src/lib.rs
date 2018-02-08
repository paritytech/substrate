// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! The Substrate runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_runtime_std as rstd;
#[macro_use]
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

#[cfg(feature = "std")]
pub mod genesismap;
pub mod system;
mod transaction;
mod unchecked_transaction;
mod block;

use rstd::prelude::*;
use codec::Slicable;

use primitives::AuthorityId;
use primitives::hash::H512;
pub use primitives::hash::H256;
pub use primitives::block::{Header, Number as BlockNumber, Digest};
pub use transaction::Transaction;
pub use unchecked_transaction::UncheckedTransaction;
pub use block::Block;

/// An identifier for an account on this system.
pub type AccountId = AuthorityId;
/// Signature for our transactions.
pub type Signature = H512;
/// A simple hash type for all our hashing.
pub type Hash = H256;

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(mut input: &[u8]) -> Vec<u8> {
	system::execute_block(Block::from_slice(&mut input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let utx = UncheckedTransaction::from_slice(&mut input).unwrap();
	let header = system::execute_transaction(utx, header);
	header.to_vec()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn finalise_block(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let header = system::finalise_block(header);
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
