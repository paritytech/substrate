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

#[macro_use]
extern crate polkadot_runtime_std as runtime_std;

#[cfg(feature = "std")]
extern crate rustc_hex;
#[cfg(feature = "with-std")]
#[macro_use]
extern crate log;

extern crate substrate_codec as codec;
extern crate polkadot_primitives as primitives;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
pub mod support;
pub mod runtime;

use runtime_std::prelude::*;
use codec::Slicable;
use primitives::relay::{Header, Block, UncheckedTransaction};

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
	use runtime_std::print;

	print("run_tests...");
	let block = Block::from_slice(&mut input).unwrap();
	print("deserialised block.");
	let stxs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].to_vec()
}

impl_stubs!(execute_block, execute_transaction, finalise_block, run_tests);
